import V185TrunkScan23Chunk0270

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1603257 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 3, 1, 5]
def baseStart_1603257 : Nat := 118140960795 + 1603257 * 2 ^ 59
def prefixEnd_1603257 : Nat := 4983230072969 + 3 ^ 40 * 1603257 * 2
def baseEnd_1603257 : Nat := 823241453685538983314261

theorem tailTrace_1603257 : CollatzResearch.WordTrace tailWord_1603257 prefixEnd_1603257 823241453685538983314261 := by
  unfold tailWord_1603257
  simp only [CollatzResearch.WordTrace]
  refine ⟨58475586752681178341224025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38983724501787452227482683 58475586752681178341224025)
  ·
    refine ⟨43856690064510883755918019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58475586752681178341224025 43856690064510883755918019)
    ·
      refine ⟨65785035096766325633877029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43856690064510883755918019 65785035096766325633877029)
      ·
        refine ⟨12334694080643686056351943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65785035096766325633877029 12334694080643686056351943)
        ·
          refine ⟨18502041120965529084527915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12334694080643686056351943 18502041120965529084527915)
          ·
            refine ⟨27753061681448293626791873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18502041120965529084527915 27753061681448293626791873)
            ·
              refine ⟨20814796261086220220093905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27753061681448293626791873 20814796261086220220093905)
              ·
                refine ⟨15611097195814665165070429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20814796261086220220093905 15611097195814665165070429)
                ·
                  refine ⟨5854161448430499436901411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15611097195814665165070429 5854161448430499436901411)
                  ·
                    refine ⟨8781242172645749155352117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5854161448430499436901411 8781242172645749155352117)
                    ·
                      refine ⟨823241453685538983314261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8781242172645749155352117 823241453685538983314261)
                      ·
                        rfl

theorem cell23_1603257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_1603257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603257 prefixEnd_1603257 := by exact prefixLift 1603257
  have htrace : WordTrace (prefixWord ++ tailWord_1603257) baseStart_1603257 baseEnd_1603257 := by
    simpa [prefixWord, tailWord_1603257, baseEnd_1603257] using wordTrace_append hprefix tailTrace_1603257
  have hstable : (prefixWord ++ tailWord_1603257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603257).length < 2 ^ (prefixWord ++ tailWord_1603257).sum := by decide
  have hdescent : baseEnd_1603257 < baseStart_1603257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603271 : List Nat := [1, 1, 4, 1, 1, 1, 7, 1, 1, 1, 4]
def baseStart_1603271 : Nat := 118140960795 + 1603271 * 2 ^ 59
def prefixEnd_1603271 : Nat := 4983230072969 + 3 ^ 40 * 1603271 * 2
def baseEnd_1603271 : Nat := 823248642414701928539197

theorem tailTrace_1603271 : CollatzResearch.WordTrace tailWord_1603271 prefixEnd_1603271 823248642414701928539197 := by
  unfold tailWord_1603271
  simp only [CollatzResearch.WordTrace]
  refine ⟨58476097374630458732233667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38984064916420305821489111 58476097374630458732233667)
  ·
    refine ⟨87714146061945688098350501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58476097374630458732233667 87714146061945688098350501)
    ·
      refine ⟨16446402386614816518440719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87714146061945688098350501 16446402386614816518440719)
      ·
        refine ⟨24669603579922224777661079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16446402386614816518440719 24669603579922224777661079)
        ·
          refine ⟨37004405369883337166491619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24669603579922224777661079 37004405369883337166491619)
          ·
            refine ⟨55506608054825005749737429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37004405369883337166491619 55506608054825005749737429)
            ·
              refine ⟨1300936126284961072259471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 55506608054825005749737429 1300936126284961072259471)
              ·
                refine ⟨1951404189427441608389207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1300936126284961072259471 1951404189427441608389207)
                ·
                  refine ⟨2927106284141162412583811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1951404189427441608389207 2927106284141162412583811)
                  ·
                    refine ⟨4390659426211743618875717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2927106284141162412583811 4390659426211743618875717)
                    ·
                      refine ⟨823248642414701928539197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4390659426211743618875717 823248642414701928539197)
                      ·
                        rfl

theorem cell23_1603271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_1603271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603271 prefixEnd_1603271 := by exact prefixLift 1603271
  have htrace : WordTrace (prefixWord ++ tailWord_1603271) baseStart_1603271 baseEnd_1603271 := by
    simpa [prefixWord, tailWord_1603271, baseEnd_1603271] using wordTrace_append hprefix tailTrace_1603271
  have hstable : (prefixWord ++ tailWord_1603271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603271).length < 2 ^ (prefixWord ++ tailWord_1603271).sum := by decide
  have hdescent : baseEnd_1603271 < baseStart_1603271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603281 : List Nat := [1, 2, 2, 1, 2, 5, 2, 2, 2, 4]
def baseStart_1603281 : Nat := 118140960795 + 1603281 * 2 ^ 59
def prefixEnd_1603281 : Nat := 4983230072969 + 3 ^ 40 * 1603281 * 2
def baseEnd_1603281 : Nat := 274417925740415629804717

theorem tailTrace_1603281 : CollatzResearch.WordTrace tailWord_1603281 prefixEnd_1603281 274417925740415629804717 := by
  unfold tailWord_1603281
  simp only [CollatzResearch.WordTrace]
  refine ⟨58476462104594230440097697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38984308069729486960065131 58476462104594230440097697)
  ·
    refine ⟨43857346578445672830073273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58476462104594230440097697 43857346578445672830073273)
    ·
      refine ⟨32893009933834254622554955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43857346578445672830073273 32893009933834254622554955)
      ·
        refine ⟨49339514900751381933832433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32893009933834254622554955 49339514900751381933832433)
        ·
          refine ⟨37004636175563536450374325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49339514900751381933832433 37004636175563536450374325)
          ·
            refine ⟨3469184641459081542222593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37004636175563536450374325 3469184641459081542222593)
            ·
              refine ⟨2601888481094311156666945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3469184641459081542222593 2601888481094311156666945)
              ·
                refine ⟨1951416360820733367500209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2601888481094311156666945 1951416360820733367500209)
                ·
                  refine ⟨1463562270615550025625157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1951416360820733367500209 1463562270615550025625157)
                  ·
                    refine ⟨274417925740415629804717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1463562270615550025625157 274417925740415629804717)
                    ·
                      rfl

theorem cell23_1603281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 4].length) (baseStart_1603281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603281 prefixEnd_1603281 := by exact prefixLift 1603281
  have htrace : WordTrace (prefixWord ++ tailWord_1603281) baseStart_1603281 baseEnd_1603281 := by
    simpa [prefixWord, tailWord_1603281, baseEnd_1603281] using wordTrace_append hprefix tailTrace_1603281
  have hstable : (prefixWord ++ tailWord_1603281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603281).length < 2 ^ (prefixWord ++ tailWord_1603281).sum := by decide
  have hdescent : baseEnd_1603281 < baseStart_1603281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603282 : List Nat := [3, 2, 2, 2, 2, 3, 2, 2, 1, 1, 3]
def baseStart_1603282 : Nat := 118140960795 + 1603282 * 2 ^ 59
def prefixEnd_1603282 : Nat := 4983230072969 + 3 ^ 40 * 1603282 * 2
def baseEnd_1603282 : Nat := 823254290701901385501647

theorem tailTrace_1603282 : CollatzResearch.WordTrace tailWord_1603282 prefixEnd_1603282 823254290701901385501647 := by
  unfold tailWord_1603282
  simp only [CollatzResearch.WordTrace]
  refine ⟨14619124644397651902721025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38984332385060405073922733 14619124644397651902721025)
  ·
    refine ⟨10964343483298238927040769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14619124644397651902721025 10964343483298238927040769)
    ·
      refine ⟨8223257612473679195280577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10964343483298238927040769 8223257612473679195280577)
      ·
        refine ⟨6167443209355259396460433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8223257612473679195280577 6167443209355259396460433)
        ·
          refine ⟨4625582407016444547345325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6167443209355259396460433 4625582407016444547345325)
          ·
            refine ⟨1734593402631166705254497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4625582407016444547345325 1734593402631166705254497)
            ·
              refine ⟨1300945051973375028940873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1734593402631166705254497 1300945051973375028940873)
              ·
                refine ⟨975708788980031271705655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1300945051973375028940873 975708788980031271705655)
                ·
                  refine ⟨1463563183470046907558483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 975708788980031271705655 1463563183470046907558483)
                  ·
                    refine ⟨2195344775205070361337725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1463563183470046907558483 2195344775205070361337725)
                    ·
                      refine ⟨823254290701901385501647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2195344775205070361337725 823254290701901385501647)
                      ·
                        rfl

theorem cell23_1603282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_1603282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603282 prefixEnd_1603282 := by exact prefixLift 1603282
  have htrace : WordTrace (prefixWord ++ tailWord_1603282) baseStart_1603282 baseEnd_1603282 := by
    simpa [prefixWord, tailWord_1603282, baseEnd_1603282] using wordTrace_append hprefix tailTrace_1603282
  have hstable : (prefixWord ++ tailWord_1603282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603282).length < 2 ^ (prefixWord ++ tailWord_1603282).sum := by decide
  have hdescent : baseEnd_1603282 < baseStart_1603282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603338 : List Nat := [3, 1, 2, 2, 1, 3, 3, 2, 2, 1, 3]
def baseStart_1603338 : Nat := 118140960795 + 1603338 * 2 ^ 59
def prefixEnd_1603338 : Nat := 4983230072969 + 3 ^ 40 * 1603338 * 2
def baseEnd_1603338 : Nat := 823283045618553166401389

theorem tailTrace_1603338 : CollatzResearch.WordTrace tailWord_1603338 prefixEnd_1603338 823283045618553166401389 := by
  unfold tailWord_1603338
  simp only [CollatzResearch.WordTrace]
  refine ⟨14619635266346932293730667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38985694043591819449948445 14619635266346932293730667)
  ·
    refine ⟨21929452899520398440596001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14619635266346932293730667 21929452899520398440596001)
    ·
      refine ⟨16447089674640298830447001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21929452899520398440596001 16447089674640298830447001)
      ·
        refine ⟨12335317255980224122835251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16447089674640298830447001 12335317255980224122835251)
        ·
          refine ⟨18502975883970336184252877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12335317255980224122835251 18502975883970336184252877)
          ·
            refine ⟨6938615956488876069094829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18502975883970336184252877 6938615956488876069094829)
            ·
              refine ⟨2601980983683328525910561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6938615956488876069094829 2601980983683328525910561)
              ·
                refine ⟨1951485737762496394432921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2601980983683328525910561 1951485737762496394432921)
                ·
                  refine ⟨1463614303321872295824691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1951485737762496394432921 1463614303321872295824691)
                  ·
                    refine ⟨2195421454982808443737037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1463614303321872295824691 2195421454982808443737037)
                    ·
                      refine ⟨823283045618553166401389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2195421454982808443737037 823283045618553166401389)
                      ·
                        rfl

theorem cell23_1603338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_1603338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603338 prefixEnd_1603338 := by exact prefixLift 1603338
  have htrace : WordTrace (prefixWord ++ tailWord_1603338) baseStart_1603338 baseEnd_1603338 := by
    simpa [prefixWord, tailWord_1603338, baseEnd_1603338] using wordTrace_append hprefix tailTrace_1603338
  have hstable : (prefixWord ++ tailWord_1603338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603338).length < 2 ^ (prefixWord ++ tailWord_1603338).sum := by decide
  have hdescent : baseEnd_1603338 < baseStart_1603338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603347 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 5]
def baseStart_1603347 : Nat := 118140960795 + 1603347 * 2 ^ 59
def prefixEnd_1603347 : Nat := 4983230072969 + 3 ^ 40 * 1603347 * 2
def baseEnd_1603347 : Nat := 823287666944443631188847

theorem tailTrace_1603347 : CollatzResearch.WordTrace tailWord_1603347 prefixEnd_1603347 823287666944443631188847 := by
  unfold tailWord_1603347
  simp only [CollatzResearch.WordTrace]
  refine ⟨58478869322355123712000295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38985912881570082474666863 58478869322355123712000295)
  ·
    refine ⟨87718303983532685568000443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58478869322355123712000295 87718303983532685568000443)
    ·
      refine ⟨131577455975299028352000665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87718303983532685568000443 131577455975299028352000665)
      ·
        refine ⟨98683091981474271264000499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131577455975299028352000665 98683091981474271264000499)
        ·
          refine ⟨148024637972211406896000749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98683091981474271264000499 148024637972211406896000749)
          ·
            refine ⟨55509239239579277586000281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148024637972211406896000749 55509239239579277586000281)
            ·
              refine ⟨41631929429684458189500211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55509239239579277586000281 41631929429684458189500211)
              ·
                refine ⟨62447894144526687284250317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41631929429684458189500211 62447894144526687284250317)
                ·
                  refine ⟨23417960304197507731593869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62447894144526687284250317 23417960304197507731593869)
                  ·
                    refine ⟨8781735114074065399347701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23417960304197507731593869 8781735114074065399347701)
                    ·
                      refine ⟨823287666944443631188847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8781735114074065399347701 823287666944443631188847)
                      ·
                        rfl

theorem cell23_1603347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_1603347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603347 prefixEnd_1603347 := by exact prefixLift 1603347
  have htrace : WordTrace (prefixWord ++ tailWord_1603347) baseStart_1603347 baseEnd_1603347 := by
    simpa [prefixWord, tailWord_1603347, baseEnd_1603347] using wordTrace_append hprefix tailTrace_1603347
  have hstable : (prefixWord ++ tailWord_1603347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603347).length < 2 ^ (prefixWord ++ tailWord_1603347).sum := by decide
  have hdescent : baseEnd_1603347 < baseStart_1603347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603354 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 2, 6]
def baseStart_1603354 : Nat := 118140960795 + 1603354 * 2 ^ 59
def prefixEnd_1603354 : Nat := 4983230072969 + 3 ^ 40 * 1603354 * 2
def baseEnd_1603354 : Nat := 274430420436341701267105

theorem tailTrace_1603354 : CollatzResearch.WordTrace tailWord_1603354 prefixEnd_1603354 274430420436341701267105 := by
  unfold tailWord_1603354
  simp only [CollatzResearch.WordTrace]
  refine ⟨14619781158332440976876279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38986083088886509271670077 14619781158332440976876279)
  ·
    refine ⟨21929671737498661465314419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14619781158332440976876279 21929671737498661465314419)
    ·
      refine ⟨32894507606247992197971629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21929671737498661465314419 32894507606247992197971629)
      ·
        refine ⟨12335440352342997074239361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32894507606247992197971629 12335440352342997074239361)
        ·
          refine ⟨9251580264257247805679521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12335440352342997074239361 9251580264257247805679521)
          ·
            refine ⟨6938685198192935854259641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9251580264257247805679521 6938685198192935854259641)
            ·
              refine ⟨5204013898644701890694731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6938685198192935854259641 5204013898644701890694731)
              ·
                refine ⟨7806020847967052836042097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5204013898644701890694731 7806020847967052836042097)
                ·
                  refine ⟨5854515635975289627031573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7806020847967052836042097 5854515635975289627031573)
                  ·
                    refine ⟨274430420436341701267105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5854515635975289627031573 274430420436341701267105)
                    ·
                      rfl

theorem cell23_1603354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_1603354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603354 prefixEnd_1603354 := by exact prefixLift 1603354
  have htrace : WordTrace (prefixWord ++ tailWord_1603354) baseStart_1603354 baseEnd_1603354 := by
    simpa [prefixWord, tailWord_1603354, baseEnd_1603354] using wordTrace_append hprefix tailTrace_1603354
  have hstable : (prefixWord ++ tailWord_1603354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603354).length < 2 ^ (prefixWord ++ tailWord_1603354).sum := by decide
  have hdescent : baseEnd_1603354 < baseStart_1603354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603378 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2]
def baseStart_1603378 : Nat := 118140960795 + 1603378 * 2 ^ 59
def prefixEnd_1603378 : Nat := 4983230072969 + 3 ^ 40 * 1603378 * 2
def baseEnd_1603378 : Nat := 823303584844733009901205

theorem tailTrace_1603378 : CollatzResearch.WordTrace tailWord_1603378 prefixEnd_1603378 823303584844733009901205 := by
  unfold tailWord_1603378
  simp only [CollatzResearch.WordTrace]
  refine ⟨14619999996310704001594697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38986666656828544004252525 14619999996310704001594697)
  ·
    refine ⟨10964999997233028001196023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14619999996310704001594697 10964999997233028001196023)
    ·
      refine ⟨16447499995849542001794035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10964999997233028001196023 16447499995849542001794035)
      ·
        refine ⟨24671249993774313002691053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16447499995849542001794035 24671249993774313002691053)
        ·
          refine ⟨9251718747665367376009145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24671249993774313002691053 9251718747665367376009145)
          ·
            refine ⟨6938789060749025532006859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9251718747665367376009145 6938789060749025532006859)
            ·
              refine ⟨10408183591123538298010289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6938789060749025532006859 10408183591123538298010289)
              ·
                refine ⟨7806137693342653723507717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10408183591123538298010289 7806137693342653723507717)
                ·
                  refine ⟨1463650817501747573157697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7806137693342653723507717 1463650817501747573157697)
                  ·
                    refine ⟨1097738113126310679868273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1463650817501747573157697 1097738113126310679868273)
                    ·
                      refine ⟨823303584844733009901205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1097738113126310679868273 823303584844733009901205)
                      ·
                        rfl

theorem cell23_1603378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_1603378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603378 prefixEnd_1603378 := by exact prefixLift 1603378
  have htrace : WordTrace (prefixWord ++ tailWord_1603378) baseStart_1603378 baseEnd_1603378 := by
    simpa [prefixWord, tailWord_1603378, baseEnd_1603378] using wordTrace_append hprefix tailTrace_1603378
  have hstable : (prefixWord ++ tailWord_1603378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603378).length < 2 ^ (prefixWord ++ tailWord_1603378).sum := by decide
  have hdescent : baseEnd_1603378 < baseStart_1603378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603381 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 2, 1, 5]
def baseStart_1603381 : Nat := 118140960795 + 1603381 * 2 ^ 59
def prefixEnd_1603381 : Nat := 4983230072969 + 3 ^ 40 * 1603381 * 2
def baseEnd_1603381 : Nat := 823305125286696498163691

theorem tailTrace_1603381 : CollatzResearch.WordTrace tailWord_1603381 prefixEnd_1603381 823305125286696498163691 := by
  unfold tailWord_1603381
  simp only [CollatzResearch.WordTrace]
  refine ⟨58480109404231947518737997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38986739602821298345825331 58480109404231947518737997)
  ·
    refine ⟨21930041026586980319526749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58480109404231947518737997 21930041026586980319526749)
    ·
      refine ⟨8223765384970117619822531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21930041026586980319526749 8223765384970117619822531)
      ·
        refine ⟨12335648077455176429733797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8223765384970117619822531 12335648077455176429733797)
        ·
          refine ⟨2312934014522845580575087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12335648077455176429733797 2312934014522845580575087)
          ·
            refine ⟨3469401021784268370862631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2312934014522845580575087 3469401021784268370862631)
            ·
              refine ⟨5204101532676402556293947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3469401021784268370862631 5204101532676402556293947)
              ·
                refine ⟨7806152299014603834440921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5204101532676402556293947 7806152299014603834440921)
                ·
                  refine ⟨5854614224260952875830691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7806152299014603834440921 5854614224260952875830691)
                  ·
                    refine ⟨8781921336391429313746037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5854614224260952875830691 8781921336391429313746037)
                    ·
                      refine ⟨823305125286696498163691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8781921336391429313746037 823305125286696498163691)
                      ·
                        rfl

theorem cell23_1603381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_1603381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603381 prefixEnd_1603381 := by exact prefixLift 1603381
  have htrace : WordTrace (prefixWord ++ tailWord_1603381) baseStart_1603381 baseEnd_1603381 := by
    simpa [prefixWord, tailWord_1603381, baseEnd_1603381] using wordTrace_append hprefix tailTrace_1603381
  have hstable : (prefixWord ++ tailWord_1603381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603381).length < 2 ^ (prefixWord ++ tailWord_1603381).sum := by decide
  have hdescent : baseEnd_1603381 < baseStart_1603381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603412 : List Nat := [2, 4, 1, 1, 3, 1, 4, 1, 2, 2, 2]
def baseStart_1603412 : Nat := 118140960795 + 1603412 * 2 ^ 59
def prefixEnd_1603412 : Nat := 4983230072969 + 3 ^ 40 * 1603412 * 2
def baseEnd_1603412 : Nat := 823321043186985876876049

theorem tailTrace_1603412 : CollatzResearch.WordTrace tailWord_1603412 prefixEnd_1603412 823321043186985876876049 := by
  unfold tailWord_1603412
  simp only [CollatzResearch.WordTrace]
  refine ⟨29240620033559819906558245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38987493378079759875410993 29240620033559819906558245)
  ·
    refine ⟨5482616256292466232479671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29240620033559819906558245 5482616256292466232479671)
    ·
      refine ⟨8223924384438699348719507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5482616256292466232479671 8223924384438699348719507)
      ·
        refine ⟨12335886576658049023079261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8223924384438699348719507 12335886576658049023079261)
        ·
          refine ⟨4625957466246768383654723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12335886576658049023079261 4625957466246768383654723)
          ·
            refine ⟨6938936199370152575482085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4625957466246768383654723 6938936199370152575482085)
            ·
              refine ⟨1301050537381903607902891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6938936199370152575482085 1301050537381903607902891)
              ·
                refine ⟨1951575806072855411854337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1301050537381903607902891 1951575806072855411854337)
                ·
                  refine ⟨1463681854554641558890753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1951575806072855411854337 1463681854554641558890753)
                  ·
                    refine ⟨1097761390915981169168065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1463681854554641558890753 1097761390915981169168065)
                    ·
                      refine ⟨823321043186985876876049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1097761390915981169168065 823321043186985876876049)
                      ·
                        rfl

theorem cell23_1603412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_1603412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603412 prefixEnd_1603412 := by exact prefixLift 1603412
  have htrace : WordTrace (prefixWord ++ tailWord_1603412) baseStart_1603412 baseEnd_1603412 := by
    simpa [prefixWord, tailWord_1603412, baseEnd_1603412] using wordTrace_append hprefix tailTrace_1603412
  have hstable : (prefixWord ++ tailWord_1603412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603412).length < 2 ^ (prefixWord ++ tailWord_1603412).sum := by decide
  have hdescent : baseEnd_1603412 < baseStart_1603412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603431 : List Nat := [1, 1, 5, 1, 2, 1, 4, 1, 2, 5]
def baseStart_1603431 : Nat := 118140960795 + 1603431 * 2 ^ 59
def prefixEnd_1603431 : Nat := 4983230072969 + 3 ^ 40 * 1603431 * 2
def baseEnd_1603431 : Nat := 274443599773140434179487

theorem tailTrace_1603431 : CollatzResearch.WordTrace tailWord_1603431 prefixEnd_1603431 274443599773140434179487 := by
  unfold tailWord_1603431
  simp only [CollatzResearch.WordTrace]
  refine ⟨58481933054050806058058147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38987955369367204038705431 58481933054050806058058147)
  ·
    refine ⟨87722899581076209087087221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58481933054050806058058147 87722899581076209087087221)
    ·
      refine ⟨8224021835725894601914427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87722899581076209087087221 8224021835725894601914427)
      ·
        refine ⟨12336032753588841902871641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8224021835725894601914427 12336032753588841902871641)
        ·
          refine ⟨9252024565191631427153731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12336032753588841902871641 9252024565191631427153731)
          ·
            refine ⟨13878036847787447140730597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9252024565191631427153731 13878036847787447140730597)
            ·
              refine ⟨2602131908960146338886987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13878036847787447140730597 2602131908960146338886987)
              ·
                refine ⟨3903197863440219508330481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2602131908960146338886987 3903197863440219508330481)
                ·
                  refine ⟨2927398397580164631247861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3903197863440219508330481 2927398397580164631247861)
                  ·
                    refine ⟨274443599773140434179487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2927398397580164631247861 274443599773140434179487)
                    ·
                      rfl

theorem cell23_1603431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_1603431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603431 prefixEnd_1603431 := by exact prefixLift 1603431
  have htrace : WordTrace (prefixWord ++ tailWord_1603431) baseStart_1603431 baseEnd_1603431 := by
    simpa [prefixWord, tailWord_1603431, baseEnd_1603431] using wordTrace_append hprefix tailTrace_1603431
  have hstable : (prefixWord ++ tailWord_1603431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603431).length < 2 ^ (prefixWord ++ tailWord_1603431).sum := by decide
  have hdescent : baseEnd_1603431 < baseStart_1603431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603451 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 2, 4, 2]
def baseStart_1603451 : Nat := 118140960795 + 1603451 * 2 ^ 59
def prefixEnd_1603451 : Nat := 4983230072969 + 3 ^ 40 * 1603451 * 2
def baseEnd_1603451 : Nat := 823341068932511224288369

theorem tailTrace_1603451 : CollatzResearch.WordTrace tailWord_1603451 prefixEnd_1603451 823341068932511224288369 := by
  unfold tailWord_1603451
  simp only [CollatzResearch.WordTrace]
  refine ⟨58482662513978349473786207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38988441675985566315857471 58482662513978349473786207)
  ·
    refine ⟨87723993770967524210679311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58482662513978349473786207 87723993770967524210679311)
    ·
      refine ⟨131585990656451286316018967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87723993770967524210679311 131585990656451286316018967)
      ·
        refine ⟨197378985984676929474028451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131585990656451286316018967 197378985984676929474028451)
        ·
          refine ⟨296068478977015394211042677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197378985984676929474028451 296068478977015394211042677)
          ·
            refine ⟨27756419904095193207285251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 296068478977015394211042677 27756419904095193207285251)
            ·
              refine ⟨41634629856142789810927877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27756419904095193207285251 41634629856142789810927877)
              ·
                refine ⟨7806493098026773089548977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41634629856142789810927877 7806493098026773089548977)
                ·
                  refine ⟨5854869823520079817161733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7806493098026773089548977 5854869823520079817161733)
                  ·
                    refine ⟨1097788091910014965717825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5854869823520079817161733 1097788091910014965717825)
                    ·
                      refine ⟨823341068932511224288369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1097788091910014965717825 823341068932511224288369)
                      ·
                        rfl

theorem cell23_1603451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 4, 2].length) (baseStart_1603451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603451 prefixEnd_1603451 := by exact prefixLift 1603451
  have htrace : WordTrace (prefixWord ++ tailWord_1603451) baseStart_1603451 baseEnd_1603451 := by
    simpa [prefixWord, tailWord_1603451, baseEnd_1603451] using wordTrace_append hprefix tailTrace_1603451
  have hstable : (prefixWord ++ tailWord_1603451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603451).length < 2 ^ (prefixWord ++ tailWord_1603451).sum := by decide
  have hdescent : baseEnd_1603451 < baseStart_1603451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603461 : List Nat := [1, 3, 1, 1, 3, 2, 2, 3, 3, 4]
def baseStart_1603461 : Nat := 118140960795 + 1603461 * 2 ^ 59
def prefixEnd_1603461 : Nat := 4983230072969 + 3 ^ 40 * 1603461 * 2
def baseEnd_1603461 : Nat := 274448734579685395054441

theorem tailTrace_1603461 : CollatzResearch.WordTrace tailWord_1603461 prefixEnd_1603461 274448734579685395054441 := by
  unfold tailWord_1603461
  simp only [CollatzResearch.WordTrace]
  refine ⟨58483027243942121181650237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38988684829294747454433491 58483027243942121181650237)
  ·
    refine ⟨21931135216478295443118839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58483027243942121181650237 21931135216478295443118839)
    ·
      refine ⟨32896702824717443164678259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21931135216478295443118839 32896702824717443164678259)
      ·
        refine ⟨49345054237076164747017389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32896702824717443164678259 49345054237076164747017389)
        ·
          refine ⟨18504395338903561780131521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49345054237076164747017389 18504395338903561780131521)
          ·
            refine ⟨13878296504177671335098641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18504395338903561780131521 13878296504177671335098641)
            ·
              refine ⟨10408722378133253501323981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13878296504177671335098641 10408722378133253501323981)
              ·
                refine ⟨3903270891799970062996493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10408722378133253501323981 3903270891799970062996493)
                ·
                  refine ⟨1463726584424988773623685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3903270891799970062996493 1463726584424988773623685)
                  ·
                    refine ⟨274448734579685395054441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1463726584424988773623685 274448734579685395054441)
                    ·
                      rfl

theorem cell23_1603461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 4].length) (baseStart_1603461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603461 prefixEnd_1603461 := by exact prefixLift 1603461
  have htrace : WordTrace (prefixWord ++ tailWord_1603461) baseStart_1603461 baseEnd_1603461 := by
    simpa [prefixWord, tailWord_1603461, baseEnd_1603461] using wordTrace_append hprefix tailTrace_1603461
  have hstable : (prefixWord ++ tailWord_1603461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603461).length < 2 ^ (prefixWord ++ tailWord_1603461).sum := by decide
  have hdescent : baseEnd_1603461 < baseStart_1603461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603495 : List Nat := [1, 1, 6, 1, 2, 1, 1, 5, 1, 4]
def baseStart_1603495 : Nat := 118140960795 + 1603495 * 2 ^ 59
def prefixEnd_1603495 : Nat := 4983230072969 + 3 ^ 40 * 1603495 * 2
def baseEnd_1603495 : Nat := 274454554027103017379389

theorem tailTrace_1603495 : CollatzResearch.WordTrace tailWord_1603495 prefixEnd_1603495 274454554027103017379389 := by
  unfold tailWord_1603495
  simp only [CollatzResearch.WordTrace]
  refine ⟨58484267325818944988387939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38989511550545963325591959 58484267325818944988387939)
  ·
    refine ⟨87726400988728417482581909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58484267325818944988387939 87726400988728417482581909)
    ·
      refine ⟨4112175046346644569496027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87726400988728417482581909 4112175046346644569496027)
      ·
        refine ⟨6168262569519966854244041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4112175046346644569496027 6168262569519966854244041)
        ·
          refine ⟨4626196927139975140683031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6168262569519966854244041 4626196927139975140683031)
          ·
            refine ⟨6939295390709962711024547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4626196927139975140683031 6939295390709962711024547)
            ·
              refine ⟨10408943086064944066536821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6939295390709962711024547 10408943086064944066536821)
              ·
                refine ⟨975838414318588506237827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10408943086064944066536821 975838414318588506237827)
                ·
                  refine ⟨1463757621477882759356741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 975838414318588506237827 1463757621477882759356741)
                  ·
                    refine ⟨274454554027103017379389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1463757621477882759356741 274454554027103017379389)
                    ·
                      rfl

theorem cell23_1603495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_1603495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603495 prefixEnd_1603495 := by exact prefixLift 1603495
  have htrace : WordTrace (prefixWord ++ tailWord_1603495) baseStart_1603495 baseEnd_1603495 := by
    simpa [prefixWord, tailWord_1603495, baseEnd_1603495] using wordTrace_append hprefix tailTrace_1603495
  have hstable : (prefixWord ++ tailWord_1603495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603495).length < 2 ^ (prefixWord ++ tailWord_1603495).sum := by decide
  have hdescent : baseEnd_1603495 < baseStart_1603495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603514 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7]
def baseStart_1603514 : Nat := 118140960795 + 1603514 * 2 ^ 59
def prefixEnd_1603514 : Nat := 4983230072969 + 3 ^ 40 * 1603514 * 2
def baseEnd_1603514 : Nat := 823373418213744477800579

theorem tailTrace_1603514 : CollatzResearch.WordTrace tailWord_1603514 prefixEnd_1603514 823373418213744477800579 := by
  unfold tailWord_1603514
  simp only [CollatzResearch.WordTrace]
  refine ⟨14621240078187527808332399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38989973541833407488886397 14621240078187527808332399)
  ·
    refine ⟨21931860117281291712498599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14621240078187527808332399 21931860117281291712498599)
    ·
      refine ⟨32897790175921937568747899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21931860117281291712498599 32897790175921937568747899)
      ·
        refine ⟨49346685263882906353121849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32897790175921937568747899 49346685263882906353121849)
        ·
          refine ⟨37010013947912179764841387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49346685263882906353121849 37010013947912179764841387)
          ·
            refine ⟨55515020921868269647262081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37010013947912179764841387 55515020921868269647262081)
            ·
              refine ⟨41636265691401202235446561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55515020921868269647262081 41636265691401202235446561)
              ·
                refine ⟨31227199268550901676584921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41636265691401202235446561 31227199268550901676584921)
                ·
                  refine ⟨23420399451413176257438691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31227199268550901676584921 23420399451413176257438691)
                  ·
                    refine ⟨35130599177119764386158037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23420399451413176257438691 35130599177119764386158037)
                    ·
                      refine ⟨823373418213744477800579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35130599177119764386158037 823373418213744477800579)
                      ·
                        rfl

theorem cell23_1603514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_1603514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603514 prefixEnd_1603514 := by exact prefixLift 1603514
  have htrace : WordTrace (prefixWord ++ tailWord_1603514) baseStart_1603514 baseEnd_1603514 := by
    simpa [prefixWord, tailWord_1603514, baseEnd_1603514] using wordTrace_append hprefix tailTrace_1603514
  have hstable : (prefixWord ++ tailWord_1603514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603514).length < 2 ^ (prefixWord ++ tailWord_1603514).sum := by decide
  have hdescent : baseEnd_1603514 < baseStart_1603514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603528 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 1, 5, 2]
def baseStart_1603528 : Nat := 118140960795 + 1603528 * 2 ^ 59
def prefixEnd_1603528 : Nat := 4983230072969 + 3 ^ 40 * 1603528 * 2
def baseEnd_1603528 : Nat := 823380606942907423025515

theorem tailTrace_1603528 : CollatzResearch.WordTrace tailWord_1603528 prefixEnd_1603528 823380606942907423025515 := by
  unfold tailWord_1603528
  simp only [CollatzResearch.WordTrace]
  refine ⟨29242735467349695812169619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38990313956466261082892825 29242735467349695812169619)
  ·
    refine ⟨43864103201024543718254429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29242735467349695812169619 43864103201024543718254429)
    ·
      refine ⟨16449038700384203894345411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43864103201024543718254429 16449038700384203894345411)
      ·
        refine ⟨24673558050576305841518117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16449038700384203894345411 24673558050576305841518117)
        ·
          refine ⟨4626292134483057345284647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24673558050576305841518117 4626292134483057345284647)
          ·
            refine ⟨6939438201724586017926971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4626292134483057345284647 6939438201724586017926971)
            ·
              refine ⟨10409157302586879026890457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6939438201724586017926971 10409157302586879026890457)
              ·
                refine ⟨7806867976940159270167843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10409157302586879026890457 7806867976940159270167843)
                ·
                  refine ⟨11710301965410238905251765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7806867976940159270167843 11710301965410238905251765)
                  ·
                    refine ⟨1097840809257209897367353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11710301965410238905251765 1097840809257209897367353)
                    ·
                      refine ⟨823380606942907423025515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1097840809257209897367353 823380606942907423025515)
                      ·
                        rfl

theorem cell23_1603528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_1603528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603528 prefixEnd_1603528 := by exact prefixLift 1603528
  have htrace : WordTrace (prefixWord ++ tailWord_1603528) baseStart_1603528 baseEnd_1603528 := by
    simpa [prefixWord, tailWord_1603528, baseEnd_1603528] using wordTrace_append hprefix tailTrace_1603528
  have hstable : (prefixWord ++ tailWord_1603528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603528).length < 2 ^ (prefixWord ++ tailWord_1603528).sum := by decide
  have hdescent : baseEnd_1603528 < baseStart_1603528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603569 : List Nat := [1, 2, 2, 2, 5, 1, 3, 2, 1, 1, 3]
def baseStart_1603569 : Nat := 118140960795 + 1603569 * 2 ^ 59
def prefixEnd_1603569 : Nat := 4983230072969 + 3 ^ 40 * 1603569 * 2
def baseEnd_1603569 : Nat := 823401659649741762612827

theorem tailTrace_1603569 : CollatzResearch.WordTrace tailWord_1603569 prefixEnd_1603569 823401659649741762612827 := by
  unfold tailWord_1603569
  simp only [CollatzResearch.WordTrace]
  refine ⟨58486966327550855626581761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38991310885033903751054507 58486966327550855626581761)
  ·
    refine ⟨43865224745663141719936321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58486966327550855626581761 43865224745663141719936321)
    ·
      refine ⟨32898918559247356289952241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43865224745663141719936321 32898918559247356289952241)
      ·
        refine ⟨24674188919435517217464181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32898918559247356289952241 24674188919435517217464181)
        ·
          refine ⟨2313205211197079739137267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24674188919435517217464181 2313205211197079739137267)
          ·
            refine ⟨3469807816795619608705901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2313205211197079739137267 3469807816795619608705901)
            ·
              refine ⟨1301177931298357353264713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3469807816795619608705901 1301177931298357353264713)
              ·
                refine ⟨975883448473768014948535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1301177931298357353264713 975883448473768014948535)
                ·
                  refine ⟨1463825172710652022422803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 975883448473768014948535 1463825172710652022422803)
                  ·
                    refine ⟨2195737759065978033634205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1463825172710652022422803 2195737759065978033634205)
                    ·
                      refine ⟨823401659649741762612827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2195737759065978033634205 823401659649741762612827)
                      ·
                        rfl

theorem cell23_1603569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 1, 1, 3].length) (baseStart_1603569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603569 prefixEnd_1603569 := by exact prefixLift 1603569
  have htrace : WordTrace (prefixWord ++ tailWord_1603569) baseStart_1603569 baseEnd_1603569 := by
    simpa [prefixWord, tailWord_1603569, baseEnd_1603569] using wordTrace_append hprefix tailTrace_1603569
  have hstable : (prefixWord ++ tailWord_1603569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603569).length < 2 ^ (prefixWord ++ tailWord_1603569).sum := by decide
  have hdescent : baseEnd_1603569 < baseStart_1603569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603608 : List Nat := [2, 1, 2, 3, 2, 1, 3, 2, 1, 3, 3]
def baseStart_1603608 : Nat := 118140960795 + 1603608 * 2 ^ 59
def prefixEnd_1603608 : Nat := 4983230072969 + 3 ^ 40 * 1603608 * 2
def baseEnd_1603608 : Nat := 823421685395267110025147

theorem tailTrace_1603608 : CollatzResearch.WordTrace tailWord_1603608 prefixEnd_1603608 823421685395267110025147 := by
  unfold tailWord_1603608
  simp only [CollatzResearch.WordTrace]
  refine ⟨29244194387204782643625739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38992259182939710191500985 29244194387204782643625739)
  ·
    refine ⟨43866291580807173965438609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29244194387204782643625739 43866291580807173965438609)
    ·
      refine ⟨32899718685605380474078957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43866291580807173965438609 32899718685605380474078957)
      ·
        refine ⟨12337394507102017677779609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32899718685605380474078957 12337394507102017677779609)
        ·
          refine ⟨9253045880326513258334707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12337394507102017677779609 9253045880326513258334707)
          ·
            refine ⟨13879568820489769887502061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9253045880326513258334707 13879568820489769887502061)
            ·
              refine ⟨5204838307683663707813273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13879568820489769887502061 5204838307683663707813273)
              ·
                refine ⟨3903628730762747780859955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5204838307683663707813273 3903628730762747780859955)
                ·
                  refine ⟨5855443096144121671289933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3903628730762747780859955 5855443096144121671289933)
                  ·
                    refine ⟨2195791161054045626733725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5855443096144121671289933 2195791161054045626733725)
                    ·
                      refine ⟨823421685395267110025147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2195791161054045626733725 823421685395267110025147)
                      ·
                        rfl

theorem cell23_1603608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_1603608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603608 prefixEnd_1603608 := by exact prefixLift 1603608
  have htrace : WordTrace (prefixWord ++ tailWord_1603608) baseStart_1603608 baseEnd_1603608 := by
    simpa [prefixWord, tailWord_1603608, baseEnd_1603608] using wordTrace_append hprefix tailTrace_1603608
  have hstable : (prefixWord ++ tailWord_1603608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603608).length < 2 ^ (prefixWord ++ tailWord_1603608).sum := by decide
  have hdescent : baseEnd_1603608 < baseStart_1603608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603612 : List Nat := [2, 2, 3, 1, 3, 2, 3, 1, 1, 2, 3]
def baseStart_1603612 : Nat := 118140960795 + 1603612 * 2 ^ 59
def prefixEnd_1603612 : Nat := 4983230072969 + 3 ^ 40 * 1603612 * 2
def baseEnd_1603612 : Nat := 823423739317885094375129

theorem tailTrace_1603612 : CollatzResearch.WordTrace tailWord_1603612 prefixEnd_1603612 823423739317885094375129 := by
  unfold tailWord_1603612
  simp only [CollatzResearch.WordTrace]
  refine ⟨29244267333197536985198545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38992356444263382646931393 29244267333197536985198545)
  ·
    refine ⟨21933200499898152738898909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29244267333197536985198545 21933200499898152738898909)
    ·
      refine ⟨8224950187461807277087091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21933200499898152738898909 8224950187461807277087091)
      ·
        refine ⟨12337425281192710915630637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8224950187461807277087091 12337425281192710915630637)
        ·
          refine ⟨4626534480447266593361489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12337425281192710915630637 4626534480447266593361489)
          ·
            refine ⟨3469900860335449945021117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4626534480447266593361489 3469900860335449945021117)
            ·
              refine ⟨1301212822625793729382919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3469900860335449945021117 1301212822625793729382919)
              ·
                refine ⟨1951819233938690594074379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1301212822625793729382919 1951819233938690594074379)
                ·
                  refine ⟨2927728850908035891111569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1951819233938690594074379 2927728850908035891111569)
                  ·
                    refine ⟨2195796638181026918333677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2927728850908035891111569 2195796638181026918333677)
                    ·
                      refine ⟨823423739317885094375129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2195796638181026918333677 823423739317885094375129)
                      ·
                        rfl

theorem cell23_1603612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_1603612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603612 prefixEnd_1603612 := by exact prefixLift 1603612
  have htrace : WordTrace (prefixWord ++ tailWord_1603612) baseStart_1603612 baseEnd_1603612 := by
    simpa [prefixWord, tailWord_1603612, baseEnd_1603612] using wordTrace_append hprefix tailTrace_1603612
  have hstable : (prefixWord ++ tailWord_1603612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603612).length < 2 ^ (prefixWord ++ tailWord_1603612).sum := by decide
  have hdescent : baseEnd_1603612 < baseStart_1603612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603626 : List Nat := [3, 1, 4, 1, 2, 1, 4, 2, 1, 2, 2]
def baseStart_1603626 : Nat := 118140960795 + 1603626 * 2 ^ 59
def prefixEnd_1603626 : Nat := 4983230072969 + 3 ^ 40 * 1603626 * 2
def baseEnd_1603626 : Nat := 823430928047048039600065

theorem tailTrace_1603626 : CollatzResearch.WordTrace tailWord_1603626 prefixEnd_1603626 823430928047048039600065 := by
  unfold tailWord_1603626
  simp only [CollatzResearch.WordTrace]
  refine ⟨14622261322086088590351683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38992696858896236240937821 14622261322086088590351683)
  ·
    refine ⟨21933391983129132885527525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14622261322086088590351683 21933391983129132885527525)
    ·
      refine ⟨4112510996836712416036411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21933391983129132885527525 4112510996836712416036411)
      ·
        refine ⟨6168766495255068624054617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4112510996836712416036411 6168766495255068624054617)
        ·
          refine ⟨4626574871441301468040963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6168766495255068624054617 4626574871441301468040963)
          ·
            refine ⟨6939862307161952202061445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4626574871441301468040963 6939862307161952202061445)
            ·
              refine ⟨1301224182592866037886521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6939862307161952202061445 1301224182592866037886521)
              ·
                refine ⟨975918136944649528414891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1301224182592866037886521 975918136944649528414891)
                ·
                  refine ⟨1463877205416974292622337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 975918136944649528414891 1463877205416974292622337)
                  ·
                    refine ⟨1097907904062730719466753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1463877205416974292622337 1097907904062730719466753)
                    ·
                      refine ⟨823430928047048039600065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1097907904062730719466753 823430928047048039600065)
                      ·
                        rfl

theorem cell23_1603626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_1603626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603626 prefixEnd_1603626 := by exact prefixLift 1603626
  have htrace : WordTrace (prefixWord ++ tailWord_1603626) baseStart_1603626 baseEnd_1603626 := by
    simpa [prefixWord, tailWord_1603626, baseEnd_1603626] using wordTrace_append hprefix tailTrace_1603626
  have hstable : (prefixWord ++ tailWord_1603626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603626).length < 2 ^ (prefixWord ++ tailWord_1603626).sum := by decide
  have hdescent : baseEnd_1603626 < baseStart_1603626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603651 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 5]
def baseStart_1603651 : Nat := 118140960795 + 1603651 * 2 ^ 59
def prefixEnd_1603651 : Nat := 4983230072969 + 3 ^ 40 * 1603651 * 2
def baseEnd_1603651 : Nat := 823443765063410441787449

theorem tailTrace_1603651 : CollatzResearch.WordTrace tailWord_1603651 prefixEnd_1603651 823443765063410441787449 := by
  unfold tailWord_1603651
  simp only [CollatzResearch.WordTrace]
  refine ⟨58489957113253783631066807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38993304742169189087377871 58489957113253783631066807)
  ·
    refine ⟨87734935669880675446600211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58489957113253783631066807 87734935669880675446600211)
    ·
      refine ⟨131602403504821013169900317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87734935669880675446600211 131602403504821013169900317)
      ·
        refine ⟨49350901314307879938712619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131602403504821013169900317 49350901314307879938712619)
        ·
          refine ⟨74026351971461819908068929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49350901314307879938712619 74026351971461819908068929)
          ·
            refine ⟨55519763978596364931051697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74026351971461819908068929 55519763978596364931051697)
            ·
              refine ⟨41639822983947273698288773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55519763978596364931051697 41639822983947273698288773)
              ·
                refine ⟨7807466809490113818429145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41639822983947273698288773 7807466809490113818429145)
                ·
                  refine ⟨5855600107117585363821859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7807466809490113818429145 5855600107117585363821859)
                  ·
                    refine ⟨8783400160676378045732789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5855600107117585363821859 8783400160676378045732789)
                    ·
                      refine ⟨823443765063410441787449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8783400160676378045732789 823443765063410441787449)
                      ·
                        rfl

theorem cell23_1603651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_1603651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603651 prefixEnd_1603651 := by exact prefixLift 1603651
  have htrace : WordTrace (prefixWord ++ tailWord_1603651) baseStart_1603651 baseEnd_1603651 := by
    simpa [prefixWord, tailWord_1603651, baseEnd_1603651] using wordTrace_append hprefix tailTrace_1603651
  have hstable : (prefixWord ++ tailWord_1603651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603651).length < 2 ^ (prefixWord ++ tailWord_1603651).sum := by decide
  have hdescent : baseEnd_1603651 < baseStart_1603651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603665 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 4, 2, 2]
def baseStart_1603665 : Nat := 118140960795 + 1603665 * 2 ^ 59
def prefixEnd_1603665 : Nat := 4983230072969 + 3 ^ 40 * 1603665 * 2
def baseEnd_1603665 : Nat := 823450953792573387012385

theorem tailTrace_1603665 : CollatzResearch.WordTrace tailWord_1603665 prefixEnd_1603665 823450953792573387012385 := by
  unfold tailWord_1603665
  simp only [CollatzResearch.WordTrace]
  refine ⟨58490467735203064022076449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38993645156802042681384299 58490467735203064022076449)
  ·
    refine ⟨43867850801402298016557337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58490467735203064022076449 43867850801402298016557337)
    ·
      refine ⟨32900888101051723512418003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43867850801402298016557337 32900888101051723512418003)
      ·
        refine ⟨49351332151577585268627005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32900888101051723512418003 49351332151577585268627005)
        ·
          refine ⟨18506749556841594475735127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49351332151577585268627005 18506749556841594475735127)
          ·
            refine ⟨27760124335262391713602691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18506749556841594475735127 27760124335262391713602691)
            ·
              refine ⟨41640186502893587570404037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27760124335262391713602691 41640186502893587570404037)
              ·
                refine ⟨7807534969292547669450757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41640186502893587570404037 7807534969292547669450757)
                ·
                  refine ⟨1463912806742352688022017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7807534969292547669450757 1463912806742352688022017)
                  ·
                    refine ⟨1097934605056764516016513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1463912806742352688022017 1097934605056764516016513)
                    ·
                      refine ⟨823450953792573387012385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1097934605056764516016513 823450953792573387012385)
                      ·
                        rfl

theorem cell23_1603665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 2, 2].length) (baseStart_1603665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603665 prefixEnd_1603665 := by exact prefixLift 1603665
  have htrace : WordTrace (prefixWord ++ tailWord_1603665) baseStart_1603665 baseEnd_1603665 := by
    simpa [prefixWord, tailWord_1603665, baseEnd_1603665] using wordTrace_append hprefix tailTrace_1603665
  have hstable : (prefixWord ++ tailWord_1603665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603665).length < 2 ^ (prefixWord ++ tailWord_1603665).sum := by decide
  have hdescent : baseEnd_1603665 < baseStart_1603665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603669 : List Nat := [1, 3, 2, 2, 1, 5, 2, 1, 1, 3, 2]
def baseStart_1603669 : Nat := 118140960795 + 1603669 * 2 ^ 59
def prefixEnd_1603669 : Nat := 4983230072969 + 3 ^ 40 * 1603669 * 2
def baseEnd_1603669 : Nat := 823453007715191371362367

theorem tailTrace_1603669 : CollatzResearch.WordTrace tailWord_1603669 prefixEnd_1603669 823453007715191371362367 := by
  unfold tailWord_1603669
  simp only [CollatzResearch.WordTrace]
  refine ⟨58490613627188572705222061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38993742418125715136814707 58490613627188572705222061)
  ·
    refine ⟨21933980110195714764458273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58490613627188572705222061 21933980110195714764458273)
    ·
      refine ⟨16450485082646786073343705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21933980110195714764458273 16450485082646786073343705)
      ·
        refine ⟨12337863811985089555007779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16450485082646786073343705 12337863811985089555007779)
        ·
          refine ⟨18506795717977634332511669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12337863811985089555007779 18506795717977634332511669)
          ·
            refine ⟨1735012098560403218672969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18506795717977634332511669 1735012098560403218672969)
            ·
              refine ⟨1301259073920302414004727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1735012098560403218672969 1301259073920302414004727)
              ·
                refine ⟨1951888610880453621007091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1301259073920302414004727 1951888610880453621007091)
                ·
                  refine ⟨2927832916320680431510637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1951888610880453621007091 2927832916320680431510637)
                  ·
                    refine ⟨1097937343620255161816489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2927832916320680431510637 1097937343620255161816489)
                    ·
                      refine ⟨823453007715191371362367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1097937343620255161816489 823453007715191371362367)
                      ·
                        rfl

theorem cell23_1603669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_1603669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603669 prefixEnd_1603669 := by exact prefixLift 1603669
  have htrace : WordTrace (prefixWord ++ tailWord_1603669) baseStart_1603669 baseEnd_1603669 := by
    simpa [prefixWord, tailWord_1603669, baseEnd_1603669] using wordTrace_append hprefix tailTrace_1603669
  have hstable : (prefixWord ++ tailWord_1603669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603669).length < 2 ^ (prefixWord ++ tailWord_1603669).sum := by decide
  have hdescent : baseEnd_1603669 < baseStart_1603669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603722 : List Nat := [3, 1, 2, 3, 1, 4, 1, 3, 5]
def baseStart_1603722 : Nat := 118140960795 + 1603722 * 2 ^ 59
def prefixEnd_1603722 : Nat := 4983230072969 + 3 ^ 40 * 1603722 * 2
def baseEnd_1603722 : Nat := 91497802465542184888847

theorem tailTrace_1603722 : CollatzResearch.WordTrace tailWord_1603722 prefixEnd_1603722 91497802465542184888847 := by
  unfold tailWord_1603722
  simp only [CollatzResearch.WordTrace]
  refine ⟨14623136673999140689225355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38995031130664375171267613 14623136673999140689225355)
  ·
    refine ⟨21934705010998711033838033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14623136673999140689225355 21934705010998711033838033)
    ·
      refine ⟨16451028758249033275378525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21934705010998711033838033 16451028758249033275378525)
      ·
        refine ⟨6169135784343387478266947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16451028758249033275378525 6169135784343387478266947)
        ·
          refine ⟨9253703676515081217400421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6169135784343387478266947 9253703676515081217400421)
          ·
            refine ⟨1735069439346577728262579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9253703676515081217400421 1735069439346577728262579)
            ·
              refine ⟨2602604159019866592393869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1735069439346577728262579 2602604159019866592393869)
              ·
                refine ⟨975976559632449972147701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2602604159019866592393869 975976559632449972147701)
                ·
                  refine ⟨91497802465542184888847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 975976559632449972147701 91497802465542184888847)
                  ·
                    rfl

theorem cell23_1603722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 5].length) (baseStart_1603722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603722 prefixEnd_1603722 := by exact prefixLift 1603722
  have htrace : WordTrace (prefixWord ++ tailWord_1603722) baseStart_1603722 baseEnd_1603722 := by
    simpa [prefixWord, tailWord_1603722, baseEnd_1603722] using wordTrace_append hprefix tailTrace_1603722
  have hstable : (prefixWord ++ tailWord_1603722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603722).length < 2 ^ (prefixWord ++ tailWord_1603722).sum := by decide
  have hdescent : baseEnd_1603722 < baseStart_1603722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603735 : List Nat := [1, 1, 3, 3, 4, 1, 1, 2, 2, 5]
def baseStart_1603735 : Nat := 118140960795 + 1603735 * 2 ^ 59
def prefixEnd_1603735 : Nat := 4983230072969 + 3 ^ 40 * 1603735 * 2
def baseEnd_1603735 : Nat := 274495632479462704379021

theorem tailTrace_1603735 : CollatzResearch.WordTrace tailWord_1603735 prefixEnd_1603735 274495632479462704379021 := by
  unfold tailWord_1603735
  simp only [CollatzResearch.WordTrace]
  refine ⟨58493020844949465977124659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38995347229966310651416439 58493020844949465977124659)
  ·
    refine ⟨87739531267424198965686989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58493020844949465977124659 87739531267424198965686989)
    ·
      refine ⟨32902324225284074612132621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87739531267424198965686989 32902324225284074612132621)
      ·
        refine ⟨12338371584481527979549733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32902324225284074612132621 12338371584481527979549733)
        ·
          refine ⟨2313444672090286496165575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12338371584481527979549733 2313444672090286496165575)
          ·
            refine ⟨3470167008135429744248363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2313444672090286496165575 3470167008135429744248363)
            ·
              refine ⟨5205250512203144616372545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3470167008135429744248363 5205250512203144616372545)
              ·
                refine ⟨3903937884152358462279409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5205250512203144616372545 3903937884152358462279409)
                ·
                  refine ⟨2927953413114268846709557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3903937884152358462279409 2927953413114268846709557)
                  ·
                    refine ⟨274495632479462704379021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2927953413114268846709557 274495632479462704379021)
                    ·
                      rfl

theorem cell23_1603735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 5].length) (baseStart_1603735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603735 prefixEnd_1603735 := by exact prefixLift 1603735
  have htrace : WordTrace (prefixWord ++ tailWord_1603735) baseStart_1603735 baseEnd_1603735 := by
    simpa [prefixWord, tailWord_1603735, baseEnd_1603735] using wordTrace_append hprefix tailTrace_1603735
  have hstable : (prefixWord ++ tailWord_1603735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603735).length < 2 ^ (prefixWord ++ tailWord_1603735).sum := by decide
  have hdescent : baseEnd_1603735 < baseStart_1603735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603772 : List Nat := [2, 2, 2, 3, 3, 1, 2, 1, 2, 1, 4]
def baseStart_1603772 : Nat := 118140960795 + 1603772 * 2 ^ 59
def prefixEnd_1603772 : Nat := 4983230072969 + 3 ^ 40 * 1603772 * 2
def baseEnd_1603772 : Nat := 823505896222604468374393

theorem tailTrace_1603772 : CollatzResearch.WordTrace tailWord_1603772 prefixEnd_1603772 823505896222604468374393 := by
  unfold tailWord_1603772
  simp only [CollatzResearch.WordTrace]
  refine ⟨29247185172907710648110785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38996246897210280864147713 29247185172907710648110785)
  ·
    refine ⟨21935388879680782986083089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29247185172907710648110785 21935388879680782986083089)
    ·
      refine ⟨16451541659760587239562317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21935388879680782986083089 16451541659760587239562317)
      ·
        refine ⟨6169328122410220214835869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16451541659760587239562317 6169328122410220214835869)
        ·
          refine ⟨2313498045903832580563451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6169328122410220214835869 2313498045903832580563451)
          ·
            refine ⟨3470247068855748870845177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2313498045903832580563451 3470247068855748870845177)
            ·
              refine ⟨2602685301641811653133883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3470247068855748870845177 2602685301641811653133883)
              ·
                refine ⟨3904027952462717479700825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2602685301641811653133883 3904027952462717479700825)
                ·
                  refine ⟨2928020964347038109775619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3904027952462717479700825 2928020964347038109775619)
                  ·
                    refine ⟨4392031446520557164663429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2928020964347038109775619 4392031446520557164663429)
                    ·
                      refine ⟨823505896222604468374393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4392031446520557164663429 823505896222604468374393)
                      ·
                        rfl

theorem cell23_1603772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_1603772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603772 prefixEnd_1603772 := by exact prefixLift 1603772
  have htrace : WordTrace (prefixWord ++ tailWord_1603772) baseStart_1603772 baseEnd_1603772 := by
    simpa [prefixWord, tailWord_1603772, baseEnd_1603772] using wordTrace_append hprefix tailTrace_1603772
  have hstable : (prefixWord ++ tailWord_1603772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603772).length < 2 ^ (prefixWord ++ tailWord_1603772).sum := by decide
  have hdescent : baseEnd_1603772 < baseStart_1603772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603808 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 5, 5]
def baseStart_1603808 : Nat := 118140960795 + 1603808 * 2 ^ 59
def prefixEnd_1603808 : Nat := 4983230072969 + 3 ^ 40 * 1603808 * 2
def baseEnd_1603808 : Nat := 274508127175388775841409

theorem tailTrace_1603808 : CollatzResearch.WordTrace tailWord_1603808 prefixEnd_1603808 274508127175388775841409 := by
  unfold tailWord_1603808
  simp only [CollatzResearch.WordTrace]
  refine ⟨29247841686842499722266039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38997122249123332963021385 29247841686842499722266039)
  ·
    refine ⟨43871762530263749583399059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29247841686842499722266039 43871762530263749583399059)
    ·
      refine ⟨65807643795395624375098589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43871762530263749583399059 65807643795395624375098589)
      ·
        refine ⟨24677866423273359140661971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65807643795395624375098589 24677866423273359140661971)
        ·
          refine ⟨37016799634910038710992957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24677866423273359140661971 37016799634910038710992957)
          ·
            refine ⟨13881299863091264516622359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37016799634910038710992957 13881299863091264516622359)
            ·
              refine ⟨20821949794636896774933539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13881299863091264516622359 20821949794636896774933539)
              ·
                refine ⟨31232924691955345162400309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20821949794636896774933539 31232924691955345162400309)
                ·
                  refine ⟨2928086689870813608975029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31232924691955345162400309 2928086689870813608975029)
                  ·
                    refine ⟨274508127175388775841409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2928086689870813608975029 274508127175388775841409)
                    ·
                      rfl

theorem cell23_1603808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 5, 5].length) (baseStart_1603808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603808 prefixEnd_1603808 := by exact prefixLift 1603808
  have htrace : WordTrace (prefixWord ++ tailWord_1603808) baseStart_1603808 baseEnd_1603808 := by
    simpa [prefixWord, tailWord_1603808, baseEnd_1603808] using wordTrace_append hprefix tailTrace_1603808
  have hstable : (prefixWord ++ tailWord_1603808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603808).length < 2 ^ (prefixWord ++ tailWord_1603808).sum := by decide
  have hdescent : baseEnd_1603808 < baseStart_1603808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603818 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_1603818 : Nat := 118140960795 + 1603818 * 2 ^ 59
def prefixEnd_1603818 : Nat := 4983230072969 + 3 ^ 40 * 1603818 * 2
def baseEnd_1603818 : Nat := 823529516332711288399181

theorem tailTrace_1603818 : CollatzResearch.WordTrace tailWord_1603818 prefixEnd_1603818 823529516332711288399181 := by
  unfold tailWord_1603818
  simp only [CollatzResearch.WordTrace]
  refine ⟨14624012025912192788099027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38997365402432514101597405 14624012025912192788099027)
  ·
    refine ⟨21936018038868289182148541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14624012025912192788099027 21936018038868289182148541)
    ·
      refine ⟨8226006764575608443305703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21936018038868289182148541 8226006764575608443305703)
      ·
        refine ⟨12339010146863412664958555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8226006764575608443305703 12339010146863412664958555)
        ·
          refine ⟨18508515220295118997437833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12339010146863412664958555 18508515220295118997437833)
          ·
            refine ⟨13881386415221339248078375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18508515220295118997437833 13881386415221339248078375)
            ·
              refine ⟨20822079622832008872117563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13881386415221339248078375 20822079622832008872117563)
              ·
                refine ⟨31233119434248013308176345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20822079622832008872117563 31233119434248013308176345)
                ·
                  refine ⟨23424839575686009981132259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31233119434248013308176345 23424839575686009981132259)
                  ·
                    refine ⟨35137259363529014971698389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23424839575686009981132259 35137259363529014971698389)
                    ·
                      refine ⟨823529516332711288399181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35137259363529014971698389 823529516332711288399181)
                      ·
                        rfl

theorem cell23_1603818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_1603818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603818 prefixEnd_1603818 := by exact prefixLift 1603818
  have htrace : WordTrace (prefixWord ++ tailWord_1603818) baseStart_1603818 baseEnd_1603818 := by
    simpa [prefixWord, tailWord_1603818, baseEnd_1603818] using wordTrace_append hprefix tailTrace_1603818
  have hstable : (prefixWord ++ tailWord_1603818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603818).length < 2 ^ (prefixWord ++ tailWord_1603818).sum := by decide
  have hdescent : baseEnd_1603818 < baseStart_1603818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603839 : List Nat := [1, 1, 2, 2, 1, 4, 4, 3, 1, 1, 3]
def baseStart_1603839 : Nat := 118140960795 + 1603839 * 2 ^ 59
def prefixEnd_1603839 : Nat := 4983230072969 + 3 ^ 40 * 1603839 * 2
def baseEnd_1603839 : Nat := 823540299426455706236585

theorem tailTrace_1603839 : CollatzResearch.WordTrace tailWord_1603839 prefixEnd_1603839 823540299426455706236585 := by
  unfold tailWord_1603839
  simp only [CollatzResearch.WordTrace]
  refine ⟨58496814036572691738910571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38997876024381794492607047 58496814036572691738910571)
  ·
    refine ⟨87745221054859037608365857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58496814036572691738910571 87745221054859037608365857)
    ·
      refine ⟨65808915791144278206274393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87745221054859037608365857 65808915791144278206274393)
      ·
        refine ⟨49356686843358208654705795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65808915791144278206274393 49356686843358208654705795)
        ·
          refine ⟨74035030265037312982058693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49356686843358208654705795 74035030265037312982058693)
          ·
            refine ⟨13881568174694496184136005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74035030265037312982058693 13881568174694496184136005)
            ·
              refine ⟨2602794032755218034525501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13881568174694496184136005 2602794032755218034525501)
              ·
                refine ⟨976047762283206762947063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2602794032755218034525501 976047762283206762947063)
                ·
                  refine ⟨1464071643424810144420595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 976047762283206762947063 1464071643424810144420595)
                  ·
                    refine ⟨2196107465137215216630893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1464071643424810144420595 2196107465137215216630893)
                    ·
                      refine ⟨823540299426455706236585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2196107465137215216630893 823540299426455706236585)
                      ·
                        rfl

theorem cell23_1603839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 1, 1, 3].length) (baseStart_1603839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603839 prefixEnd_1603839 := by exact prefixLift 1603839
  have htrace : WordTrace (prefixWord ++ tailWord_1603839) baseStart_1603839 baseEnd_1603839 := by
    simpa [prefixWord, tailWord_1603839, baseEnd_1603839] using wordTrace_append hprefix tailTrace_1603839
  have hstable : (prefixWord ++ tailWord_1603839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603839).length < 2 ^ (prefixWord ++ tailWord_1603839).sum := by decide
  have hdescent : baseEnd_1603839 < baseStart_1603839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603868 : List Nat := [2, 2, 3, 1, 1, 1, 1, 12]
def baseStart_1603868 : Nat := 118140960795 + 1603868 * 2 ^ 59
def prefixEnd_1603868 : Nat := 4983230072969 + 3 ^ 40 * 1603868 * 2
def baseEnd_1603868 : Nat := 30502044087608744176813

theorem tailTrace_1603868 : CollatzResearch.WordTrace tailWord_1603868 prefixEnd_1603868 30502044087608744176813 := by
  unfold tailWord_1603868
  simp only [CollatzResearch.WordTrace]
  refine ⟨29248935876733814845858129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38998581168978419794477505 29248935876733814845858129)
  ·
    refine ⟨21936701907550361134393597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29248935876733814845858129 21936701907550361134393597)
    ·
      refine ⟨8226263215331385425397599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21936701907550361134393597 8226263215331385425397599)
      ·
        refine ⟨12339394822997078138096399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8226263215331385425397599 12339394822997078138096399)
        ·
          refine ⟨18509092234495617207144599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12339394822997078138096399 18509092234495617207144599)
          ·
            refine ⟨27763638351743425810716899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18509092234495617207144599 27763638351743425810716899)
            ·
              refine ⟨41645457527615138716075349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27763638351743425810716899 41645457527615138716075349)
              ·
                refine ⟨30502044087608744176813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 41645457527615138716075349 30502044087608744176813)
                ·
                  rfl

theorem cell23_1603868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 12].length) (baseStart_1603868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603868 prefixEnd_1603868 := by exact prefixLift 1603868
  have htrace : WordTrace (prefixWord ++ tailWord_1603868) baseStart_1603868 baseEnd_1603868 := by
    simpa [prefixWord, tailWord_1603868, baseEnd_1603868] using wordTrace_append hprefix tailTrace_1603868
  have hstable : (prefixWord ++ tailWord_1603868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603868).length < 2 ^ (prefixWord ++ tailWord_1603868).sum := by decide
  have hdescent : baseEnd_1603868 < baseStart_1603868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603872 : List Nat := [2, 1, 1, 5, 2, 3, 1, 1, 1, 6]
def baseStart_1603872 : Nat := 118140960795 + 1603872 * 2 ^ 59
def prefixEnd_1603872 : Nat := 4983230072969 + 3 ^ 40 * 1603872 * 2
def baseEnd_1603872 : Nat := 274519081429351359041311

theorem tailTrace_1603872 : CollatzResearch.WordTrace tailWord_1603872 prefixEnd_1603872 274519081429351359041311 := by
  unfold tailWord_1603872
  simp only [CollatzResearch.WordTrace]
  refine ⟨29249008822726569187430935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38998678430302092249907913 29249008822726569187430935)
  ·
    refine ⟨43873513234089853781146403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29249008822726569187430935 43873513234089853781146403)
    ·
      refine ⟨65810269851134780671719605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43873513234089853781146403 65810269851134780671719605)
      ·
        refine ⟨6169712798543885687973713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65810269851134780671719605 6169712798543885687973713)
        ·
          refine ⟨4627284598907914265980285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6169712798543885687973713 4627284598907914265980285)
          ·
            refine ⟨1735231724590467849742607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4627284598907914265980285 1735231724590467849742607)
            ·
              refine ⟨2602847586885701774613911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1735231724590467849742607 2602847586885701774613911)
              ·
                refine ⟨3904271380328552661920867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2602847586885701774613911 3904271380328552661920867)
                ·
                  refine ⟨5856407070492828992881301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3904271380328552661920867 5856407070492828992881301)
                  ·
                    refine ⟨274519081429351359041311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5856407070492828992881301 274519081429351359041311)
                    ·
                      rfl

theorem cell23_1603872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 1, 6].length) (baseStart_1603872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603872 prefixEnd_1603872 := by exact prefixLift 1603872
  have htrace : WordTrace (prefixWord ++ tailWord_1603872) baseStart_1603872 baseEnd_1603872 := by
    simpa [prefixWord, tailWord_1603872, baseEnd_1603872] using wordTrace_append hprefix tailTrace_1603872
  have hstable : (prefixWord ++ tailWord_1603872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603872).length < 2 ^ (prefixWord ++ tailWord_1603872).sum := by decide
  have hdescent : baseEnd_1603872 < baseStart_1603872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603895 : List Nat := [1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 3]
def baseStart_1603895 : Nat := 118140960795 + 1603895 * 2 ^ 59
def prefixEnd_1603895 : Nat := 4983230072969 + 3 ^ 40 * 1603895 * 2
def baseEnd_1603895 : Nat := 823569054343107487136327

theorem tailTrace_1603895 : CollatzResearch.WordTrace tailWord_1603895 prefixEnd_1603895 823569054343107487136327 := by
  unfold tailWord_1603895
  simp only [CollatzResearch.WordTrace]
  refine ⟨58498856524369813302949139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38999237682913208868632759 58498856524369813302949139)
  ·
    refine ⟨87748284786554719954423709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58498856524369813302949139 87748284786554719954423709)
    ·
      refine ⟨32905606794958019982908891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87748284786554719954423709 32905606794958019982908891)
      ·
        refine ⟨49358410192437029974363337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32905606794958019982908891 49358410192437029974363337)
        ·
          refine ⟨37018807644327772480772503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49358410192437029974363337 37018807644327772480772503)
          ·
            refine ⟨55528211466491658721158755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37018807644327772480772503 55528211466491658721158755)
            ·
              refine ⟨83292317199737488081738133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55528211466491658721158755 83292317199737488081738133)
              ·
                refine ⟨3904327368737694753831475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83292317199737488081738133 3904327368737694753831475)
                ·
                  refine ⟨5856491053106542130747213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3904327368737694753831475 5856491053106542130747213)
                  ·
                    refine ⟨2196184144914953299030205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5856491053106542130747213 2196184144914953299030205)
                    ·
                      refine ⟨823569054343107487136327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2196184144914953299030205 823569054343107487136327)
                      ·
                        rfl

theorem cell23_1603895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_1603895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603895 prefixEnd_1603895 := by exact prefixLift 1603895
  have htrace : WordTrace (prefixWord ++ tailWord_1603895) baseStart_1603895 baseEnd_1603895 := by
    simpa [prefixWord, tailWord_1603895, baseEnd_1603895] using wordTrace_append hprefix tailTrace_1603895
  have hstable : (prefixWord ++ tailWord_1603895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603895).length < 2 ^ (prefixWord ++ tailWord_1603895).sum := by decide
  have hdescent : baseEnd_1603895 < baseStart_1603895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603896 : List Nat := [2, 1, 2, 1, 3, 1, 5, 3, 1, 2, 2]
def baseStart_1603896 : Nat := 118140960795 + 1603896 * 2 ^ 59
def prefixEnd_1603896 : Nat := 4983230072969 + 3 ^ 40 * 1603896 * 2
def baseEnd_1603896 : Nat := 823569567823761983223823

theorem tailTrace_1603896 : CollatzResearch.WordTrace tailWord_1603896 prefixEnd_1603896 823569567823761983223823 := by
  unfold tailWord_1603896
  simp only [CollatzResearch.WordTrace]
  refine ⟨29249446498683095236867771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38999261998244126982490361 29249446498683095236867771)
  ·
    refine ⟨43874169748024642855301657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29249446498683095236867771 43874169748024642855301657)
    ·
      refine ⟨32905627311018482141476243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43874169748024642855301657 32905627311018482141476243)
      ·
        refine ⟨49358440966527723212214365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32905627311018482141476243 49358440966527723212214365)
        ·
          refine ⟨18509415362447896204580387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49358440966527723212214365 18509415362447896204580387)
          ·
            refine ⟨27764123043671844306870581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18509415362447896204580387 27764123043671844306870581)
            ·
              refine ⟨2602886535344235403769117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27764123043671844306870581 2602886535344235403769117)
              ·
                refine ⟨976082450754088276413419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2602886535344235403769117 976082450754088276413419)
                ·
                  refine ⟨1464123676131132414620129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 976082450754088276413419 1464123676131132414620129)
                  ·
                    refine ⟨1098092757098349310965097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1464123676131132414620129 1098092757098349310965097)
                    ·
                      refine ⟨823569567823761983223823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1098092757098349310965097 823569567823761983223823)
                      ·
                        rfl

theorem cell23_1603896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 1, 2, 2].length) (baseStart_1603896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603896 prefixEnd_1603896 := by exact prefixLift 1603896
  have htrace : WordTrace (prefixWord ++ tailWord_1603896) baseStart_1603896 baseEnd_1603896 := by
    simpa [prefixWord, tailWord_1603896, baseEnd_1603896] using wordTrace_append hprefix tailTrace_1603896
  have hstable : (prefixWord ++ tailWord_1603896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603896).length < 2 ^ (prefixWord ++ tailWord_1603896).sum := by decide
  have hdescent : baseEnd_1603896 < baseStart_1603896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603912 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 4, 1, 3]
def baseStart_1603912 : Nat := 118140960795 + 1603912 * 2 ^ 59
def prefixEnd_1603912 : Nat := 4983230072969 + 3 ^ 40 * 1603912 * 2
def baseEnd_1603912 : Nat := 823577783514233920623749

theorem tailTrace_1603912 : CollatzResearch.WordTrace tailWord_1603912 prefixEnd_1603912 823577783514233920623749 := by
  unfold tailWord_1603912
  simp only [CollatzResearch.WordTrace]
  refine ⟨29249738282654112603158995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38999651043538816804211993 29249738282654112603158995)
  ·
    refine ⟨43874607423981168904738493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29249738282654112603158995 43874607423981168904738493)
    ·
      refine ⟨16452977783992938339276935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43874607423981168904738493 16452977783992938339276935)
      ·
        refine ⟨24679466675989407508915403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16452977783992938339276935 24679466675989407508915403)
        ·
          refine ⟨37019200013984111263373105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24679466675989407508915403 37019200013984111263373105)
          ·
            refine ⟨27764400010488083447529829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37019200013984111263373105 27764400010488083447529829)
            ·
              refine ⟨5205825001966515646411843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27764400010488083447529829 5205825001966515646411843)
              ·
                refine ⟨7808737502949773469617765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5205825001966515646411843 7808737502949773469617765)
                ·
                  refine ⟨1464138281803082525553331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7808737502949773469617765 1464138281803082525553331)
                  ·
                    refine ⟨2196207422704623788329997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1464138281803082525553331 2196207422704623788329997)
                    ·
                      refine ⟨823577783514233920623749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2196207422704623788329997 823577783514233920623749)
                      ·
                        rfl

theorem cell23_1603912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_1603912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603912 prefixEnd_1603912 := by exact prefixLift 1603912
  have htrace : WordTrace (prefixWord ++ tailWord_1603912) baseStart_1603912 baseEnd_1603912 := by
    simpa [prefixWord, tailWord_1603912, baseEnd_1603912] using wordTrace_append hprefix tailTrace_1603912
  have hstable : (prefixWord ++ tailWord_1603912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603912).length < 2 ^ (prefixWord ++ tailWord_1603912).sum := by decide
  have hdescent : baseEnd_1603912 < baseStart_1603912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603952 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 3, 4, 2]
def baseStart_1603952 : Nat := 118140960795 + 1603952 * 2 ^ 59
def prefixEnd_1603952 : Nat := 4983230072969 + 3 ^ 40 * 1603952 * 2
def baseEnd_1603952 : Nat := 823598322740413764123565

theorem tailTrace_1603952 : CollatzResearch.WordTrace tailWord_1603952 prefixEnd_1603952 823598322740413764123565 := by
  unfold tailWord_1603952
  simp only [CollatzResearch.WordTrace]
  refine ⟨29250467742581656018887055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39000623656775541358516073 29250467742581656018887055)
  ·
    refine ⟨43875701613872484028330583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29250467742581656018887055 43875701613872484028330583)
    ·
      refine ⟨65813552420808726042495875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43875701613872484028330583 65813552420808726042495875)
      ·
        refine ⟨98720328631213089063743813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65813552420808726042495875 98720328631213089063743813)
        ·
          refine ⟨18510061618352454199451965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98720328631213089063743813 18510061618352454199451965)
          ·
            refine ⟨6941273106882170324794487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18510061618352454199451965 6941273106882170324794487)
            ·
              refine ⟨10411909660323255487191731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6941273106882170324794487 10411909660323255487191731)
              ·
                refine ⟨15617864490484883230787597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10411909660323255487191731 15617864490484883230787597)
                ·
                  refine ⟨5856699183931831211545349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15617864490484883230787597 5856699183931831211545349)
                  ·
                    refine ⟨1098131096987218352164753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5856699183931831211545349 1098131096987218352164753)
                    ·
                      refine ⟨823598322740413764123565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1098131096987218352164753 823598322740413764123565)
                      ·
                        rfl

theorem cell23_1603952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 3, 4, 2].length) (baseStart_1603952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603952 prefixEnd_1603952 := by exact prefixLift 1603952
  have htrace : WordTrace (prefixWord ++ tailWord_1603952) baseStart_1603952 baseEnd_1603952 := by
    simpa [prefixWord, tailWord_1603952, baseEnd_1603952] using wordTrace_append hprefix tailTrace_1603952
  have hstable : (prefixWord ++ tailWord_1603952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603952).length < 2 ^ (prefixWord ++ tailWord_1603952).sum := by decide
  have hdescent : baseEnd_1603952 < baseStart_1603952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603975 : List Nat := [1, 1, 4, 2, 2, 1, 2, 3, 7]
def baseStart_1603975 : Nat := 118140960795 + 1603975 * 2 ^ 59
def prefixEnd_1603975 : Nat := 4983230072969 + 3 ^ 40 * 1603975 * 2
def baseEnd_1603975 : Nat := 91512236977274130459551

theorem tailTrace_1603975 : CollatzResearch.WordTrace tailWord_1603975 prefixEnd_1603975 91512236977274130459551 := by
  unfold tailWord_1603975
  simp only [CollatzResearch.WordTrace]
  refine ⟨58501774364079986965861379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39001182909386657977240919 58501774364079986965861379)
  ·
    refine ⟨87752661546119980448792069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58501774364079986965861379 87752661546119980448792069)
    ·
      refine ⟨16453624039897496334148513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87752661546119980448792069 16453624039897496334148513)
      ·
        refine ⟨12340218029923122250611385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16453624039897496334148513 12340218029923122250611385)
        ·
          refine ⟨9255163522442341687958539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12340218029923122250611385 9255163522442341687958539)
          ·
            refine ⟨13882745283663512531937809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9255163522442341687958539 13882745283663512531937809)
            ·
              refine ⟨10412058962747634398953357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13882745283663512531937809 10412058962747634398953357)
              ·
                refine ⟨3904522111030362899607509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10412058962747634398953357 3904522111030362899607509)
                ·
                  refine ⟨91512236977274130459551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3904522111030362899607509 91512236977274130459551)
                  ·
                    rfl

theorem cell23_1603975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 7].length) (baseStart_1603975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603975 prefixEnd_1603975 := by exact prefixLift 1603975
  have htrace : WordTrace (prefixWord ++ tailWord_1603975) baseStart_1603975 baseEnd_1603975 := by
    simpa [prefixWord, tailWord_1603975, baseEnd_1603975] using wordTrace_append hprefix tailTrace_1603975
  have hstable : (prefixWord ++ tailWord_1603975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603975).length < 2 ^ (prefixWord ++ tailWord_1603975).sum := by decide
  have hdescent : baseEnd_1603975 < baseStart_1603975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603982 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1603982 : Nat := 118140960795 + 1603982 * 2 ^ 59
def prefixEnd_1603982 : Nat := 4983230072969 + 3 ^ 40 * 1603982 * 2
def baseEnd_1603982 : Nat := 823613727160048646748427

theorem tailTrace_1603982 : CollatzResearch.WordTrace tailWord_1603982 prefixEnd_1603982 823613727160048646748427 := by
  unfold tailWord_1603982
  simp only [CollatzResearch.WordTrace]
  refine ⟨7312753709381828395170775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39001353116703084774244133 7312753709381828395170775)
  ·
    refine ⟨10969130564072742592756163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7312753709381828395170775 10969130564072742592756163)
    ·
      refine ⟨16453695846109113889134245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10969130564072742592756163 16453695846109113889134245)
      ·
        refine ⟨3085067971145458854212671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16453695846109113889134245 3085067971145458854212671)
        ·
          refine ⟨4627601956718188281319007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3085067971145458854212671 4627601956718188281319007)
          ·
            refine ⟨6941402935077282421978511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4627601956718188281319007 6941402935077282421978511)
            ·
              refine ⟨10412104402615923632967767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6941402935077282421978511 10412104402615923632967767)
              ·
                refine ⟨15618156603923885449451651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10412104402615923632967767 15618156603923885449451651)
                ·
                  refine ⟨23427234905885828174177477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15618156603923885449451651 23427234905885828174177477)
                  ·
                    refine ⟨4392606544853592782658277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23427234905885828174177477 4392606544853592782658277)
                    ·
                      refine ⟨823613727160048646748427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4392606544853592782658277 823613727160048646748427)
                      ·
                        rfl

theorem cell23_1603982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1603982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603982 prefixEnd_1603982 := by exact prefixLift 1603982
  have htrace : WordTrace (prefixWord ++ tailWord_1603982) baseStart_1603982 baseEnd_1603982 := by
    simpa [prefixWord, tailWord_1603982, baseEnd_1603982] using wordTrace_append hprefix tailTrace_1603982
  have hstable : (prefixWord ++ tailWord_1603982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603982).length < 2 ^ (prefixWord ++ tailWord_1603982).sum := by decide
  have hdescent : baseEnd_1603982 < baseStart_1603982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603992 : List Nat := [2, 1, 2, 5, 1, 2, 1, 2, 7]
def baseStart_1603992 : Nat := 118140960795 + 1603992 * 2 ^ 59
def prefixEnd_1603992 : Nat := 4983230072969 + 3 ^ 40 * 1603992 * 2
def baseEnd_1603992 : Nat := 91513206885177067513709

theorem tailTrace_1603992 : CollatzResearch.WordTrace tailWord_1603992 prefixEnd_1603992 91513206885177067513709 := by
  unfold tailWord_1603992
  simp only [CollatzResearch.WordTrace]
  refine ⟨29251197202509199434615115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39001596270012265912820153 29251197202509199434615115)
  ·
    refine ⟨43876795803763799151922673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29251197202509199434615115 43876795803763799151922673)
    ·
      refine ⟨32907596852822849363942005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43876795803763799151922673 32907596852822849363942005)
      ·
        refine ⟨3085087204952142127869563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32907596852822849363942005 3085087204952142127869563)
        ·
          refine ⟨4627630807428213191804345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3085087204952142127869563 4627630807428213191804345)
          ·
            refine ⟨3470723105571159893853259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4627630807428213191804345 3470723105571159893853259)
            ·
              refine ⟨5206084658356739840779889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3470723105571159893853259 5206084658356739840779889)
              ·
                refine ⟨3904563493767554880584917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5206084658356739840779889 3904563493767554880584917)
                ·
                  refine ⟨91513206885177067513709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3904563493767554880584917 91513206885177067513709)
                  ·
                    rfl

theorem cell23_1603992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 7].length) (baseStart_1603992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1603992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1603992 prefixEnd_1603992 := by exact prefixLift 1603992
  have htrace : WordTrace (prefixWord ++ tailWord_1603992) baseStart_1603992 baseEnd_1603992 := by
    simpa [prefixWord, tailWord_1603992, baseEnd_1603992] using wordTrace_append hprefix tailTrace_1603992
  have hstable : (prefixWord ++ tailWord_1603992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603992).length < 2 ^ (prefixWord ++ tailWord_1603992).sum := by decide
  have hdescent : baseEnd_1603992 < baseStart_1603992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604002 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 1, 5, 3]
def baseStart_1604002 : Nat := 118140960795 + 1604002 * 2 ^ 59
def prefixEnd_1604002 : Nat := 4983230072969 + 3 ^ 40 * 1604002 * 2
def baseEnd_1604002 : Nat := 823623996773138568498335

theorem tailTrace_1604002 : CollatzResearch.WordTrace tailWord_1604002 prefixEnd_1604002 823623996773138568498335 := by
  unfold tailWord_1604002
  simp only [CollatzResearch.WordTrace]
  refine ⟨14625689783745542644273565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39001839423321447051396173 14625689783745542644273565)
  ·
    refine ⟨5484633668904578491602587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14625689783745542644273565 5484633668904578491602587)
    ·
      refine ⟨8226950503356867737403881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5484633668904578491602587 8226950503356867737403881)
      ·
        refine ⟨6170212877517650803052911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8226950503356867737403881 6170212877517650803052911)
        ·
          refine ⟨9255319316276476204579367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6170212877517650803052911 9255319316276476204579367)
          ·
            refine ⟨13882978974414714306869051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9255319316276476204579367 13882978974414714306869051)
            ·
              refine ⟨20824468461622071460303577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13882978974414714306869051 20824468461622071460303577)
              ·
                refine ⟨15618351346216553595227683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20824468461622071460303577 15618351346216553595227683)
                ·
                  refine ⟨23427527019324830392841525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15618351346216553595227683 23427527019324830392841525)
                  ·
                    refine ⟨2196330658061702849328893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23427527019324830392841525 2196330658061702849328893)
                    ·
                      refine ⟨823623996773138568498335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2196330658061702849328893 823623996773138568498335)
                      ·
                        rfl

theorem cell23_1604002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_1604002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604002 prefixEnd_1604002 := by exact prefixLift 1604002
  have htrace : WordTrace (prefixWord ++ tailWord_1604002) baseStart_1604002 baseEnd_1604002 := by
    simpa [prefixWord, tailWord_1604002, baseEnd_1604002] using wordTrace_append hprefix tailTrace_1604002
  have hstable : (prefixWord ++ tailWord_1604002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604002).length < 2 ^ (prefixWord ++ tailWord_1604002).sum := by decide
  have hdescent : baseEnd_1604002 < baseStart_1604002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604005 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 1, 7]
def baseStart_1604005 : Nat := 118140960795 + 1604005 * 2 ^ 59
def prefixEnd_1604005 : Nat := 4983230072969 + 3 ^ 40 * 1604005 * 2
def baseEnd_1604005 : Nat := 274541845738367352253607

theorem tailTrace_1604005 : CollatzResearch.WordTrace tailWord_1604005 prefixEnd_1604005 274541845738367352253607 := by
  unfold tailWord_1604005
  simp only [CollatzResearch.WordTrace]
  refine ⟨58502868553971302089453469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39001912369314201392968979 58502868553971302089453469)
  ·
    refine ⟨21938575707739238283545051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58502868553971302089453469 21938575707739238283545051)
    ·
      refine ⟨32907863561608857425317577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21938575707739238283545051 32907863561608857425317577)
      ·
        refine ⟨24680897671206643068988183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32907863561608857425317577 24680897671206643068988183)
        ·
          refine ⟨37021346506809964603482275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24680897671206643068988183 37021346506809964603482275)
          ·
            refine ⟨55532019760214946905223413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37021346506809964603482275 55532019760214946905223413)
            ·
              refine ⟨5206126852520151272364695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55532019760214946905223413 5206126852520151272364695)
              ·
                refine ⟨7809190278780226908547043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5206126852520151272364695 7809190278780226908547043)
                ·
                  refine ⟨11713785418170340362820565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7809190278780226908547043 11713785418170340362820565)
                  ·
                    refine ⟨274541845738367352253607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11713785418170340362820565 274541845738367352253607)
                    ·
                      rfl

theorem cell23_1604005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_1604005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604005 prefixEnd_1604005 := by exact prefixLift 1604005
  have htrace : WordTrace (prefixWord ++ tailWord_1604005) baseStart_1604005 baseEnd_1604005 := by
    simpa [prefixWord, tailWord_1604005, baseEnd_1604005] using wordTrace_append hprefix tailTrace_1604005
  have hstable : (prefixWord ++ tailWord_1604005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604005).length < 2 ^ (prefixWord ++ tailWord_1604005).sum := by decide
  have hdescent : baseEnd_1604005 < baseStart_1604005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604020 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_1604020 : Nat := 118140960795 + 1604020 * 2 ^ 59
def prefixEnd_1604020 : Nat := 4983230072969 + 3 ^ 40 * 1604020 * 2
def baseEnd_1604020 : Nat := 823633239424919498073253

theorem tailTrace_1604020 : CollatzResearch.WordTrace tailWord_1604020 prefixEnd_1604020 823633239424919498073253 := by
  unfold tailWord_1604020
  simp only [CollatzResearch.WordTrace]
  refine ⟨29251707824458479825624757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39002277099277973100833009 29251707824458479825624757)
  ·
    refine ⟨2742347608542982483652321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29251707824458479825624757 2742347608542982483652321)
    ·
      refine ⟨2056760706407236862739241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2742347608542982483652321 2056760706407236862739241)
      ·
        refine ⟨1542570529805427647054431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2056760706407236862739241 1542570529805427647054431)
        ·
          refine ⟨2313855794708141470581647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1542570529805427647054431 2313855794708141470581647)
          ·
            refine ⟨3470783692062212205872471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2313855794708141470581647 3470783692062212205872471)
            ·
              refine ⟨5206175538093318308808707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3470783692062212205872471 5206175538093318308808707)
              ·
                refine ⟨7809263307139977463213061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5206175538093318308808707 7809263307139977463213061)
                ·
                  refine ⟨1464236870088745774352449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7809263307139977463213061 1464236870088745774352449)
                  ·
                    refine ⟨1098177652566559330764337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1464236870088745774352449 1098177652566559330764337)
                    ·
                      refine ⟨823633239424919498073253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1098177652566559330764337 823633239424919498073253)
                      ·
                        rfl

theorem cell23_1604020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_1604020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604020 prefixEnd_1604020 := by exact prefixLift 1604020
  have htrace : WordTrace (prefixWord ++ tailWord_1604020) baseStart_1604020 baseEnd_1604020 := by
    simpa [prefixWord, tailWord_1604020, baseEnd_1604020] using wordTrace_append hprefix tailTrace_1604020
  have hstable : (prefixWord ++ tailWord_1604020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604020).length < 2 ^ (prefixWord ++ tailWord_1604020).sum := by decide
  have hdescent : baseEnd_1604020 < baseStart_1604020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604065 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 10]
def baseStart_1604065 : Nat := 118140960795 + 1604065 * 2 ^ 59
def prefixEnd_1604065 : Nat := 4983230072969 + 3 ^ 40 * 1604065 * 2
def baseEnd_1604065 : Nat := 91517371783819091334505

theorem tailTrace_1604065 : CollatzResearch.WordTrace tailWord_1604065 prefixEnd_1604065 91517371783819091334505 := by
  unfold tailWord_1604065
  simp only [CollatzResearch.WordTrace]
  refine ⟨58505056933753932336637649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39003371289169288224425099 58505056933753932336637649)
  ·
    refine ⟨43878792700315449252478237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58505056933753932336637649 43878792700315449252478237)
    ·
      refine ⟨16454547262618293469679339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43878792700315449252478237 16454547262618293469679339)
      ·
        refine ⟨24681820893927440204519009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16454547262618293469679339 24681820893927440204519009)
        ·
          refine ⟨18511365670445580153389257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24681820893927440204519009 18511365670445580153389257)
          ·
            refine ⟨13883524252834185115041943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18511365670445580153389257 13883524252834185115041943)
            ·
              refine ⟨20825286379251277672562915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13883524252834185115041943 20825286379251277672562915)
              ·
                refine ⟨31237929568876916508844373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20825286379251277672562915 31237929568876916508844373)
                ·
                  refine ⟨91517371783819091334505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 31237929568876916508844373 91517371783819091334505)
                  ·
                    rfl

theorem cell23_1604065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 10].length) (baseStart_1604065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604065 prefixEnd_1604065 := by exact prefixLift 1604065
  have htrace : WordTrace (prefixWord ++ tailWord_1604065) baseStart_1604065 baseEnd_1604065 := by
    simpa [prefixWord, tailWord_1604065, baseEnd_1604065] using wordTrace_append hprefix tailTrace_1604065
  have hstable : (prefixWord ++ tailWord_1604065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604065).length < 2 ^ (prefixWord ++ tailWord_1604065).sum := by decide
  have hdescent : baseEnd_1604065 < baseStart_1604065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604105 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 7]
def baseStart_1604105 : Nat := 118140960795 + 1604105 * 2 ^ 59
def prefixEnd_1604105 : Nat := 4983230072969 + 3 ^ 40 * 1604105 * 2
def baseEnd_1604105 : Nat := 823676885280551665510361

theorem tailTrace_1604105 : CollatzResearch.WordTrace tailWord_1604105 prefixEnd_1604105 823676885280551665510361 := by
  unfold tailWord_1604105
  simp only [CollatzResearch.WordTrace]
  refine ⟨58506515853609019168093769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39004343902406012778729179 58506515853609019168093769)
  ·
    refine ⟨43879886890206764376070327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58506515853609019168093769 43879886890206764376070327)
    ·
      refine ⟨65819830335310146564105491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43879886890206764376070327 65819830335310146564105491)
      ·
        refine ⟨98729745502965219846158237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65819830335310146564105491 98729745502965219846158237)
        ·
          refine ⟨37023654563611957442309339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98729745502965219846158237 37023654563611957442309339)
          ·
            refine ⟨55535481845417936163464009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37023654563611957442309339 55535481845417936163464009)
            ·
              refine ⟨41651611384063452122598007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55535481845417936163464009 41651611384063452122598007)
              ·
                refine ⟨62477417076095178183897011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41651611384063452122598007 62477417076095178183897011)
                ·
                  refine ⟨93716125614142767275845517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62477417076095178183897011 93716125614142767275845517)
                  ·
                    refine ⟨35143547105303537728442069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93716125614142767275845517 35143547105303537728442069)
                    ·
                      refine ⟨823676885280551665510361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35143547105303537728442069 823676885280551665510361)
                      ·
                        rfl

theorem cell23_1604105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_1604105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604105 prefixEnd_1604105 := by exact prefixLift 1604105
  have htrace : WordTrace (prefixWord ++ tailWord_1604105) baseStart_1604105 baseEnd_1604105 := by
    simpa [prefixWord, tailWord_1604105, baseEnd_1604105] using wordTrace_append hprefix tailTrace_1604105
  have hstable : (prefixWord ++ tailWord_1604105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604105).length < 2 ^ (prefixWord ++ tailWord_1604105).sum := by decide
  have hdescent : baseEnd_1604105 < baseStart_1604105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604152 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 3, 1, 5]
def baseStart_1604152 : Nat := 118140960795 + 1604152 * 2 ^ 59
def prefixEnd_1604152 : Nat := 4983230072969 + 3 ^ 40 * 1604152 * 2
def baseEnd_1604152 : Nat := 823701018871312981622645

theorem tailTrace_1604152 : CollatzResearch.WordTrace tailWord_1604152 prefixEnd_1604152 823701018871312981622645 := by
  unfold tailWord_1604152
  simp only [CollatzResearch.WordTrace]
  refine ⟨29254115042219373097527355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39005486722959164130036473 29254115042219373097527355)
  ·
    refine ⟨43881172563329059646291033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29254115042219373097527355 43881172563329059646291033)
    ·
      refine ⟨32910879422496794734718275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43881172563329059646291033 32910879422496794734718275)
      ·
        refine ⟨49366319133745192102077413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32910879422496794734718275 49366319133745192102077413)
        ·
          refine ⟨9256184837577223519139515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49366319133745192102077413 9256184837577223519139515)
          ·
            refine ⟨13884277256365835278709273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9256184837577223519139515 13884277256365835278709273)
            ·
              refine ⟨10413207942274376459031955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13884277256365835278709273 10413207942274376459031955)
              ·
                refine ⟨15619811913411564688547933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10413207942274376459031955 15619811913411564688547933)
                ·
                  refine ⟨5857429467529336758205475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15619811913411564688547933 5857429467529336758205475)
                  ·
                    refine ⟨8786144201294005137308213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5857429467529336758205475 8786144201294005137308213)
                    ·
                      refine ⟨823701018871312981622645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8786144201294005137308213 823701018871312981622645)
                      ·
                        rfl

theorem cell23_1604152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_1604152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604152 prefixEnd_1604152 := by exact prefixLift 1604152
  have htrace : WordTrace (prefixWord ++ tailWord_1604152) baseStart_1604152 baseEnd_1604152 := by
    simpa [prefixWord, tailWord_1604152, baseEnd_1604152] using wordTrace_append hprefix tailTrace_1604152
  have hstable : (prefixWord ++ tailWord_1604152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604152).length < 2 ^ (prefixWord ++ tailWord_1604152).sum := by decide
  have hdescent : baseEnd_1604152 < baseStart_1604152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604159 : List Nat := [1, 1, 2, 2, 3, 2, 1, 5, 2, 4]
def baseStart_1604159 : Nat := 118140960795 + 1604159 * 2 ^ 59
def prefixEnd_1604159 : Nat := 4983230072969 + 3 ^ 40 * 1604159 * 2
def baseEnd_1604159 : Nat := 274568204411964818078371

theorem tailTrace_1604159 : CollatzResearch.WordTrace tailWord_1604159 prefixEnd_1604159 274568204411964818078371 := by
  unfold tailWord_1604159
  simp only [CollatzResearch.WordTrace]
  refine ⟨58508485395413386390559531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39005656930275590927039687 58508485395413386390559531)
  ·
    refine ⟨87762728093120079585839297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58508485395413386390559531 87762728093120079585839297)
    ·
      refine ⟨65822046069840059689379473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87762728093120079585839297 65822046069840059689379473)
      ·
        refine ⟨49366534552380044767034605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65822046069840059689379473 49366534552380044767034605)
        ·
          refine ⟨18512450457142516787637977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49366534552380044767034605 18512450457142516787637977)
          ·
            refine ⟨13884337842856887590728483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18512450457142516787637977 13884337842856887590728483)
            ·
              refine ⟨20826506764285331386092725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13884337842856887590728483 20826506764285331386092725)
              ·
                refine ⟨1952485009151749817446193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20826506764285331386092725 1952485009151749817446193)
                ·
                  refine ⟨1464363756863812363084645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1952485009151749817446193 1464363756863812363084645)
                  ·
                    refine ⟨274568204411964818078371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1464363756863812363084645 274568204411964818078371)
                    ·
                      rfl

theorem cell23_1604159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 4].length) (baseStart_1604159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604159 prefixEnd_1604159 := by exact prefixLift 1604159
  have htrace : WordTrace (prefixWord ++ tailWord_1604159) baseStart_1604159 baseEnd_1604159 := by
    simpa [prefixWord, tailWord_1604159, baseEnd_1604159] using wordTrace_append hprefix tailTrace_1604159
  have hstable : (prefixWord ++ tailWord_1604159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604159).length < 2 ^ (prefixWord ++ tailWord_1604159).sum := by decide
  have hdescent : baseEnd_1604159 < baseStart_1604159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604200 : List Nat := [2, 1, 4, 3, 2, 1, 2, 1, 3, 2, 2]
def baseStart_1604200 : Nat := 118140960795 + 1604200 * 2 ^ 59
def prefixEnd_1604200 : Nat := 4983230072969 + 3 ^ 40 * 1604200 * 2
def baseEnd_1604200 : Nat := 823725665942728793822425

theorem tailTrace_1604200 : CollatzResearch.WordTrace tailWord_1604200 prefixEnd_1604200 823725665942728793822425 := by
  unfold tailWord_1604200
  simp only [CollatzResearch.WordTrace]
  refine ⟨29254990394132425196401027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39006653858843233595201369 29254990394132425196401027)
  ·
    refine ⟨43882485591198637794601541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29254990394132425196401027 43882485591198637794601541)
    ·
      refine ⟨8227966048349744586487789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43882485591198637794601541 8227966048349744586487789)
      ·
        refine ⟨3085487268131154219932921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8227966048349744586487789 3085487268131154219932921)
        ·
          refine ⟨2314115451098365664949691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3085487268131154219932921 2314115451098365664949691)
          ·
            refine ⟨3471173176647548497424537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2314115451098365664949691 3471173176647548497424537)
            ·
              refine ⟨2603379882485661373068403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3471173176647548497424537 2603379882485661373068403)
              ·
                refine ⟨3905069823728492059602605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2603379882485661373068403 3905069823728492059602605)
                ·
                  refine ⟨1464401183898184522350977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3905069823728492059602605 1464401183898184522350977)
                  ·
                    refine ⟨1098300887923638391763233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1464401183898184522350977 1098300887923638391763233)
                    ·
                      refine ⟨823725665942728793822425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1098300887923638391763233 823725665942728793822425)
                      ·
                        rfl

theorem cell23_1604200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_1604200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604200 prefixEnd_1604200 := by exact prefixLift 1604200
  have htrace : WordTrace (prefixWord ++ tailWord_1604200) baseStart_1604200 baseEnd_1604200 := by
    simpa [prefixWord, tailWord_1604200, baseEnd_1604200] using wordTrace_append hprefix tailTrace_1604200
  have hstable : (prefixWord ++ tailWord_1604200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604200).length < 2 ^ (prefixWord ++ tailWord_1604200).sum := by decide
  have hdescent : baseEnd_1604200 < baseStart_1604200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604213 : List Nat := [1, 3, 4, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_1604213 : Nat := 118140960795 + 1604213 * 2 ^ 59
def prefixEnd_1604213 : Nat := 4983230072969 + 3 ^ 40 * 1604213 * 2
def baseEnd_1604213 : Nat := 823732341191237242959865

theorem tailTrace_1604213 : CollatzResearch.WordTrace tailWord_1604213 prefixEnd_1604213 823732341191237242959865 := by
  unfold tailWord_1604213
  simp only [CollatzResearch.WordTrace]
  refine ⟨58510454937217753613025293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39006969958145169075350195 58510454937217753613025293)
  ·
    refine ⟨21941420601456657604884485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58510454937217753613025293 21941420601456657604884485)
    ·
      refine ⟨4114016362773123300915841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21941420601456657604884485 4114016362773123300915841)
      ·
        refine ⟨3085512272079842475686881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4114016362773123300915841 3085512272079842475686881)
        ·
          refine ⟨2314134204059881856765161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3085512272079842475686881 2314134204059881856765161)
          ·
            refine ⟨1735600653044911392573871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2314134204059881856765161 1735600653044911392573871)
            ·
              refine ⟨2603400979567367088860807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1735600653044911392573871 2603400979567367088860807)
              ·
                refine ⟨3905101469351050633291211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2603400979567367088860807 3905101469351050633291211)
                ·
                  refine ⟨5857652204026575949936817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3905101469351050633291211 5857652204026575949936817)
                  ·
                    refine ⟨4393239153019931962452613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5857652204026575949936817 4393239153019931962452613)
                    ·
                      refine ⟨823732341191237242959865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4393239153019931962452613 823732341191237242959865)
                      ·
                        rfl

theorem cell23_1604213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_1604213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604213 prefixEnd_1604213 := by exact prefixLift 1604213
  have htrace : WordTrace (prefixWord ++ tailWord_1604213) baseStart_1604213 baseEnd_1604213 := by
    simpa [prefixWord, tailWord_1604213, baseEnd_1604213] using wordTrace_append hprefix tailTrace_1604213
  have hstable : (prefixWord ++ tailWord_1604213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604213).length < 2 ^ (prefixWord ++ tailWord_1604213).sum := by decide
  have hdescent : baseEnd_1604213 < baseStart_1604213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604234 : List Nat := [3, 1, 2, 3, 4, 1, 1, 3, 1, 2, 2]
def baseStart_1604234 : Nat := 118140960795 + 1604234 * 2 ^ 59
def prefixEnd_1604234 : Nat := 4983230072969 + 3 ^ 40 * 1604234 * 2
def baseEnd_1604234 : Nat := 823743124284981660797269

theorem tailTrace_1604234 : CollatzResearch.WordTrace tailWord_1604234 prefixEnd_1604234 823743124284981660797269 := by
  unfold tailWord_1604234
  simp only [CollatzResearch.WordTrace]
  refine ⟨14627805217535418549884939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39007480580094449466359837 14627805217535418549884939)
  ·
    refine ⟨21941707826303127824827409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14627805217535418549884939 21941707826303127824827409)
    ·
      refine ⟨16456280869727345868620557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21941707826303127824827409 16456280869727345868620557)
      ·
        refine ⟨6171105326147754700732709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16456280869727345868620557 6171105326147754700732709)
        ·
          refine ⟨1157082248652704006387383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6171105326147754700732709 1157082248652704006387383)
          ·
            refine ⟨1735623372979056009581075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157082248652704006387383 1735623372979056009581075)
            ·
              refine ⟨2603435059468584014371613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1735623372979056009581075 2603435059468584014371613)
              ·
                refine ⟨976288147300719005389355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2603435059468584014371613 976288147300719005389355)
                ·
                  refine ⟨1464432220951078508084033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 976288147300719005389355 1464432220951078508084033)
                  ·
                    refine ⟨1098324165713308881063025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1464432220951078508084033 1098324165713308881063025)
                    ·
                      refine ⟨823743124284981660797269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1098324165713308881063025 823743124284981660797269)
                      ·
                        rfl

theorem cell23_1604234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_1604234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604234 prefixEnd_1604234 := by exact prefixLift 1604234
  have htrace : WordTrace (prefixWord ++ tailWord_1604234) baseStart_1604234 baseEnd_1604234 := by
    simpa [prefixWord, tailWord_1604234, baseEnd_1604234] using wordTrace_append hprefix tailTrace_1604234
  have hstable : (prefixWord ++ tailWord_1604234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604234).length < 2 ^ (prefixWord ++ tailWord_1604234).sum := by decide
  have hdescent : baseEnd_1604234 < baseStart_1604234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604319 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 5]
def baseStart_1604319 : Nat := 118140960795 + 1604319 * 2 ^ 59
def prefixEnd_1604319 : Nat := 4983230072969 + 3 ^ 40 * 1604319 * 2
def baseEnd_1604319 : Nat := 823786770140613828234377

theorem tailTrace_1604319 : CollatzResearch.WordTrace tailWord_1604319 prefixEnd_1604319 823786770140613828234377 := by
  unfold tailWord_1604319
  simp only [CollatzResearch.WordTrace]
  refine ⟨58514321074833733716384011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39009547383222489144256007 58514321074833733716384011)
  ·
    refine ⟨87771481612250600574576017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58514321074833733716384011 87771481612250600574576017)
    ·
      refine ⟨65828611209187950430932013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87771481612250600574576017 65828611209187950430932013)
      ·
        refine ⟨24685729203445481411599505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65828611209187950430932013 24685729203445481411599505)
        ·
          refine ⟨18514296902584111058699629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24685729203445481411599505 18514296902584111058699629)
          ·
            refine ⟨6942861338469041647012361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18514296902584111058699629 6942861338469041647012361)
            ·
              refine ⟨5207146003851781235259271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6942861338469041647012361 5207146003851781235259271)
              ·
                refine ⟨7810719005777671852888907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5207146003851781235259271 7810719005777671852888907)
                ·
                  refine ⟨11716078508666507779333361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7810719005777671852888907 11716078508666507779333361)
                  ·
                    refine ⟨8787058881499880834500021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11716078508666507779333361 8787058881499880834500021)
                    ·
                      refine ⟨823786770140613828234377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8787058881499880834500021 823786770140613828234377)
                      ·
                        rfl

theorem cell23_1604319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_1604319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604319 prefixEnd_1604319 := by exact prefixLift 1604319
  have htrace : WordTrace (prefixWord ++ tailWord_1604319) baseStart_1604319 baseEnd_1604319 := by
    simpa [prefixWord, tailWord_1604319, baseEnd_1604319] using wordTrace_append hprefix tailTrace_1604319
  have hstable : (prefixWord ++ tailWord_1604319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604319).length < 2 ^ (prefixWord ++ tailWord_1604319).sum := by decide
  have hdescent : baseEnd_1604319 < baseStart_1604319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604329 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 4, 1, 4]
def baseStart_1604329 : Nat := 118140960795 + 1604329 * 2 ^ 59
def prefixEnd_1604329 : Nat := 4983230072969 + 3 ^ 40 * 1604329 * 2
def baseEnd_1604329 : Nat := 823791904947158789109331

theorem tailTrace_1604329 : CollatzResearch.WordTrace tailWord_1604329 prefixEnd_1604329 823791904947158789109331 := by
  unfold tailWord_1604329
  simp only [CollatzResearch.WordTrace]
  refine ⟨58514685804797505424248041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39009790536531670282832027 58514685804797505424248041)
  ·
    refine ⟨43886014353598129068186031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58514685804797505424248041 43886014353598129068186031)
    ·
      refine ⟨65829021530397193602279047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43886014353598129068186031 65829021530397193602279047)
      ·
        refine ⟨98743532295595790403418571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65829021530397193602279047 98743532295595790403418571)
        ·
          refine ⟨148115298443393685605127857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98743532295595790403418571 148115298443393685605127857)
          ·
            refine ⟨111086473832545264203845893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148115298443393685605127857 111086473832545264203845893)
            ·
              refine ⟨20828713843602237038221105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111086473832545264203845893 20828713843602237038221105)
              ·
                refine ⟨15621535382701677778665829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20828713843602237038221105 15621535382701677778665829)
                ·
                  refine ⟨2929037884256564583499843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15621535382701677778665829 2929037884256564583499843)
                  ·
                    refine ⟨4393556826384846875249765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2929037884256564583499843 4393556826384846875249765)
                    ·
                      refine ⟨823791904947158789109331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4393556826384846875249765 823791904947158789109331)
                      ·
                        rfl

theorem cell23_1604329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 1, 4].length) (baseStart_1604329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604329 prefixEnd_1604329 := by exact prefixLift 1604329
  have htrace : WordTrace (prefixWord ++ tailWord_1604329) baseStart_1604329 baseEnd_1604329 := by
    simpa [prefixWord, tailWord_1604329, baseEnd_1604329] using wordTrace_append hprefix tailTrace_1604329
  have hstable : (prefixWord ++ tailWord_1604329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604329).length < 2 ^ (prefixWord ++ tailWord_1604329).sum := by decide
  have hdescent : baseEnd_1604329 < baseStart_1604329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604346 : List Nat := [3, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4]
def baseStart_1604346 : Nat := 118140960795 + 1604346 * 2 ^ 59
def prefixEnd_1604346 : Nat := 4983230072969 + 3 ^ 40 * 1604346 * 2
def baseEnd_1604346 : Nat := 823800634118285222596753

theorem tailTrace_1604346 : CollatzResearch.WordTrace tailWord_1604346 prefixEnd_1604346 823800634118285222596753 := by
  unfold tailWord_1604346
  simp only [CollatzResearch.WordTrace]
  refine ⟨14628826461433979331904223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39010203897157278218411261 14628826461433979331904223)
  ·
    refine ⟨21943239692150968997856335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14628826461433979331904223 21943239692150968997856335)
    ·
      refine ⟨32914859538226453496784503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21943239692150968997856335 32914859538226453496784503)
      ·
        refine ⟨49372289307339680245176755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32914859538226453496784503 49372289307339680245176755)
        ·
          refine ⟨74058433961009520367765133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49372289307339680245176755 74058433961009520367765133)
          ·
            refine ⟨27771912735378570137911925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74058433961009520367765133 27771912735378570137911925)
            ·
              refine ⟨2603616818941740950429243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27771912735378570137911925 2603616818941740950429243)
              ·
                refine ⟨3905425228412611425643865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2603616818941740950429243 3905425228412611425643865)
                ·
                  refine ⟨2929068921309458569232899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3905425228412611425643865 2929068921309458569232899)
                  ·
                    refine ⟨4393603381964187853849349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2929068921309458569232899 4393603381964187853849349)
                    ·
                      refine ⟨823800634118285222596753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4393603381964187853849349 823800634118285222596753)
                      ·
                        rfl

theorem cell23_1604346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 2, 1, 4].length) (baseStart_1604346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604346 prefixEnd_1604346 := by exact prefixLift 1604346
  have htrace : WordTrace (prefixWord ++ tailWord_1604346) baseStart_1604346 baseEnd_1604346 := by
    simpa [prefixWord, tailWord_1604346, baseEnd_1604346] using wordTrace_append hprefix tailTrace_1604346
  have hstable : (prefixWord ++ tailWord_1604346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604346).length < 2 ^ (prefixWord ++ tailWord_1604346).sum := by decide
  have hdescent : baseEnd_1604346 < baseStart_1604346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604356 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 5, 4]
def baseStart_1604356 : Nat := 118140960795 + 1604356 * 2 ^ 59
def prefixEnd_1604356 : Nat := 4983230072969 + 3 ^ 40 * 1604356 * 2
def baseEnd_1604356 : Nat := 274601922974943394490569

theorem tailTrace_1604356 : CollatzResearch.WordTrace tailWord_1604356 prefixEnd_1604356 274601922974943394490569 := by
  unfold tailWord_1604356
  simp only [CollatzResearch.WordTrace]
  refine ⟨29257835287849844517740461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39010447050466459356987281 29257835287849844517740461)
  ·
    refine ⟨10971688232943691694152673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29257835287849844517740461 10971688232943691694152673)
    ·
      refine ⟨8228766174707768770614505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10971688232943691694152673 8228766174707768770614505)
      ·
        refine ⟨6171574631030826577960879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8228766174707768770614505 6171574631030826577960879)
        ·
          refine ⟨9257361946546239866941319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6171574631030826577960879 9257361946546239866941319)
          ·
            refine ⟨13886042919819359800411979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9257361946546239866941319 13886042919819359800411979)
            ·
              refine ⟨20829064379729039700617969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13886042919819359800411979 20829064379729039700617969)
              ·
                refine ⟨15621798284796779775463477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20829064379729039700617969 15621798284796779775463477)
                ·
                  refine ⟨1464543589199698103949701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15621798284796779775463477 1464543589199698103949701)
                  ·
                    refine ⟨274601922974943394490569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1464543589199698103949701 274601922974943394490569)
                    ·
                      rfl

theorem cell23_1604356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_1604356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604356 prefixEnd_1604356 := by exact prefixLift 1604356
  have htrace : WordTrace (prefixWord ++ tailWord_1604356) baseStart_1604356 baseEnd_1604356 := by
    simpa [prefixWord, tailWord_1604356, baseEnd_1604356] using wordTrace_append hprefix tailTrace_1604356
  have hstable : (prefixWord ++ tailWord_1604356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604356).length < 2 ^ (prefixWord ++ tailWord_1604356).sum := by decide
  have hdescent : baseEnd_1604356 < baseStart_1604356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604366 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3]
def baseStart_1604366 : Nat := 118140960795 + 1604366 * 2 ^ 59
def prefixEnd_1604366 : Nat := 4983230072969 + 3 ^ 40 * 1604366 * 2
def baseEnd_1604366 : Nat := 823810903731375144346661

theorem tailTrace_1604366 : CollatzResearch.WordTrace tailWord_1604366 prefixEnd_1604366 823810903731375144346661 := by
  unfold tailWord_1604366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7314504413207932592918119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39010690203775640495563301 7314504413207932592918119)
  ·
    refine ⟨10971756619811898889377179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7314504413207932592918119 10971756619811898889377179)
    ·
      refine ⟨16457634929717848334065769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10971756619811898889377179 16457634929717848334065769)
      ·
        refine ⟨12343226197288386250549327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16457634929717848334065769 12343226197288386250549327)
        ·
          refine ⟨18514839295932579375823991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12343226197288386250549327 18514839295932579375823991)
          ·
            refine ⟨27772258943898869063735987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18514839295932579375823991 27772258943898869063735987)
            ·
              refine ⟨41658388415848303595603981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27772258943898869063735987 41658388415848303595603981)
              ·
                refine ⟨15621895655943113848351493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41658388415848303595603981 15621895655943113848351493)
                ·
                  refine ⟨2929105435489333846565905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15621895655943113848351493 2929105435489333846565905)
                  ·
                    refine ⟨2196829076617000384924429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2929105435489333846565905 2196829076617000384924429)
                    ·
                      refine ⟨823810903731375144346661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2196829076617000384924429 823810903731375144346661)
                      ·
                        rfl

theorem cell23_1604366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_1604366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604366 prefixEnd_1604366 := by exact prefixLift 1604366
  have htrace : WordTrace (prefixWord ++ tailWord_1604366) baseStart_1604366 baseEnd_1604366 := by
    simpa [prefixWord, tailWord_1604366, baseEnd_1604366] using wordTrace_append hprefix tailTrace_1604366
  have hstable : (prefixWord ++ tailWord_1604366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604366).length < 2 ^ (prefixWord ++ tailWord_1604366).sum := by decide
  have hdescent : baseEnd_1604366 < baseStart_1604366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604373 : List Nat := [1, 3, 2, 1, 2, 2, 1, 6, 1, 4]
def baseStart_1604373 : Nat := 118140960795 + 1604373 * 2 ^ 59
def prefixEnd_1604373 : Nat := 4983230072969 + 3 ^ 40 * 1604373 * 2
def baseEnd_1604373 : Nat := 274604832698652205653043

theorem tailTrace_1604373 : CollatzResearch.WordTrace tailWord_1604373 prefixEnd_1604373 274604832698652205653043 := by
  unfold tailWord_1604373
  simp only [CollatzResearch.WordTrace]
  refine ⟨58516290616638100938849773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39010860411092067292566515 58516290616638100938849773)
  ·
    refine ⟨21943608981239287852068665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58516290616638100938849773 21943608981239287852068665)
    ·
      refine ⟨16457706735929465889051499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21943608981239287852068665 16457706735929465889051499)
      ·
        refine ⟨24686560103894198833577249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16457706735929465889051499 24686560103894198833577249)
        ·
          refine ⟨18514920077920649125182937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24686560103894198833577249 18514920077920649125182937)
          ·
            refine ⟨13886190058440486843887203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18514920077920649125182937 13886190058440486843887203)
            ·
              refine ⟨20829285087660730265830805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13886190058440486843887203 20829285087660730265830805)
              ·
                refine ⟨976372738484096731210819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20829285087660730265830805 976372738484096731210819)
                ·
                  refine ⟨1464559107726145096816229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 976372738484096731210819 1464559107726145096816229)
                  ·
                    refine ⟨274604832698652205653043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1464559107726145096816229 274604832698652205653043)
                    ·
                      rfl

theorem cell23_1604373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_1604373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604373 prefixEnd_1604373 := by exact prefixLift 1604373
  have htrace : WordTrace (prefixWord ++ tailWord_1604373) baseStart_1604373 baseEnd_1604373 := by
    simpa [prefixWord, tailWord_1604373, baseEnd_1604373] using wordTrace_append hprefix tailTrace_1604373
  have hstable : (prefixWord ++ tailWord_1604373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604373).length < 2 ^ (prefixWord ++ tailWord_1604373).sum := by decide
  have hdescent : baseEnd_1604373 < baseStart_1604373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604379 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 3]
def baseStart_1604379 : Nat := 118140960795 + 1604379 * 2 ^ 59
def prefixEnd_1604379 : Nat := 4983230072969 + 3 ^ 40 * 1604379 * 2
def baseEnd_1604379 : Nat := 823817578979883593484101

theorem tailTrace_1604379 : CollatzResearch.WordTrace tailWord_1604379 prefixEnd_1604379 823817578979883593484101 := by
  unfold tailWord_1604379
  simp only [CollatzResearch.WordTrace]
  refine ⟨58516509454616363963568191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39011006303077575975712127 58516509454616363963568191)
  ·
    refine ⟨87774764181924545945352287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58516509454616363963568191 87774764181924545945352287)
    ·
      refine ⟨131662146272886818918028431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87774764181924545945352287 131662146272886818918028431)
      ·
        refine ⟨197493219409330228377042647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131662146272886818918028431 197493219409330228377042647)
        ·
          refine ⟨296239829113995342565563971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197493219409330228377042647 296239829113995342565563971)
          ·
            refine ⟨444359743670993013848345957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296239829113995342565563971 444359743670993013848345957)
            ·
              refine ⟨83317451938311190096564867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 444359743670993013848345957 83317451938311190096564867)
              ·
                refine ⟨124976177907466785144847301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83317451938311190096564867 124976177907466785144847301)
                ·
                  refine ⟨23433033357650022214658869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124976177907466785144847301 23433033357650022214658869)
                  ·
                    refine ⟨2196846877279689582624269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23433033357650022214658869 2196846877279689582624269)
                    ·
                      refine ⟨823817578979883593484101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2196846877279689582624269 823817578979883593484101)
                      ·
                        rfl

theorem cell23_1604379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 3].length) (baseStart_1604379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604379 prefixEnd_1604379 := by exact prefixLift 1604379
  have htrace : WordTrace (prefixWord ++ tailWord_1604379) baseStart_1604379 baseEnd_1604379 := by
    simpa [prefixWord, tailWord_1604379, baseEnd_1604379] using wordTrace_append hprefix tailTrace_1604379
  have hstable : (prefixWord ++ tailWord_1604379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604379).length < 2 ^ (prefixWord ++ tailWord_1604379).sum := by decide
  have hdescent : baseEnd_1604379 < baseStart_1604379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604389 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 1, 2, 6]
def baseStart_1604389 : Nat := 118140960795 + 1604389 * 2 ^ 59
def prefixEnd_1604389 : Nat := 4983230072969 + 3 ^ 40 * 1604389 * 2
def baseEnd_1604389 : Nat := 823822713786428554359055

theorem tailTrace_1604389 : CollatzResearch.WordTrace tailWord_1604389 prefixEnd_1604389 823822713786428554359055 := by
  unfold tailWord_1604389
  simp only [CollatzResearch.WordTrace]
  refine ⟨58516874184580135671432221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39011249456386757114288147 58516874184580135671432221)
  ·
    refine ⟨21943827819217550876787083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58516874184580135671432221 21943827819217550876787083)
    ·
      refine ⟨32915741728826326315180625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21943827819217550876787083 32915741728826326315180625)
      ·
        refine ⟨24686806296619744736385469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32915741728826326315180625 24686806296619744736385469)
        ·
          refine ⟨9257552361232404276144551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24686806296619744736385469 9257552361232404276144551)
          ·
            refine ⟨13886328541848606414216827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9257552361232404276144551 13886328541848606414216827)
            ·
              refine ⟨20829492812772909621325241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13886328541848606414216827 20829492812772909621325241)
              ·
                refine ⟨15622119609579682215993931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20829492812772909621325241 15622119609579682215993931)
                ·
                  refine ⟨23433179414369523323990897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15622119609579682215993931 23433179414369523323990897)
                  ·
                    refine ⟨17574884560777142492993173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23433179414369523323990897 17574884560777142492993173)
                    ·
                      refine ⟨823822713786428554359055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17574884560777142492993173 823822713786428554359055)
                      ·
                        rfl

theorem cell23_1604389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_1604389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604389 prefixEnd_1604389 := by exact prefixLift 1604389
  have htrace : WordTrace (prefixWord ++ tailWord_1604389) baseStart_1604389 baseEnd_1604389 := by
    simpa [prefixWord, tailWord_1604389, baseEnd_1604389] using wordTrace_append hprefix tailTrace_1604389
  have hstable : (prefixWord ++ tailWord_1604389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604389).length < 2 ^ (prefixWord ++ tailWord_1604389).sum := by decide
  have hdescent : baseEnd_1604389 < baseStart_1604389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604430 : List Nat := [4, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3]
def baseStart_1604430 : Nat := 118140960795 + 1604430 * 2 ^ 59
def prefixEnd_1604430 : Nat := 4983230072969 + 3 ^ 40 * 1604430 * 2
def baseEnd_1604430 : Nat := 823843766493262893946367

theorem tailTrace_1604430 : CollatzResearch.WordTrace tailWord_1604430 prefixEnd_1604430 823843766493262893946367 := by
  unfold tailWord_1604430
  simp only [CollatzResearch.WordTrace]
  refine ⟨7314796197178949959209343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39012246384954399782449829 7314796197178949959209343)
  ·
    refine ⟨10972194295768424938814015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7314796197178949959209343 10972194295768424938814015)
    ·
      refine ⟨16458291443652637408221023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10972194295768424938814015 16458291443652637408221023)
      ·
        refine ⟨24687437165478956112331535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16458291443652637408221023 24687437165478956112331535)
        ·
          refine ⟨37031155748218434168497303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24687437165478956112331535 37031155748218434168497303)
          ·
            refine ⟨55546733622327651252745955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37031155748218434168497303 55546733622327651252745955)
            ·
              refine ⟨83320100433491476879118933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55546733622327651252745955 83320100433491476879118933)
              ·
                refine ⟨976407426954978244677175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 83320100433491476879118933 976407426954978244677175)
                ·
                  refine ⟨1464611140432467367015763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 976407426954978244677175 1464611140432467367015763)
                  ·
                    refine ⟨2196916710648701050523645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1464611140432467367015763 2196916710648701050523645)
                    ·
                      refine ⟨823843766493262893946367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2196916710648701050523645 823843766493262893946367)
                      ·
                        rfl

theorem cell23_1604430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3].length) (baseStart_1604430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604430 prefixEnd_1604430 := by exact prefixLift 1604430
  have htrace : WordTrace (prefixWord ++ tailWord_1604430) baseStart_1604430 baseEnd_1604430 := by
    simpa [prefixWord, tailWord_1604430, baseEnd_1604430] using wordTrace_append hprefix tailTrace_1604430
  have hstable : (prefixWord ++ tailWord_1604430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604430).length < 2 ^ (prefixWord ++ tailWord_1604430).sum := by decide
  have hdescent : baseEnd_1604430 < baseStart_1604430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604453 : List Nat := [1, 3, 1, 3, 1, 1, 5, 2, 1, 1, 4]
def baseStart_1604453 : Nat := 118140960795 + 1604453 * 2 ^ 59
def prefixEnd_1604453 : Nat := 4983230072969 + 3 ^ 40 * 1604453 * 2
def baseEnd_1604453 : Nat := 823855576548316303958761

theorem tailTrace_1604453 : CollatzResearch.WordTrace tailWord_1604453 prefixEnd_1604453 823855576548316303958761 := by
  unfold tailWord_1604453
  simp only [CollatzResearch.WordTrace]
  refine ⟨58519208456348274601762013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39012805637565516401174675 58519208456348274601762013)
  ·
    refine ⟨21944703171130602975660755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58519208456348274601762013 21944703171130602975660755)
    ·
      refine ⟨32917054756695904463491133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21944703171130602975660755 32917054756695904463491133)
      ·
        refine ⟨12343895533760964173809175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32917054756695904463491133 12343895533760964173809175)
        ·
          refine ⟨18515843300641446260713763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12343895533760964173809175 18515843300641446260713763)
          ·
            refine ⟨27773764950962169391070645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18515843300641446260713763 27773764950962169391070645)
            ·
              refine ⟨2603790464152703380412873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27773764950962169391070645 2603790464152703380412873)
              ·
                refine ⟨1952842848114527535309655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2603790464152703380412873 1952842848114527535309655)
                ·
                  refine ⟨2929264272171791302964483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1952842848114527535309655 2929264272171791302964483)
                  ·
                    refine ⟨4393896408257686954446725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2929264272171791302964483 4393896408257686954446725)
                    ·
                      refine ⟨823855576548316303958761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4393896408257686954446725 823855576548316303958761)
                      ·
                        rfl

theorem cell23_1604453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_1604453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604453 prefixEnd_1604453 := by exact prefixLift 1604453
  have htrace : WordTrace (prefixWord ++ tailWord_1604453) baseStart_1604453 baseEnd_1604453 := by
    simpa [prefixWord, tailWord_1604453, baseEnd_1604453] using wordTrace_append hprefix tailTrace_1604453
  have hstable : (prefixWord ++ tailWord_1604453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604453).length < 2 ^ (prefixWord ++ tailWord_1604453).sum := by decide
  have hdescent : baseEnd_1604453 < baseStart_1604453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604459 : List Nat := [1, 1, 1, 1, 2, 2, 6, 9]
def baseStart_1604459 : Nat := 118140960795 + 1604459 * 2 ^ 59
def prefixEnd_1604459 : Nat := 4983230072969 + 3 ^ 40 * 1604459 * 2
def baseEnd_1604459 : Nat := 30513283608601602980879

theorem tailTrace_1604459 : CollatzResearch.WordTrace tailWord_1604459 prefixEnd_1604459 30513283608601602980879 := by
  unfold tailWord_1604459
  simp only [CollatzResearch.WordTrace]
  refine ⟨58519427294326537626480431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39012951529551025084320287 58519427294326537626480431)
  ·
    refine ⟨87779140941489806439720647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58519427294326537626480431 87779140941489806439720647)
    ·
      refine ⟨131668711412234709659580971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87779140941489806439720647 131668711412234709659580971)
      ·
        refine ⟨197503067118352064489371457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131668711412234709659580971 197503067118352064489371457)
        ·
          refine ⟨148127300338764048367028593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197503067118352064489371457 148127300338764048367028593)
          ·
            refine ⟨111095475254073036275271445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148127300338764048367028593 111095475254073036275271445)
            ·
              refine ⟨5207600402534673575403349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111095475254073036275271445 5207600402534673575403349)
              ·
                refine ⟨30513283608601602980879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5207600402534673575403349 30513283608601602980879)
                ·
                  rfl

theorem cell23_1604459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 9].length) (baseStart_1604459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604459 prefixEnd_1604459 := by exact prefixLift 1604459
  have htrace : WordTrace (prefixWord ++ tailWord_1604459) baseStart_1604459 baseEnd_1604459 := by
    simpa [prefixWord, tailWord_1604459, baseEnd_1604459] using wordTrace_append hprefix tailTrace_1604459
  have hstable : (prefixWord ++ tailWord_1604459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604459).length < 2 ^ (prefixWord ++ tailWord_1604459).sum := by decide
  have hdescent : baseEnd_1604459 < baseStart_1604459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604466 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 3, 2, 4]
def baseStart_1604466 : Nat := 118140960795 + 1604466 * 2 ^ 59
def prefixEnd_1604466 : Nat := 4983230072969 + 3 ^ 40 * 1604466 * 2
def baseEnd_1604466 : Nat := 823862251796824753096201

theorem tailTrace_1604466 : CollatzResearch.WordTrace tailWord_1604466 prefixEnd_1604466 823862251796824753096201 := by
  unfold tailWord_1604466
  simp only [CollatzResearch.WordTrace]
  refine ⟨14629920651325294455496313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39013121736867451881323501 14629920651325294455496313)
  ·
    refine ⟨10972440488493970841622235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14629920651325294455496313 10972440488493970841622235)
    ·
      refine ⟨16458660732740956262433353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10972440488493970841622235 16458660732740956262433353)
      ·
        refine ⟨12343995549555717196825015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16458660732740956262433353 12343995549555717196825015)
        ·
          refine ⟨18515993324333575795237523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12343995549555717196825015 18515993324333575795237523)
          ·
            refine ⟨27773989986500363692856285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18515993324333575795237523 27773989986500363692856285)
            ·
              refine ⟨10415246244937636384821107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27773989986500363692856285 10415246244937636384821107)
              ·
                refine ⟨15622869367406454577231661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10415246244937636384821107 15622869367406454577231661)
                ·
                  refine ⟨5858576012777420466461873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15622869367406454577231661 5858576012777420466461873)
                  ·
                    refine ⟨4393932009583065349846405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5858576012777420466461873 4393932009583065349846405)
                    ·
                      refine ⟨823862251796824753096201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4393932009583065349846405 823862251796824753096201)
                      ·
                        rfl

theorem cell23_1604466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_1604466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604466 prefixEnd_1604466 := by exact prefixLift 1604466
  have htrace : WordTrace (prefixWord ++ tailWord_1604466) baseStart_1604466 baseEnd_1604466 := by
    simpa [prefixWord, tailWord_1604466, baseEnd_1604466] using wordTrace_append hprefix tailTrace_1604466
  have hstable : (prefixWord ++ tailWord_1604466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604466).length < 2 ^ (prefixWord ++ tailWord_1604466).sum := by decide
  have hdescent : baseEnd_1604466 < baseStart_1604466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604473 : List Nat := [1, 2, 1, 3, 2, 5, 1, 1, 1, 1, 5]
def baseStart_1604473 : Nat := 118140960795 + 1604473 * 2 ^ 59
def prefixEnd_1604473 : Nat := 4983230072969 + 3 ^ 40 * 1604473 * 2
def baseEnd_1604473 : Nat := 823865846161406225708669

theorem tailTrace_1604473 : CollatzResearch.WordTrace tailWord_1604473 prefixEnd_1604473 823865846161406225708669 := by
  unfold tailWord_1604473
  simp only [CollatzResearch.WordTrace]
  refine ⟨58519937916275818017490073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39013291944183878678326715 58519937916275818017490073)
  ·
    refine ⟨43889953437206863513117555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58519937916275818017490073 43889953437206863513117555)
    ·
      refine ⟨65834930155810295269676333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43889953437206863513117555 65834930155810295269676333)
      ·
        refine ⟨24688098808428860726128625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65834930155810295269676333 24688098808428860726128625)
        ·
          refine ⟨18516074106321645544596469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24688098808428860726128625 18516074106321645544596469)
          ·
            refine ⟨1735881947467654269805919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18516074106321645544596469 1735881947467654269805919)
            ·
              refine ⟨2603822921201481404708879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1735881947467654269805919 2603822921201481404708879)
              ·
                refine ⟨3905734381802222107063319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2603822921201481404708879 3905734381802222107063319)
                ·
                  refine ⟨5858601572703333160594979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3905734381802222107063319 5858601572703333160594979)
                  ·
                    refine ⟨8787902359054999740892469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5858601572703333160594979 8787902359054999740892469)
                    ·
                      refine ⟨823865846161406225708669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8787902359054999740892469 823865846161406225708669)
                      ·
                        rfl

theorem cell23_1604473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_1604473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604473 prefixEnd_1604473 := by exact prefixLift 1604473
  have htrace : WordTrace (prefixWord ++ tailWord_1604473) baseStart_1604473 baseEnd_1604473 := by
    simpa [prefixWord, tailWord_1604473, baseEnd_1604473] using wordTrace_append hprefix tailTrace_1604473
  have hstable : (prefixWord ++ tailWord_1604473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604473).length < 2 ^ (prefixWord ++ tailWord_1604473).sum := by decide
  have hdescent : baseEnd_1604473 < baseStart_1604473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604503 : List Nat := [1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 3]
def baseStart_1604503 : Nat := 118140960795 + 1604503 * 2 ^ 59
def prefixEnd_1604503 : Nat := 4983230072969 + 3 ^ 40 * 1604503 * 2
def baseEnd_1604503 : Nat := 823881250581041108333531

theorem tailTrace_1604503 : CollatzResearch.WordTrace tailWord_1604503 prefixEnd_1604503 823881250581041108333531 := by
  unfold tailWord_1604503
  simp only [CollatzResearch.WordTrace]
  refine ⟨58521032106167133141082163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39014021404111422094054775 58521032106167133141082163)
  ·
    refine ⟨87781548159250699711623245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58521032106167133141082163 87781548159250699711623245)
    ·
      refine ⟨32918080559719012391858717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87781548159250699711623245 32918080559719012391858717)
      ·
        refine ⟨12344280209894629646947019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32918080559719012391858717 12344280209894629646947019)
        ·
          refine ⟨18516420314841944470420529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12344280209894629646947019 18516420314841944470420529)
          ·
            refine ⟨13887315236131458352815397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18516420314841944470420529 13887315236131458352815397)
            ·
              refine ⟨2603871606774648441152887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13887315236131458352815397 2603871606774648441152887)
              ·
                refine ⟨3905807410161972661729331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2603871606774648441152887 3905807410161972661729331)
                ·
                  refine ⟨5858711115242958992593997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3905807410161972661729331 5858711115242958992593997)
                  ·
                    refine ⟨2197016668216109622222749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5858711115242958992593997 2197016668216109622222749)
                    ·
                      refine ⟨823881250581041108333531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2197016668216109622222749 823881250581041108333531)
                      ·
                        rfl

theorem cell23_1604503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_1604503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604503 prefixEnd_1604503 := by exact prefixLift 1604503
  have htrace : WordTrace (prefixWord ++ tailWord_1604503) baseStart_1604503 baseEnd_1604503 := by
    simpa [prefixWord, tailWord_1604503, baseEnd_1604503] using wordTrace_append hprefix tailTrace_1604503
  have hstable : (prefixWord ++ tailWord_1604503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604503).length < 2 ^ (prefixWord ++ tailWord_1604503).sum := by decide
  have hdescent : baseEnd_1604503 < baseStart_1604503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604516 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_1604516 : Nat := 118140960795 + 1604516 * 2 ^ 59
def prefixEnd_1604516 : Nat := 4983230072969 + 3 ^ 40 * 1604516 * 2
def baseEnd_1604516 : Nat := 823887925829549557470971

theorem tailTrace_1604516 : CollatzResearch.WordTrace tailWord_1604516 prefixEnd_1604516 823887925829549557470971 := by
  unfold tailWord_1604516
  simp only [CollatzResearch.WordTrace]
  refine ⟨29260753127560018180652701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39014337503413357574203601 29260753127560018180652701)
  ·
    refine ⟨10972782422835006817744763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29260753127560018180652701 10972782422835006817744763)
    ·
      refine ⟨16459173634252510226617145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10972782422835006817744763 16459173634252510226617145)
      ·
        refine ⟨12344380225689382669962859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16459173634252510226617145 12344380225689382669962859)
        ·
          refine ⟨18516570338534074004944289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12344380225689382669962859 18516570338534074004944289)
          ·
            refine ⟨13887427753900555503708217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18516570338534074004944289 13887427753900555503708217)
            ·
              refine ⟨10415570815425416627781163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13887427753900555503708217 10415570815425416627781163)
              ·
                refine ⟨15623356223138124941671745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10415570815425416627781163 15623356223138124941671745)
                ·
                  refine ⟨11717517167353593706253809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15623356223138124941671745 11717517167353593706253809)
                  ·
                    refine ⟨8788137875515195279690357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11717517167353593706253809 8788137875515195279690357)
                    ·
                      refine ⟨823887925829549557470971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8788137875515195279690357 823887925829549557470971)
                      ·
                        rfl

theorem cell23_1604516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_1604516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604516 prefixEnd_1604516 := by exact prefixLift 1604516
  have htrace : WordTrace (prefixWord ++ tailWord_1604516) baseStart_1604516 baseEnd_1604516 := by
    simpa [prefixWord, tailWord_1604516, baseEnd_1604516] using wordTrace_append hprefix tailTrace_1604516
  have hstable : (prefixWord ++ tailWord_1604516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604516).length < 2 ^ (prefixWord ++ tailWord_1604516).sum := by decide
  have hdescent : baseEnd_1604516 < baseStart_1604516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604536 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 2, 6]
def baseStart_1604536 : Nat := 118140960795 + 1604536 * 2 ^ 59
def prefixEnd_1604536 : Nat := 4983230072969 + 3 ^ 40 * 1604536 * 2
def baseEnd_1604536 : Nat := 274632731814213159740293

theorem tailTrace_1604536 : CollatzResearch.WordTrace tailWord_1604536 prefixEnd_1604536 274632731814213159740293 := by
  unfold tailWord_1604536
  simp only [CollatzResearch.WordTrace]
  refine ⟨29261117857523789888516731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39014823810031719851355641 29261117857523789888516731)
  ·
    refine ⟨43891676786285684832775097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29261117857523789888516731 43891676786285684832775097)
    ·
      refine ⟨32918757589714263624581323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43891676786285684832775097 32918757589714263624581323)
      ·
        refine ⟨49378136384571395436871985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32918757589714263624581323 49378136384571395436871985)
        ·
          refine ⟨37033602288428546577653989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49378136384571395436871985 37033602288428546577653989)
          ·
            refine ⟨6943800429080352483310123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37033602288428546577653989 6943800429080352483310123)
            ·
              refine ⟨10415700643620528724965185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6943800429080352483310123 10415700643620528724965185)
              ·
                refine ⟨7811775482715396543723889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10415700643620528724965185 7811775482715396543723889)
                ·
                  refine ⟨5858831612036547407792917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7811775482715396543723889 5858831612036547407792917)
                  ·
                    refine ⟨274632731814213159740293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5858831612036547407792917 274632731814213159740293)
                    ·
                      rfl

theorem cell23_1604536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_1604536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604536 prefixEnd_1604536 := by exact prefixLift 1604536
  have htrace : WordTrace (prefixWord ++ tailWord_1604536) baseStart_1604536 baseEnd_1604536 := by
    simpa [prefixWord, tailWord_1604536, baseEnd_1604536] using wordTrace_append hprefix tailTrace_1604536
  have hstable : (prefixWord ++ tailWord_1604536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604536).length < 2 ^ (prefixWord ++ tailWord_1604536).sum := by decide
  have hdescent : baseEnd_1604536 < baseStart_1604536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604537 : List Nat := [1, 2, 1, 4, 2, 4, 1, 2, 2, 1, 3]
def baseStart_1604537 : Nat := 118140960795 + 1604537 * 2 ^ 59
def prefixEnd_1604537 : Nat := 4983230072969 + 3 ^ 40 * 1604537 * 2
def baseEnd_1604537 : Nat := 823898708923293975308375

theorem tailTrace_1604537 : CollatzResearch.WordTrace tailWord_1604537 prefixEnd_1604537 823898708923293975308375 := by
  unfold tailWord_1604537
  simp only [CollatzResearch.WordTrace]
  refine ⟨58522272188043956947819865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39014848125362637965213243 58522272188043956947819865)
  ·
    refine ⟨43891704141032967710864899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58522272188043956947819865 43891704141032967710864899)
    ·
      refine ⟨65837556211549451566297349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43891704141032967710864899 65837556211549451566297349)
      ·
        refine ⟨12344541789665522168680753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65837556211549451566297349 12344541789665522168680753)
        ·
          refine ⟨9258406342249141626510565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12344541789665522168680753 9258406342249141626510565)
          ·
            refine ⟨1735951189171714054970731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9258406342249141626510565 1735951189171714054970731)
            ·
              refine ⟨2603926783757571082456097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1735951189171714054970731 2603926783757571082456097)
              ·
                refine ⟨1952945087818178311842073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2603926783757571082456097 1952945087818178311842073)
                ·
                  refine ⟨1464708815863633733881555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1952945087818178311842073 1464708815863633733881555)
                  ·
                    refine ⟨2197063223795450600822333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1464708815863633733881555 2197063223795450600822333)
                    ·
                      refine ⟨823898708923293975308375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2197063223795450600822333 823898708923293975308375)
                      ·
                        rfl

theorem cell23_1604537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_1604537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604537 prefixEnd_1604537 := by exact prefixLift 1604537
  have htrace : WordTrace (prefixWord ++ tailWord_1604537) baseStart_1604537 baseEnd_1604537 := by
    simpa [prefixWord, tailWord_1604537, baseEnd_1604537] using wordTrace_append hprefix tailTrace_1604537
  have hstable : (prefixWord ++ tailWord_1604537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604537).length < 2 ^ (prefixWord ++ tailWord_1604537).sum := by decide
  have hdescent : baseEnd_1604537 < baseStart_1604537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604603 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 2, 5, 2]
def baseStart_1604603 : Nat := 118140960795 + 1604603 * 2 ^ 59
def prefixEnd_1604603 : Nat := 4983230072969 + 3 ^ 40 * 1604603 * 2
def baseEnd_1604603 : Nat := 823932598646490717083071

theorem tailTrace_1604603 : CollatzResearch.WordTrace tailWord_1604603 prefixEnd_1604603 823932598646490717083071 := by
  unfold tailWord_1604603
  simp only [CollatzResearch.WordTrace]
  refine ⟨58524679405804850219722463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39016452937203233479814975 58524679405804850219722463)
  ·
    refine ⟨87787019108707275329583695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58524679405804850219722463 87787019108707275329583695)
    ·
      refine ⟨131680528663060912994375543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87787019108707275329583695 131680528663060912994375543)
      ·
        refine ⟨197520792994591369491563315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131680528663060912994375543 197520792994591369491563315)
        ·
          refine ⟨296281189491887054237344973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197520792994591369491563315 296281189491887054237344973)
          ·
            refine ⟨111105446059457645339004365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296281189491887054237344973 111105446059457645339004365)
            ·
              refine ⟨41664542272296617002126637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111105446059457645339004365 41664542272296617002126637)
              ·
                refine ⟨15624203352111231375797489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41664542272296617002126637 15624203352111231375797489)
                ·
                  refine ⟨11718152514083423531848117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15624203352111231375797489 11718152514083423531848117)
                  ·
                    refine ⟨1098576798195320956110761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11718152514083423531848117 1098576798195320956110761)
                    ·
                      refine ⟨823932598646490717083071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1098576798195320956110761 823932598646490717083071)
                      ·
                        rfl

theorem cell23_1604603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 5, 2].length) (baseStart_1604603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604603 prefixEnd_1604603 := by exact prefixLift 1604603
  have htrace : WordTrace (prefixWord ++ tailWord_1604603) baseStart_1604603 baseEnd_1604603 := by
    simpa [prefixWord, tailWord_1604603, baseEnd_1604603] using wordTrace_append hprefix tailTrace_1604603
  have hstable : (prefixWord ++ tailWord_1604603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604603).length < 2 ^ (prefixWord ++ tailWord_1604603).sum := by decide
  have hdescent : baseEnd_1604603 < baseStart_1604603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604633 : List Nat := [1, 2, 1, 2, 1, 1, 5, 3, 2, 1, 4]
def baseStart_1604633 : Nat := 118140960795 + 1604633 * 2 ^ 59
def prefixEnd_1604633 : Nat := 4983230072969 + 3 ^ 40 * 1604633 * 2
def baseEnd_1604633 : Nat := 823948003066125599707933

theorem tailTrace_1604633 : CollatzResearch.WordTrace tailWord_1604633 prefixEnd_1604633 823948003066125599707933 := by
  unfold tailWord_1604633
  simp only [CollatzResearch.WordTrace]
  refine ⟨58525773595696165343314553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39017182397130776895543035 58525773595696165343314553)
  ·
    refine ⟨43894330196772124007485915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58525773595696165343314553 43894330196772124007485915)
    ·
      refine ⟨65841495295158186011228873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43894330196772124007485915 65841495295158186011228873)
      ·
        refine ⟨49381121471368639508421655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65841495295158186011228873 49381121471368639508421655)
        ·
          refine ⟨74071682207052959262632483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49381121471368639508421655 74071682207052959262632483)
          ·
            refine ⟨111107523310579438893948725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74071682207052959262632483 111107523310579438893948725)
            ·
              refine ⟨10416330310366822396307693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111107523310579438893948725 10416330310366822396307693)
              ·
                refine ⟨3906123866387558398615385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10416330310366822396307693 3906123866387558398615385)
                ·
                  refine ⟨2929592899790668798961539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3906123866387558398615385 2929592899790668798961539)
                  ·
                    refine ⟨4394389349686003198442309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2929592899790668798961539 4394389349686003198442309)
                    ·
                      refine ⟨823948003066125599707933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4394389349686003198442309 823948003066125599707933)
                      ·
                        rfl

theorem cell23_1604633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_1604633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604633 prefixEnd_1604633 := by exact prefixLift 1604633
  have htrace : WordTrace (prefixWord ++ tailWord_1604633) baseStart_1604633 baseEnd_1604633 := by
    simpa [prefixWord, tailWord_1604633, baseEnd_1604633] using wordTrace_append hprefix tailTrace_1604633
  have hstable : (prefixWord ++ tailWord_1604633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604633).length < 2 ^ (prefixWord ++ tailWord_1604633).sum := by decide
  have hdescent : baseEnd_1604633 < baseStart_1604633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604717 : List Nat := [1, 5, 1, 1, 2, 2, 1, 3, 3, 1, 3]
def baseStart_1604717 : Nat := 118140960795 + 1604717 * 2 ^ 59
def prefixEnd_1604717 : Nat := 4983230072969 + 3 ^ 40 * 1604717 * 2
def baseEnd_1604717 : Nat := 823991135441103271057547

theorem tailTrace_1604717 : CollatzResearch.WordTrace tailWord_1604717 prefixEnd_1604717 823991135441103271057547 := by
  unfold tailWord_1604717
  simp only [CollatzResearch.WordTrace]
  refine ⟨58528837327391847689372405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39019224884927898459581603 58528837327391847689372405)
  ·
    refine ⟨5487078499442985720878663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58528837327391847689372405 5487078499442985720878663)
    ·
      refine ⟨8230617749164478581317995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5487078499442985720878663 8230617749164478581317995)
      ·
        refine ⟨12345926623746717871976993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8230617749164478581317995 12345926623746717871976993)
        ·
          refine ⟨9259444967810038403982745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12345926623746717871976993 9259444967810038403982745)
          ·
            refine ⟨6944583725857528802987059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9259444967810038403982745 6944583725857528802987059)
            ·
              refine ⟨10416875588786293204480589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6944583725857528802987059 10416875588786293204480589)
              ·
                refine ⟨3906328345794859951680221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10416875588786293204480589 3906328345794859951680221)
                ·
                  refine ⟨1464873129673072481880083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3906328345794859951680221 1464873129673072481880083)
                  ·
                    refine ⟨2197309694509608722820125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1464873129673072481880083 2197309694509608722820125)
                    ·
                      refine ⟨823991135441103271057547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2197309694509608722820125 823991135441103271057547)
                      ·
                        rfl

theorem cell23_1604717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_1604717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604717 prefixEnd_1604717 := by exact prefixLift 1604717
  have htrace : WordTrace (prefixWord ++ tailWord_1604717) baseStart_1604717 baseEnd_1604717 := by
    simpa [prefixWord, tailWord_1604717, baseEnd_1604717] using wordTrace_append hprefix tailTrace_1604717
  have hstable : (prefixWord ++ tailWord_1604717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604717).length < 2 ^ (prefixWord ++ tailWord_1604717).sum := by decide
  have hdescent : baseEnd_1604717 < baseStart_1604717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604737 : List Nat := [1, 2, 4, 2, 2, 2, 2, 2, 1, 5]
def baseStart_1604737 : Nat := 118140960795 + 1604737 * 2 ^ 59
def prefixEnd_1604737 : Nat := 4983230072969 + 3 ^ 40 * 1604737 * 2
def baseEnd_1604737 : Nat := 274667135018064397602485

theorem tailTrace_1604737 : CollatzResearch.WordTrace tailWord_1604737 prefixEnd_1604737 274667135018064397602485 := by
  unfold tailWord_1604737
  simp only [CollatzResearch.WordTrace]
  refine ⟨58529566787319391105100465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39019711191546260736733643 58529566787319391105100465)
  ·
    refine ⟨43897175090489543328825349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58529566787319391105100465 43897175090489543328825349)
    ·
      refine ⟨8230720329466789374154753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43897175090489543328825349 8230720329466789374154753)
      ·
        refine ⟨6173040247100092030616065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8230720329466789374154753 6173040247100092030616065)
        ·
          refine ⟨4629780185325069022962049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6173040247100092030616065 4629780185325069022962049)
          ·
            refine ⟨3472335138993801767221537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4629780185325069022962049 3472335138993801767221537)
            ·
              refine ⟨2604251354245351325416153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3472335138993801767221537 2604251354245351325416153)
              ·
                refine ⟨1953188515684013494062115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2604251354245351325416153 1953188515684013494062115)
                ·
                  refine ⟨2929782773526020241093173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1953188515684013494062115 2929782773526020241093173)
                  ·
                    refine ⟨274667135018064397602485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2929782773526020241093173 274667135018064397602485)
                    ·
                      rfl

theorem cell23_1604737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_1604737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604737 prefixEnd_1604737 := by exact prefixLift 1604737
  have htrace : WordTrace (prefixWord ++ tailWord_1604737) baseStart_1604737 baseEnd_1604737 := by
    simpa [prefixWord, tailWord_1604737, baseEnd_1604737] using wordTrace_append hprefix tailTrace_1604737
  have hstable : (prefixWord ++ tailWord_1604737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604737).length < 2 ^ (prefixWord ++ tailWord_1604737).sum := by decide
  have hdescent : baseEnd_1604737 < baseStart_1604737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604743 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 5]
def baseStart_1604743 : Nat := 118140960795 + 1604743 * 2 ^ 59
def prefixEnd_1604743 : Nat := 4983230072969 + 3 ^ 40 * 1604743 * 2
def baseEnd_1604743 : Nat := 824004485938120169332427

theorem tailTrace_1604743 : CollatzResearch.WordTrace tailWord_1604743 prefixEnd_1604743 824004485938120169332427 := by
  unfold tailWord_1604743
  simp only [CollatzResearch.WordTrace]
  refine ⟨58529785625297654129818883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39019857083531769419879255 58529785625297654129818883)
  ·
    refine ⟨87794678437946481194728325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58529785625297654129818883 87794678437946481194728325)
    ·
      refine ⟨16461502207114965224011561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87794678437946481194728325 16461502207114965224011561)
      ·
        refine ⟨12346126655336223918008671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16461502207114965224011561 12346126655336223918008671)
        ·
          refine ⟨18519189983004335877013007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12346126655336223918008671 18519189983004335877013007)
          ·
            refine ⟨27778784974506503815519511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18519189983004335877013007 27778784974506503815519511)
            ·
              refine ⟨41668177461759755723279267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27778784974506503815519511 41668177461759755723279267)
              ·
                refine ⟨62502266192639633584918901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41668177461759755723279267 62502266192639633584918901)
                ·
                  refine ⟨5859587455559965648586147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62502266192639633584918901 5859587455559965648586147)
                  ·
                    refine ⟨8789381183339948472879221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5859587455559965648586147 8789381183339948472879221)
                    ·
                      refine ⟨824004485938120169332427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8789381183339948472879221 824004485938120169332427)
                      ·
                        rfl

theorem cell23_1604743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_1604743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604743 prefixEnd_1604743 := by exact prefixLift 1604743
  have htrace : WordTrace (prefixWord ++ tailWord_1604743) baseStart_1604743 baseEnd_1604743 := by
    simpa [prefixWord, tailWord_1604743, baseEnd_1604743] using wordTrace_append hprefix tailTrace_1604743
  have hstable : (prefixWord ++ tailWord_1604743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604743).length < 2 ^ (prefixWord ++ tailWord_1604743).sum := by decide
  have hdescent : baseEnd_1604743 < baseStart_1604743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604760 : List Nat := [2, 1, 2, 4, 2, 1, 1, 3, 1, 1, 5]
def baseStart_1604760 : Nat := 118140960795 + 1604760 * 2 ^ 59
def prefixEnd_1604760 : Nat := 4983230072969 + 3 ^ 40 * 1604760 * 2
def baseEnd_1604760 : Nat := 824013215109246602819849

theorem tailTrace_1604760 : CollatzResearch.WordTrace tailWord_1604760 prefixEnd_1604760 824013215109246602819849 := by
  unfold tailWord_1604760
  simp only [CollatzResearch.WordTrace]
  refine ⟨29265202833118033016593867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39020270444157377355458489 29265202833118033016593867)
  ·
    refine ⟨43897804249677049524890801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29265202833118033016593867 43897804249677049524890801)
    ·
      refine ⟨32923353187257787143668101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43897804249677049524890801 32923353187257787143668101)
      ·
        refine ⟨6173128722610835089437769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32923353187257787143668101 6173128722610835089437769)
        ·
          refine ⟨4629846541958126317078327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6173128722610835089437769 4629846541958126317078327)
          ·
            refine ⟨6944769812937189475617491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4629846541958126317078327 6944769812937189475617491)
            ·
              refine ⟨10417154719405784213426237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6944769812937189475617491 10417154719405784213426237)
              ·
                refine ⟨3906433019777169080034839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10417154719405784213426237 3906433019777169080034839)
                ·
                  refine ⟨5859649529665753620052259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3906433019777169080034839 5859649529665753620052259)
                  ·
                    refine ⟨8789474294498630430078389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5859649529665753620052259 8789474294498630430078389)
                    ·
                      refine ⟨824013215109246602819849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8789474294498630430078389 824013215109246602819849)
                      ·
                        rfl

theorem cell23_1604760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_1604760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604760 prefixEnd_1604760 := by exact prefixLift 1604760
  have htrace : WordTrace (prefixWord ++ tailWord_1604760) baseStart_1604760 baseEnd_1604760 := by
    simpa [prefixWord, tailWord_1604760, baseEnd_1604760] using wordTrace_append hprefix tailTrace_1604760
  have hstable : (prefixWord ++ tailWord_1604760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604760).length < 2 ^ (prefixWord ++ tailWord_1604760).sum := by decide
  have hdescent : baseEnd_1604760 < baseStart_1604760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604803 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 5]
def baseStart_1604803 : Nat := 118140960795 + 1604803 * 2 ^ 59
def prefixEnd_1604803 : Nat := 4983230072969 + 3 ^ 40 * 1604803 * 2
def baseEnd_1604803 : Nat := 824035294777389934582151

theorem tailTrace_1604803 : CollatzResearch.WordTrace tailWord_1604803 prefixEnd_1604803 824035294777389934582151 := by
  unfold tailWord_1604803
  simp only [CollatzResearch.WordTrace]
  refine ⟨58531974005080284377003063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39021316003386856251335375 58531974005080284377003063)
  ·
    refine ⟨87797961007620426565504595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58531974005080284377003063 87797961007620426565504595)
    ·
      refine ⟨131696941511430639848256893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87797961007620426565504595 131696941511430639848256893)
      ·
        refine ⟨49386353066786489943096335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131696941511430639848256893 49386353066786489943096335)
        ·
          refine ⟨74079529600179734914644503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49386353066786489943096335 74079529600179734914644503)
          ·
            refine ⟨111119294400269602371966755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74079529600179734914644503 111119294400269602371966755)
            ·
              refine ⟨166678941600404403557950133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111119294400269602371966755 166678941600404403557950133)
              ·
                refine ⟨15626150775037912833557825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166678941600404403557950133 15626150775037912833557825)
                ·
                  refine ⟨11719613081278434625168369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15626150775037912833557825 11719613081278434625168369)
                  ·
                    refine ⟨8789709810958825968876277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11719613081278434625168369 8789709810958825968876277)
                    ·
                      refine ⟨824035294777389934582151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8789709810958825968876277 824035294777389934582151)
                      ·
                        rfl

theorem cell23_1604803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_1604803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604803 prefixEnd_1604803 := by exact prefixLift 1604803
  have htrace : WordTrace (prefixWord ++ tailWord_1604803) baseStart_1604803 baseEnd_1604803 := by
    simpa [prefixWord, tailWord_1604803, baseEnd_1604803] using wordTrace_append hprefix tailTrace_1604803
  have hstable : (prefixWord ++ tailWord_1604803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604803).length < 2 ^ (prefixWord ++ tailWord_1604803).sum := by decide
  have hdescent : baseEnd_1604803 < baseStart_1604803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604840 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 2, 6]
def baseStart_1604840 : Nat := 118140960795 + 1604840 * 2 ^ 59
def prefixEnd_1604840 : Nat := 4983230072969 + 3 ^ 40 * 1604840 * 2
def baseEnd_1604840 : Nat := 274684764520535429939827

theorem tailTrace_1604840 : CollatzResearch.WordTrace tailWord_1604840 prefixEnd_1604840 274684764520535429939827 := by
  unfold tailWord_1604840
  simp only [CollatzResearch.WordTrace]
  refine ⟨29266661752973119848049987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39022215670630826464066649 29266661752973119848049987)
  ·
    refine ⟨43899992629459679772074981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29266661752973119848049987 43899992629459679772074981)
    ·
      refine ⟨8231248618023689957264059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43899992629459679772074981 8231248618023689957264059)
      ·
        refine ⟨12346872927035534935896089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8231248618023689957264059 12346872927035534935896089)
        ·
          refine ⟨9260154695276651201922067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12346872927035534935896089 9260154695276651201922067)
          ·
            refine ⟨13890232042914976802883101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9260154695276651201922067 13890232042914976802883101)
            ·
              refine ⟨5208837016093116301081163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13890232042914976802883101 5208837016093116301081163)
              ·
                refine ⟨7813255524139674451621745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5208837016093116301081163 7813255524139674451621745)
                ·
                  refine ⟨5859941643104755838716309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7813255524139674451621745 5859941643104755838716309)
                  ·
                    refine ⟨274684764520535429939827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5859941643104755838716309 274684764520535429939827)
                    ·
                      rfl

theorem cell23_1604840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_1604840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604840 prefixEnd_1604840 := by exact prefixLift 1604840
  have htrace : WordTrace (prefixWord ++ tailWord_1604840) baseStart_1604840 baseEnd_1604840 := by
    simpa [prefixWord, tailWord_1604840, baseEnd_1604840] using wordTrace_append hprefix tailTrace_1604840
  have hstable : (prefixWord ++ tailWord_1604840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604840).length < 2 ^ (prefixWord ++ tailWord_1604840).sum := by decide
  have hdescent : baseEnd_1604840 < baseStart_1604840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604868 : List Nat := [2, 3, 2, 2, 2, 3, 2, 1, 1, 3, 2]
def baseStart_1604868 : Nat := 118140960795 + 1604868 * 2 ^ 59
def prefixEnd_1604868 : Nat := 4983230072969 + 3 ^ 40 * 1604868 * 2
def baseEnd_1604868 : Nat := 824068671019932180269353

theorem tailTrace_1604868 : CollatzResearch.WordTrace tailWord_1604868 prefixEnd_1604868 824068671019932180269353 := by
  unfold tailWord_1604868
  simp only [CollatzResearch.WordTrace]
  refine ⟨29267172374922400239059629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39022896499896533652079505 29267172374922400239059629)
  ·
    refine ⟨10975189640595900089647361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29267172374922400239059629 10975189640595900089647361)
    ·
      refine ⟨8231392230446925067235521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10975189640595900089647361 8231392230446925067235521)
      ·
        refine ⟨6173544172835193800426641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8231392230446925067235521 6173544172835193800426641)
        ·
          refine ⟨4630158129626395350319981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6173544172835193800426641 4630158129626395350319981)
          ·
            refine ⟨1736309298609898256369993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4630158129626395350319981 1736309298609898256369993)
            ·
              refine ⟨1302231973957423692277495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1736309298609898256369993 1302231973957423692277495)
              ·
                refine ⟨1953347960936135538416243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1302231973957423692277495 1953347960936135538416243)
                ·
                  refine ⟨2930021941404203307624365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1953347960936135538416243 2930021941404203307624365)
                  ·
                    refine ⟨1098758228026576240359137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2930021941404203307624365 1098758228026576240359137)
                    ·
                      refine ⟨824068671019932180269353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1098758228026576240359137 824068671019932180269353)
                      ·
                        rfl

theorem cell23_1604868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_1604868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604868 prefixEnd_1604868 := by exact prefixLift 1604868
  have htrace : WordTrace (prefixWord ++ tailWord_1604868) baseStart_1604868 baseEnd_1604868 := by
    simpa [prefixWord, tailWord_1604868, baseEnd_1604868] using wordTrace_append hprefix tailTrace_1604868
  have hstable : (prefixWord ++ tailWord_1604868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604868).length < 2 ^ (prefixWord ++ tailWord_1604868).sum := by decide
  have hdescent : baseEnd_1604868 < baseStart_1604868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604887 : List Nat := [1, 1, 3, 4, 1, 1, 1, 6, 5]
def baseStart_1604887 : Nat := 118140960795 + 1604887 * 2 ^ 59
def prefixEnd_1604887 : Nat := 4983230072969 + 3 ^ 40 * 1604887 * 2
def baseEnd_1604887 : Nat := 91564269683596400659085

theorem tailTrace_1604887 : CollatzResearch.WordTrace tailWord_1604887 prefixEnd_1604887 91564269683596400659085 := by
  unfold tailWord_1604887
  simp only [CollatzResearch.WordTrace]
  refine ⟨58535037736775966723060915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39023358491183977815373943 58535037736775966723060915)
  ·
    refine ⟨87802556605163950084591373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58535037736775966723060915 87802556605163950084591373)
    ·
      refine ⟨32925958726936481281721765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87802556605163950084591373 32925958726936481281721765)
      ·
        refine ⟨6173617261300590240322831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32925958726936481281721765 6173617261300590240322831)
        ·
          refine ⟨9260425891950885360484247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6173617261300590240322831 9260425891950885360484247)
          ·
            refine ⟨13890638837926328040726371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9260425891950885360484247 13890638837926328040726371)
            ·
              refine ⟨20835958256889492061089557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13890638837926328040726371 20835958256889492061089557)
              ·
                refine ⟨976685543291694940363573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20835958256889492061089557 976685543291694940363573)
                ·
                  refine ⟨91564269683596400659085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 976685543291694940363573 91564269683596400659085)
                  ·
                    rfl

theorem cell23_1604887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 5].length) (baseStart_1604887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604887 prefixEnd_1604887 := by exact prefixLift 1604887
  have htrace : WordTrace (prefixWord ++ tailWord_1604887) baseStart_1604887 baseEnd_1604887 := by
    simpa [prefixWord, tailWord_1604887, baseEnd_1604887] using wordTrace_append hprefix tailTrace_1604887
  have hstable : (prefixWord ++ tailWord_1604887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604887).length < 2 ^ (prefixWord ++ tailWord_1604887).sum := by decide
  have hdescent : baseEnd_1604887 < baseStart_1604887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604898 : List Nat := [3, 3, 1, 1, 5, 1, 1, 1, 1, 4, 2]
def baseStart_1604898 : Nat := 118140960795 + 1604898 * 2 ^ 59
def prefixEnd_1604898 : Nat := 4983230072969 + 3 ^ 40 * 1604898 * 2
def baseEnd_1604898 : Nat := 824084075439567062894215

theorem tailTrace_1604898 : CollatzResearch.WordTrace tailWord_1604898 prefixEnd_1604898 824084075439567062894215 := by
  unfold tailWord_1604898
  simp only [CollatzResearch.WordTrace]
  refine ⟨14633859734934028900427837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39023625959824077067807565 14633859734934028900427837)
  ·
    refine ⟨5487697400600260837660439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14633859734934028900427837 5487697400600260837660439)
    ·
      refine ⟨8231546100900391256490659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5487697400600260837660439 8231546100900391256490659)
      ·
        refine ⟨12347319151350586884735989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8231546100900391256490659 12347319151350586884735989)
        ·
          refine ⟨1157561170439117520443999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12347319151350586884735989 1157561170439117520443999)
          ·
            refine ⟨1736341755658676280665999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157561170439117520443999 1736341755658676280665999)
            ·
              refine ⟨2604512633488014420998999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736341755658676280665999 2604512633488014420998999)
              ·
                refine ⟨3906768950232021631498499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2604512633488014420998999 3906768950232021631498499)
                ·
                  refine ⟨5860153425348032447247749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3906768950232021631498499 5860153425348032447247749)
                  ·
                    refine ⟨1098778767252756083858953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5860153425348032447247749 1098778767252756083858953)
                    ·
                      refine ⟨824084075439567062894215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1098778767252756083858953 824084075439567062894215)
                      ·
                        rfl

theorem cell23_1604898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_1604898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604898 prefixEnd_1604898 := by exact prefixLift 1604898
  have htrace : WordTrace (prefixWord ++ tailWord_1604898) baseStart_1604898 baseEnd_1604898 := by
    simpa [prefixWord, tailWord_1604898, baseEnd_1604898] using wordTrace_append hprefix tailTrace_1604898
  have hstable : (prefixWord ++ tailWord_1604898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604898).length < 2 ^ (prefixWord ++ tailWord_1604898).sum := by decide
  have hdescent : baseEnd_1604898 < baseStart_1604898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604900 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 3, 7]
def baseStart_1604900 : Nat := 118140960795 + 1604900 * 2 ^ 59
def prefixEnd_1604900 : Nat := 4983230072969 + 3 ^ 40 * 1604900 * 2
def baseEnd_1604900 : Nat := 274695034133625351689735

theorem tailTrace_1604900 : CollatzResearch.WordTrace tailWord_1604900 prefixEnd_1604900 274695034133625351689735 := by
  unfold tailWord_1604900
  simp only [CollatzResearch.WordTrace]
  refine ⟨29267755942864434971642077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39023674590485913295522769 29267755942864434971642077)
  ·
    refine ⟨10975408478574163114365779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29267755942864434971642077 10975408478574163114365779)
    ·
      refine ⟨16463112717861244671548669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10975408478574163114365779 16463112717861244671548669)
      ·
        refine ⟨6173667269197966751830751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16463112717861244671548669 6173667269197966751830751)
        ·
          refine ⟨9260500903796950127746127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6173667269197966751830751 9260500903796950127746127)
          ·
            refine ⟨13890751355695425191619191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9260500903796950127746127 13890751355695425191619191)
            ·
              refine ⟨20836127033543137787428787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13890751355695425191619191 20836127033543137787428787)
              ·
                refine ⟨31254190550314706681143181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20836127033543137787428787 31254190550314706681143181)
                ·
                  refine ⟨11720321456368015005428693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31254190550314706681143181 11720321456368015005428693)
                  ·
                    refine ⟨274695034133625351689735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11720321456368015005428693 274695034133625351689735)
                    ·
                      rfl

theorem cell23_1604900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_1604900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604900 prefixEnd_1604900 := by exact prefixLift 1604900
  have htrace : WordTrace (prefixWord ++ tailWord_1604900) baseStart_1604900 baseEnd_1604900 := by
    simpa [prefixWord, tailWord_1604900, baseEnd_1604900] using wordTrace_append hprefix tailTrace_1604900
  have hstable : (prefixWord ++ tailWord_1604900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604900).length < 2 ^ (prefixWord ++ tailWord_1604900).sum := by decide
  have hdescent : baseEnd_1604900 < baseStart_1604900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604921 : List Nat := [1, 2, 1, 6, 2, 2, 1, 3, 5]
def baseStart_1604921 : Nat := 118140960795 + 1604921 * 2 ^ 59
def prefixEnd_1604921 : Nat := 4983230072969 + 3 ^ 40 * 1604921 * 2
def baseEnd_1604921 : Nat := 91566209499402274767401

theorem tailTrace_1604921 : CollatzResearch.WordTrace tailWord_1604921 prefixEnd_1604921 91566209499402274767401 := by
  unfold tailWord_1604921
  simp only [CollatzResearch.WordTrace]
  refine ⟨58536277818652790529798617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39024185212435193686532411 58536277818652790529798617)
  ·
    refine ⟨43902208363989592897348963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58536277818652790529798617 43902208363989592897348963)
    ·
      refine ⟨65853312545984389346023445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43902208363989592897348963 65853312545984389346023445)
      ·
        refine ⟨3086874025593018250594849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65853312545984389346023445 3086874025593018250594849)
        ·
          refine ⟨2315155519194763687946137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3086874025593018250594849 2315155519194763687946137)
          ·
            refine ⟨1736366639396072765959603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2315155519194763687946137 1736366639396072765959603)
            ·
              refine ⟨2604549959094109148939405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736366639396072765959603 2604549959094109148939405)
              ·
                refine ⟨976706234660290930852277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2604549959094109148939405 976706234660290930852277)
                ·
                  refine ⟨91566209499402274767401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 976706234660290930852277 91566209499402274767401)
                  ·
                    rfl

theorem cell23_1604921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 5].length) (baseStart_1604921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604921 prefixEnd_1604921 := by exact prefixLift 1604921
  have htrace : WordTrace (prefixWord ++ tailWord_1604921) baseStart_1604921 baseEnd_1604921 := by
    simpa [prefixWord, tailWord_1604921, baseEnd_1604921] using wordTrace_append hprefix tailTrace_1604921
  have hstable : (prefixWord ++ tailWord_1604921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604921).length < 2 ^ (prefixWord ++ tailWord_1604921).sum := by decide
  have hdescent : baseEnd_1604921 < baseStart_1604921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604937 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 4, 4, 2]
def baseStart_1604937 : Nat := 118140960795 + 1604937 * 2 ^ 59
def prefixEnd_1604937 : Nat := 4983230072969 + 3 ^ 40 * 1604937 * 2
def baseEnd_1604937 : Nat := 824104101185092410306535

theorem tailTrace_1604937 : CollatzResearch.WordTrace tailWord_1604937 prefixEnd_1604937 824104101185092410306535 := by
  unfold tailWord_1604937
  simp only [CollatzResearch.WordTrace]
  refine ⟨58536861386594825262381065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39024574257729883508254043 58536861386594825262381065)
  ·
    refine ⟨43902646039946118946785799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58536861386594825262381065 43902646039946118946785799)
    ·
      refine ⟨65853969059919178420178699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43902646039946118946785799 65853969059919178420178699)
      ·
        refine ⟨98780953589878767630268049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65853969059919178420178699 98780953589878767630268049)
        ·
          refine ⟨74085715192409075722701037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98780953589878767630268049 74085715192409075722701037)
          ·
            refine ⟨27782143197153403396012889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74085715192409075722701037 27782143197153403396012889)
            ·
              refine ⟨20836607397865052547009667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27782143197153403396012889 20836607397865052547009667)
              ·
                refine ⟨31254911096797578820514501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20836607397865052547009667 31254911096797578820514501)
                ·
                  refine ⟨5860295830649546028846469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31254911096797578820514501 5860295830649546028846469)
                  ·
                    refine ⟨1098805468246789880408713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5860295830649546028846469 1098805468246789880408713)
                    ·
                      refine ⟨824104101185092410306535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1098805468246789880408713 824104101185092410306535)
                      ·
                        rfl

theorem cell23_1604937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 4, 2].length) (baseStart_1604937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1604937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1604937 prefixEnd_1604937 := by exact prefixLift 1604937
  have htrace : WordTrace (prefixWord ++ tailWord_1604937) baseStart_1604937 baseEnd_1604937 := by
    simpa [prefixWord, tailWord_1604937, baseEnd_1604937] using wordTrace_append hprefix tailTrace_1604937
  have hstable : (prefixWord ++ tailWord_1604937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604937).length < 2 ^ (prefixWord ++ tailWord_1604937).sum := by decide
  have hdescent : baseEnd_1604937 < baseStart_1604937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605004 : List Nat := [2, 2, 1, 2, 1, 3, 2, 3, 3, 1, 3]
def baseStart_1605004 : Nat := 118140960795 + 1605004 * 2 ^ 59
def prefixEnd_1605004 : Nat := 4983230072969 + 3 ^ 40 * 1605004 * 2
def baseEnd_1605004 : Nat := 824138504388943648168727

theorem tailTrace_1605004 : CollatzResearch.WordTrace tailWord_1605004 prefixEnd_1605004 824138504388943648168727 := by
  unfold tailWord_1605004
  simp only [CollatzResearch.WordTrace]
  refine ⟨29269652538676047852535033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39026203384901397136713377 29269652538676047852535033)
  ·
    refine ⟨21952239404007035889401275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29269652538676047852535033 21952239404007035889401275)
    ·
      refine ⟨32928359106010553834101913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21952239404007035889401275 32928359106010553834101913)
      ·
        refine ⟨24696269329507915375576435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32928359106010553834101913 24696269329507915375576435)
        ·
          refine ⟨37044403994261873063364653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24696269329507915375576435 37044403994261873063364653)
          ·
            refine ⟨13891651497848202398761745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37044403994261873063364653 13891651497848202398761745)
            ·
              refine ⟨10418738623386151799071309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13891651497848202398761745 10418738623386151799071309)
              ·
                refine ⟨3907026983769806924651741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10418738623386151799071309 3907026983769806924651741)
                ·
                  refine ⟨1465135118913677596744403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3907026983769806924651741 1465135118913677596744403)
                  ·
                    refine ⟨2197702678370516395116605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1465135118913677596744403 2197702678370516395116605)
                    ·
                      refine ⟨824138504388943648168727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2197702678370516395116605 824138504388943648168727)
                      ·
                        rfl

theorem cell23_1605004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_1605004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605004 prefixEnd_1605004 := by exact prefixLift 1605004
  have htrace : WordTrace (prefixWord ++ tailWord_1605004) baseStart_1605004 baseEnd_1605004 := by
    simpa [prefixWord, tailWord_1605004, baseEnd_1605004] using wordTrace_append hprefix tailTrace_1605004
  have hstable : (prefixWord ++ tailWord_1605004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605004).length < 2 ^ (prefixWord ++ tailWord_1605004).sum := by decide
  have hdescent : baseEnd_1605004 < baseStart_1605004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605021 : List Nat := [1, 4, 2, 1, 3, 2, 1, 2, 3, 1, 3]
def baseStart_1605021 : Nat := 118140960795 + 1605021 * 2 ^ 59
def prefixEnd_1605021 : Nat := 4983230072969 + 3 ^ 40 * 1605021 * 2
def baseEnd_1605021 : Nat := 824147233560070081656149

theorem tailTrace_1605021 : CollatzResearch.WordTrace tailWord_1605021 prefixEnd_1605021 824147233560070081656149 := by
  unfold tailWord_1605021
  simp only [CollatzResearch.WordTrace]
  refine ⟨58539925118290507608438917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39026616745527005072292611 58539925118290507608438917)
  ·
    refine ⟨10976235959679470176582297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58539925118290507608438917 10976235959679470176582297)
    ·
      refine ⟨8232176969759602632436723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10976235959679470176582297 8232176969759602632436723)
      ·
        refine ⟨12348265454639403948655085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8232176969759602632436723 12348265454639403948655085)
        ·
          refine ⟨4630599545489776480745657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12348265454639403948655085 4630599545489776480745657)
          ·
            refine ⟨3472949659117332360559243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4630599545489776480745657 3472949659117332360559243)
            ·
              refine ⟨5209424488675998540838865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3472949659117332360559243 5209424488675998540838865)
              ·
                refine ⟨3907068366506998905629149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5209424488675998540838865 3907068366506998905629149)
                ·
                  refine ⟨1465150637440124589610931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3907068366506998905629149 1465150637440124589610931)
                  ·
                    refine ⟨2197725956160186884416397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1465150637440124589610931 2197725956160186884416397)
                    ·
                      refine ⟨824147233560070081656149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2197725956160186884416397 824147233560070081656149)
                      ·
                        rfl

theorem cell23_1605021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_1605021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605021 prefixEnd_1605021 := by exact prefixLift 1605021
  have htrace : WordTrace (prefixWord ++ tailWord_1605021) baseStart_1605021 baseEnd_1605021 := by
    simpa [prefixWord, tailWord_1605021, baseEnd_1605021] using wordTrace_append hprefix tailTrace_1605021
  have hstable : (prefixWord ++ tailWord_1605021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605021).length < 2 ^ (prefixWord ++ tailWord_1605021).sum := by decide
  have hdescent : baseEnd_1605021 < baseStart_1605021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605027 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 4]
def baseStart_1605027 : Nat := 118140960795 + 1605027 * 2 ^ 59
def prefixEnd_1605027 : Nat := 4983230072969 + 3 ^ 40 * 1605027 * 2
def baseEnd_1605027 : Nat := 824150314443997058181121

theorem tailTrace_1605027 : CollatzResearch.WordTrace tailWord_1605027 prefixEnd_1605027 824150314443997058181121 := by
  unfold tailWord_1605027
  simp only [CollatzResearch.WordTrace]
  refine ⟨58540143956268770633157335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39026762637512513755438223 58540143956268770633157335)
  ·
    refine ⟨87810215934403155949736003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58540143956268770633157335 87810215934403155949736003)
    ·
      refine ⟨131715323901604733924604005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87810215934403155949736003 131715323901604733924604005)
      ·
        refine ⟨24696623231550887610863251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131715323901604733924604005 24696623231550887610863251)
        ·
          refine ⟨37044934847326331416294877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24696623231550887610863251 37044934847326331416294877)
          ·
            refine ⟨13891850567747374281110579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37044934847326331416294877 13891850567747374281110579)
            ·
              refine ⟨20837775851621061421665869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13891850567747374281110579 20837775851621061421665869)
              ·
                refine ⟨7814165944357898033124701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20837775851621061421665869 7814165944357898033124701)
                ·
                  refine ⟨2930312229134211762421763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7814165944357898033124701 2930312229134211762421763)
                  ·
                    refine ⟨4395468343701317643632645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2930312229134211762421763 4395468343701317643632645)
                    ·
                      refine ⟨824150314443997058181121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4395468343701317643632645 824150314443997058181121)
                      ·
                        rfl

theorem cell23_1605027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_1605027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605027 prefixEnd_1605027 := by exact prefixLift 1605027
  have htrace : WordTrace (prefixWord ++ tailWord_1605027) baseStart_1605027 baseEnd_1605027 := by
    simpa [prefixWord, tailWord_1605027, baseEnd_1605027] using wordTrace_append hprefix tailTrace_1605027
  have hstable : (prefixWord ++ tailWord_1605027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605027).length < 2 ^ (prefixWord ++ tailWord_1605027).sum := by decide
  have hdescent : baseEnd_1605027 < baseStart_1605027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605047 : List Nat := [1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 5]
def baseStart_1605047 : Nat := 118140960795 + 1605047 * 2 ^ 59
def prefixEnd_1605047 : Nat := 4983230072969 + 3 ^ 40 * 1605047 * 2
def baseEnd_1605047 : Nat := 824160584057086979931029

theorem tailTrace_1605047 : CollatzResearch.WordTrace tailWord_1605047 prefixEnd_1605047 824160584057086979931029 := by
  unfold tailWord_1605047
  simp only [CollatzResearch.WordTrace]
  refine ⟨58540873416196314048885395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39027248944130876032590263 58540873416196314048885395)
  ·
    refine ⟨87811310124294471073328093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58540873416196314048885395 87811310124294471073328093)
    ·
      refine ⟨32929241296610426652498035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87811310124294471073328093 32929241296610426652498035)
      ·
        refine ⟨49393861944915639978747053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32929241296610426652498035 49393861944915639978747053)
        ·
          refine ⟨18522698229343364992030145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49393861944915639978747053 18522698229343364992030145)
          ·
            refine ⟨13892023672007523744022609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18522698229343364992030145 13892023672007523744022609)
            ·
              refine ⟨10419017754005642808016957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13892023672007523744022609 10419017754005642808016957)
              ·
                refine ⟨3907131657752116053006359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10419017754005642808016957 3907131657752116053006359)
                ·
                  refine ⟨5860697486628174079509539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3907131657752116053006359 5860697486628174079509539)
                  ·
                    refine ⟨8791046229942261119264309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5860697486628174079509539 8791046229942261119264309)
                    ·
                      refine ⟨824160584057086979931029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8791046229942261119264309 824160584057086979931029)
                      ·
                        rfl

theorem cell23_1605047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_1605047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605047 prefixEnd_1605047 := by exact prefixLift 1605047
  have htrace : WordTrace (prefixWord ++ tailWord_1605047) baseStart_1605047 baseEnd_1605047 := by
    simpa [prefixWord, tailWord_1605047, baseEnd_1605047] using wordTrace_append hprefix tailTrace_1605047
  have hstable : (prefixWord ++ tailWord_1605047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605047).length < 2 ^ (prefixWord ++ tailWord_1605047).sum := by decide
  have hdescent : baseEnd_1605047 < baseStart_1605047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605078 : List Nat := [5, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_1605078 : Nat := 118140960795 + 1605078 * 2 ^ 59
def prefixEnd_1605078 : Nat := 4983230072969 + 3 ^ 40 * 1605078 * 2
def baseEnd_1605078 : Nat := 824176501957376358643387

theorem tailTrace_1605078 : CollatzResearch.WordTrace tailWord_1605078 prefixEnd_1605078 824176501957376358643387 := by
  unfold tailWord_1605078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3658875254942750396453993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39028002719389337562175925 3658875254942750396453993)
  ·
    refine ⟨2744156441207062797340495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3658875254942750396453993 2744156441207062797340495)
    ·
      refine ⟨4116234661810594196010743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2744156441207062797340495 4116234661810594196010743)
      ·
        refine ⟨6174351992715891294016115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4116234661810594196010743 6174351992715891294016115)
        ·
          refine ⟨9261527989073836941024173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6174351992715891294016115 9261527989073836941024173)
          ·
            refine ⟨3473072995902688852884065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9261527989073836941024173 3473072995902688852884065)
            ·
              refine ⟨2604804746927016639663049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3473072995902688852884065 2604804746927016639663049)
              ·
                refine ⟨1953603560195262479747287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2604804746927016639663049 1953603560195262479747287)
                ·
                  refine ⟨2930405340292893719620931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1953603560195262479747287 2930405340292893719620931)
                  ·
                    refine ⟨4395608010439340579431397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2930405340292893719620931 4395608010439340579431397)
                    ·
                      refine ⟨824176501957376358643387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4395608010439340579431397 824176501957376358643387)
                      ·
                        rfl

theorem cell23_1605078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_1605078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605078 prefixEnd_1605078 := by exact prefixLift 1605078
  have htrace : WordTrace (prefixWord ++ tailWord_1605078) baseStart_1605078 baseEnd_1605078 := by
    simpa [prefixWord, tailWord_1605078, baseEnd_1605078] using wordTrace_append hprefix tailTrace_1605078
  have hstable : (prefixWord ++ tailWord_1605078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605078).length < 2 ^ (prefixWord ++ tailWord_1605078).sum := by decide
  have hdescent : baseEnd_1605078 < baseStart_1605078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605081 : List Nat := [1, 2, 1, 2, 4, 3, 2, 2, 1, 2, 3]
def baseStart_1605081 : Nat := 118140960795 + 1605081 * 2 ^ 59
def prefixEnd_1605081 : Nat := 4983230072969 + 3 ^ 40 * 1605081 * 2
def baseEnd_1605081 : Nat := 824178042399339846905873

theorem tailTrace_1605081 : CollatzResearch.WordTrace tailWord_1605081 prefixEnd_1605081 824178042399339846905873 := by
  unfold tailWord_1605081
  simp only [CollatzResearch.WordTrace]
  refine ⟨58542113498073137855623097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39028075665382091903748731 58542113498073137855623097)
  ·
    refine ⟨43906585123554853391717323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58542113498073137855623097 43906585123554853391717323)
    ·
      refine ⟨65859877685332280087575985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43906585123554853391717323 65859877685332280087575985)
      ·
        refine ⟨49394908263999210065681989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65859877685332280087575985 49394908263999210065681989)
        ·
          refine ⟨9261545299499851887315373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49394908263999210065681989 9261545299499851887315373)
          ·
            refine ⟨3473079487312444457743265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9261545299499851887315373 3473079487312444457743265)
            ·
              refine ⟨2604809615484333343307449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3473079487312444457743265 2604809615484333343307449)
              ·
                refine ⟨1953607211613250007480587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2604809615484333343307449 1953607211613250007480587)
                ·
                  refine ⟨2930410817419875011220881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1953607211613250007480587 2930410817419875011220881)
                  ·
                    refine ⟨2197808113064906258415661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2930410817419875011220881 2197808113064906258415661)
                    ·
                      refine ⟨824178042399339846905873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2197808113064906258415661 824178042399339846905873)
                      ·
                        rfl

theorem cell23_1605081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 2, 3].length) (baseStart_1605081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605081 prefixEnd_1605081 := by exact prefixLift 1605081
  have htrace : WordTrace (prefixWord ++ tailWord_1605081) baseStart_1605081 baseEnd_1605081 := by
    simpa [prefixWord, tailWord_1605081, baseEnd_1605081] using wordTrace_append hprefix tailTrace_1605081
  have hstable : (prefixWord ++ tailWord_1605081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605081).length < 2 ^ (prefixWord ++ tailWord_1605081).sum := by decide
  have hdescent : baseEnd_1605081 < baseStart_1605081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605095 : List Nat := [1, 1, 5, 2, 1, 2, 3, 3, 1, 2, 2]
def baseStart_1605095 : Nat := 118140960795 + 1605095 * 2 ^ 59
def prefixEnd_1605095 : Nat := 4983230072969 + 3 ^ 40 * 1605095 * 2
def baseEnd_1605095 : Nat := 824185231128502792130809

theorem tailTrace_1605095 : CollatzResearch.WordTrace tailWord_1605095 prefixEnd_1605095 824185231128502792130809 := by
  unfold tailWord_1605095
  simp only [CollatzResearch.WordTrace]
  refine ⟨58542624120022418246632739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39028416080014945497755159 58542624120022418246632739)
  ·
    refine ⟨87813936180033627369949109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58542624120022418246632739 87813936180033627369949109)
    ·
      refine ⟨8232556516878152565932729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87813936180033627369949109 8232556516878152565932729)
      ·
        refine ⟨6174417387658614424449547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8232556516878152565932729 6174417387658614424449547)
        ·
          refine ⟨9261626081487921636674321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6174417387658614424449547 9261626081487921636674321)
          ·
            refine ⟨6946219561115941227505741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9261626081487921636674321 6946219561115941227505741)
            ·
              refine ⟨2604832335418477960314653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6946219561115941227505741 2604832335418477960314653)
              ·
                refine ⟨976812125781929235117995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2604832335418477960314653 976812125781929235117995)
                ·
                  refine ⟨1465218188672893852676993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 976812125781929235117995 1465218188672893852676993)
                  ·
                    refine ⟨1098913641504670389507745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1465218188672893852676993 1098913641504670389507745)
                    ·
                      refine ⟨824185231128502792130809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1098913641504670389507745 824185231128502792130809)
                      ·
                        rfl

theorem cell23_1605095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_1605095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605095 prefixEnd_1605095 := by exact prefixLift 1605095
  have htrace : WordTrace (prefixWord ++ tailWord_1605095) baseStart_1605095 baseEnd_1605095 := by
    simpa [prefixWord, tailWord_1605095, baseEnd_1605095] using wordTrace_append hprefix tailTrace_1605095
  have hstable : (prefixWord ++ tailWord_1605095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605095).length < 2 ^ (prefixWord ++ tailWord_1605095).sum := by decide
  have hdescent : baseEnd_1605095 < baseStart_1605095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605101 : List Nat := [1, 5, 1, 3, 3, 1, 9]
def baseStart_1605101 : Nat := 118140960795 + 1605101 * 2 ^ 59
def prefixEnd_1605101 : Nat := 4983230072969 + 3 ^ 40 * 1605101 * 2
def baseEnd_1605101 : Nat := 10175164345832466279701

theorem tailTrace_1605101 : CollatzResearch.WordTrace tailWord_1605101 prefixEnd_1605101 10175164345832466279701 := by
  unfold tailWord_1605101
  simp only [CollatzResearch.WordTrace]
  refine ⟨58542842958000681271351157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39028561972000454180900771 58542842958000681271351157)
  ·
    refine ⟨5488391527312563869189171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58542842958000681271351157 5488391527312563869189171)
    ·
      refine ⟨8232587290968845803783757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5488391527312563869189171 8232587290968845803783757)
      ·
        refine ⟨3087220234113317176418909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8232587290968845803783757 3087220234113317176418909)
        ·
          refine ⟨1157707587792493941157091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3087220234113317176418909 1157707587792493941157091)
          ·
            refine ⟨1736561381688740911735637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157707587792493941157091 1736561381688740911735637)
            ·
              refine ⟨10175164345832466279701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1736561381688740911735637 10175164345832466279701)
              ·
                rfl

theorem cell23_1605101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 9].length) (baseStart_1605101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605101 prefixEnd_1605101 := by exact prefixLift 1605101
  have htrace : WordTrace (prefixWord ++ tailWord_1605101) baseStart_1605101 baseEnd_1605101 := by
    simpa [prefixWord, tailWord_1605101, baseEnd_1605101] using wordTrace_append hprefix tailTrace_1605101
  have hstable : (prefixWord ++ tailWord_1605101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605101).length < 2 ^ (prefixWord ++ tailWord_1605101).sum := by decide
  have hdescent : baseEnd_1605101 < baseStart_1605101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605128 : List Nat := [2, 1, 3, 2, 1, 1, 6, 1, 2, 1, 3]
def baseStart_1605128 : Nat := 118140960795 + 1605128 * 2 ^ 59
def prefixEnd_1605128 : Nat := 4983230072969 + 3 ^ 40 * 1605128 * 2
def baseEnd_1605128 : Nat := 824202175990101163018157

theorem tailTrace_1605128 : CollatzResearch.WordTrace tailWord_1605128 prefixEnd_1605128 824202175990101163018157 := by
  unfold tailWord_1605128
  simp only [CollatzResearch.WordTrace]
  refine ⟨29271913864451432441292019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39029218485935243255056025 29271913864451432441292019)
  ·
    refine ⟨43907870796677148661938029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29271913864451432441292019 43907870796677148661938029)
    ·
      refine ⟨16465451548753930748226761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43907870796677148661938029 16465451548753930748226761)
      ·
        refine ⟨12349088661565448061170071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16465451548753930748226761 12349088661565448061170071)
        ·
          refine ⟨18523632992348172091755107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12349088661565448061170071 18523632992348172091755107)
          ·
            refine ⟨27785449488522258137632661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18523632992348172091755107 27785449488522258137632661)
            ·
              refine ⟨1302442944774480850201531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27785449488522258137632661 1302442944774480850201531)
              ·
                refine ⟨1953664417161721275302297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1302442944774480850201531 1953664417161721275302297)
                ·
                  refine ⟨1465248312871290956476723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1953664417161721275302297 1465248312871290956476723)
                  ·
                    refine ⟨2197872469306936434715085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1465248312871290956476723 2197872469306936434715085)
                    ·
                      refine ⟨824202175990101163018157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2197872469306936434715085 824202175990101163018157)
                      ·
                        rfl

theorem cell23_1605128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_1605128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605128 prefixEnd_1605128 := by exact prefixLift 1605128
  have htrace : WordTrace (prefixWord ++ tailWord_1605128) baseStart_1605128 baseEnd_1605128 := by
    simpa [prefixWord, tailWord_1605128, baseEnd_1605128] using wordTrace_append hprefix tailTrace_1605128
  have hstable : (prefixWord ++ tailWord_1605128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605128).length < 2 ^ (prefixWord ++ tailWord_1605128).sum := by decide
  have hdescent : baseEnd_1605128 < baseStart_1605128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605137 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 5]
def baseStart_1605137 : Nat := 118140960795 + 1605137 * 2 ^ 59
def prefixEnd_1605137 : Nat := 4983230072969 + 3 ^ 40 * 1605137 * 2
def baseEnd_1605137 : Nat := 824206797315991627805615

theorem tailTrace_1605137 : CollatzResearch.WordTrace tailWord_1605137 prefixEnd_1605137 824206797315991627805615 := by
  unfold tailWord_1605137
  simp only [CollatzResearch.WordTrace]
  refine ⟨58544155985870259419661665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39029437323913506279774443 58544155985870259419661665)
  ·
    refine ⟨43908116989402694564746249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58544155985870259419661665 43908116989402694564746249)
    ·
      refine ⟨32931087742052020923559687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43908116989402694564746249 32931087742052020923559687)
      ·
        refine ⟨49396631613078031385339531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32931087742052020923559687 49396631613078031385339531)
        ·
          refine ⟨74094947419617047078009297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49396631613078031385339531 74094947419617047078009297)
          ·
            refine ⟨55571210564712785308506973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74094947419617047078009297 55571210564712785308506973)
            ·
              refine ⟨20839203961767294490690115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55571210564712785308506973 20839203961767294490690115)
              ·
                refine ⟨31258805942650941736035173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20839203961767294490690115 31258805942650941736035173)
                ·
                  refine ⟨5861026114247051575506595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31258805942650941736035173 5861026114247051575506595)
                  ·
                    refine ⟨8791539171370577363259893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5861026114247051575506595 8791539171370577363259893)
                    ·
                      refine ⟨824206797315991627805615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8791539171370577363259893 824206797315991627805615)
                      ·
                        rfl

theorem cell23_1605137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_1605137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605137 prefixEnd_1605137 := by exact prefixLift 1605137
  have htrace : WordTrace (prefixWord ++ tailWord_1605137) baseStart_1605137 baseEnd_1605137 := by
    simpa [prefixWord, tailWord_1605137, baseEnd_1605137] using wordTrace_append hprefix tailTrace_1605137
  have hstable : (prefixWord ++ tailWord_1605137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605137).length < 2 ^ (prefixWord ++ tailWord_1605137).sum := by decide
  have hdescent : baseEnd_1605137 < baseStart_1605137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605151 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 6, 2, 2]
def baseStart_1605151 : Nat := 118140960795 + 1605151 * 2 ^ 59
def prefixEnd_1605151 : Nat := 4983230072969 + 3 ^ 40 * 1605151 * 2
def baseEnd_1605151 : Nat := 824213986045154573030551

theorem tailTrace_1605151 : CollatzResearch.WordTrace tailWord_1605151 prefixEnd_1605151 824213986045154573030551 := by
  unfold tailWord_1605151
  simp only [CollatzResearch.WordTrace]
  refine ⟨58544666607819539810671307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39029777738546359873780871 58544666607819539810671307)
  ·
    refine ⟨87816999911729309716006961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58544666607819539810671307 87816999911729309716006961)
    ·
      refine ⟨65862749933796982287005221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87816999911729309716006961 65862749933796982287005221)
      ·
        refine ⟨12349265612586934178813479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65862749933796982287005221 12349265612586934178813479)
        ·
          refine ⟨18523898418880401268220219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12349265612586934178813479 18523898418880401268220219)
          ·
            refine ⟨27785847628320601902330329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18523898418880401268220219 27785847628320601902330329)
            ·
              refine ⟨20839385721240451426747747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27785847628320601902330329 20839385721240451426747747)
              ·
                refine ⟨31259078581860677140121621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20839385721240451426747747 31259078581860677140121621)
                ·
                  refine ⟨1465269308524719240943201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31259078581860677140121621 1465269308524719240943201)
                  ·
                    refine ⟨1098951981393539430707401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1465269308524719240943201 1098951981393539430707401)
                    ·
                      refine ⟨824213986045154573030551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1098951981393539430707401 824213986045154573030551)
                      ·
                        rfl

theorem cell23_1605151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_1605151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605151 prefixEnd_1605151 := by exact prefixLift 1605151
  have htrace : WordTrace (prefixWord ++ tailWord_1605151) baseStart_1605151 baseEnd_1605151 := by
    simpa [prefixWord, tailWord_1605151, baseEnd_1605151] using wordTrace_append hprefix tailTrace_1605151
  have hstable : (prefixWord ++ tailWord_1605151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605151).length < 2 ^ (prefixWord ++ tailWord_1605151).sum := by decide
  have hdescent : baseEnd_1605151 < baseStart_1605151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605154 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_1605154 : Nat := 118140960795 + 1605154 * 2 ^ 59
def prefixEnd_1605154 : Nat := 4983230072969 + 3 ^ 40 * 1605154 * 2
def baseEnd_1605154 : Nat := 824215526487118061293037

theorem tailTrace_1605154 : CollatzResearch.WordTrace tailWord_1605154 prefixEnd_1605154 824215526487118061293037 := by
  unfold tailWord_1605154
  simp only [CollatzResearch.WordTrace]
  refine ⟨14636194006702167830757629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39029850684539114215353677 14636194006702167830757629)
  ·
    refine ⟨5488572752513312936534111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14636194006702167830757629 5488572752513312936534111)
    ·
      refine ⟨8232859128769969404801167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5488572752513312936534111 8232859128769969404801167)
      ·
        refine ⟨12349288693154954107201751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8232859128769969404801167 12349288693154954107201751)
        ·
          refine ⟨18523933039732431160802627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12349288693154954107201751 18523933039732431160802627)
          ·
            refine ⟨27785899559598646741203941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18523933039732431160802627 27785899559598646741203941)
            ·
              refine ⟨5209856167424746263975739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27785899559598646741203941 5209856167424746263975739)
              ·
                refine ⟨7814784251137119395963609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5209856167424746263975739 7814784251137119395963609)
                ·
                  refine ⟨5861088188352839546972707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7814784251137119395963609 5861088188352839546972707)
                  ·
                    refine ⟨8791632282529259320459061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5861088188352839546972707 8791632282529259320459061)
                    ·
                      refine ⟨824215526487118061293037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8791632282529259320459061 824215526487118061293037)
                      ·
                        rfl

theorem cell23_1605154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_1605154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605154 prefixEnd_1605154 := by exact prefixLift 1605154
  have htrace : WordTrace (prefixWord ++ tailWord_1605154) baseStart_1605154 baseEnd_1605154 := by
    simpa [prefixWord, tailWord_1605154, baseEnd_1605154] using wordTrace_append hprefix tailTrace_1605154
  have hstable : (prefixWord ++ tailWord_1605154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605154).length < 2 ^ (prefixWord ++ tailWord_1605154).sum := by decide
  have hdescent : baseEnd_1605154 < baseStart_1605154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605155 : List Nat := [1, 1, 1, 4, 5, 1, 3, 1, 1, 3, 2]
def baseStart_1605155 : Nat := 118140960795 + 1605155 * 2 ^ 59
def prefixEnd_1605155 : Nat := 4983230072969 + 3 ^ 40 * 1605155 * 2
def baseEnd_1605155 : Nat := 824216039967772557380533

theorem tailTrace_1605155 : CollatzResearch.WordTrace tailWord_1605155 prefixEnd_1605155 824216039967772557380533 := by
  unfold tailWord_1605155
  simp only [CollatzResearch.WordTrace]
  refine ⟨58544812499805048493816919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39029874999870032329211279 58544812499805048493816919)
  ·
    refine ⟨87817218749707572740725379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58544812499805048493816919 87817218749707572740725379)
    ·
      refine ⟨131725828124561359111088069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87817218749707572740725379 131725828124561359111088069)
      ·
        refine ⟨24698592773355254833329013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131725828124561359111088069 24698592773355254833329013)
        ·
          refine ⟨2315493072502055140624595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24698592773355254833329013 2315493072502055140624595)
          ·
            refine ⟨3473239608753082710936893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2315493072502055140624595 3473239608753082710936893)
            ·
              refine ⟨1302464853282406016601335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3473239608753082710936893 1302464853282406016601335)
              ·
                refine ⟨1953697279923609024902003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1302464853282406016601335 1953697279923609024902003)
                ·
                  refine ⟨2930545919885413537353005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1953697279923609024902003 2930545919885413537353005)
                  ·
                    refine ⟨1098954719957030076507377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2930545919885413537353005 1098954719957030076507377)
                    ·
                      refine ⟨824216039967772557380533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1098954719957030076507377 824216039967772557380533)
                      ·
                        rfl

theorem cell23_1605155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_1605155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605155 prefixEnd_1605155 := by exact prefixLift 1605155
  have htrace : WordTrace (prefixWord ++ tailWord_1605155) baseStart_1605155 baseEnd_1605155 := by
    simpa [prefixWord, tailWord_1605155, baseEnd_1605155] using wordTrace_append hprefix tailTrace_1605155
  have hstable : (prefixWord ++ tailWord_1605155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605155).length < 2 ^ (prefixWord ++ tailWord_1605155).sum := by decide
  have hdescent : baseEnd_1605155 < baseStart_1605155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605181 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 2, 2, 4]
def baseStart_1605181 : Nat := 118140960795 + 1605181 * 2 ^ 59
def prefixEnd_1605181 : Nat := 4983230072969 + 3 ^ 40 * 1605181 * 2
def baseEnd_1605181 : Nat := 824229390464789455655413

theorem tailTrace_1605181 : CollatzResearch.WordTrace tailWord_1605181 prefixEnd_1605181 824229390464789455655413 := by
  unfold tailWord_1605181
  simp only [CollatzResearch.WordTrace]
  refine ⟨58545760797710854934263397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39030507198473903289508931 58545760797710854934263397)
  ·
    refine ⟨10977330149570785300174387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58545760797710854934263397 10977330149570785300174387)
    ·
      refine ⟨16465995224356177950261581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10977330149570785300174387 16465995224356177950261581)
      ·
        refine ⟨6174748209133566731348093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16465995224356177950261581 6174748209133566731348093)
        ·
          refine ⟨2315530578425087524255535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6174748209133566731348093 2315530578425087524255535)
          ·
            refine ⟨3473295867637631286383303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2315530578425087524255535 3473295867637631286383303)
            ·
              refine ⟨5209943801456446929574955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3473295867637631286383303 5209943801456446929574955)
              ·
                refine ⟨7814915702184670394362433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5209943801456446929574955 7814915702184670394362433)
                ·
                  refine ⟨5861186776638502795771825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7814915702184670394362433 5861186776638502795771825)
                  ·
                    refine ⟨4395890082478877096828869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5861186776638502795771825 4395890082478877096828869)
                    ·
                      refine ⟨824229390464789455655413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4395890082478877096828869 824229390464789455655413)
                      ·
                        rfl

theorem cell23_1605181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_1605181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605181 prefixEnd_1605181 := by exact prefixLift 1605181
  have htrace : WordTrace (prefixWord ++ tailWord_1605181) baseStart_1605181 baseEnd_1605181 := by
    simpa [prefixWord, tailWord_1605181, baseEnd_1605181] using wordTrace_append hprefix tailTrace_1605181
  have hstable : (prefixWord ++ tailWord_1605181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605181).length < 2 ^ (prefixWord ++ tailWord_1605181).sum := by decide
  have hdescent : baseEnd_1605181 < baseStart_1605181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605204 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_1605204 : Nat := 118140960795 + 1605204 * 2 ^ 59
def prefixEnd_1605204 : Nat := 4983230072969 + 3 ^ 40 * 1605204 * 2
def baseEnd_1605204 : Nat := 274747066839947621889269

theorem tailTrace_1605204 : CollatzResearch.WordTrace tailWord_1605204 prefixEnd_1605204 274747066839947621889269 := by
  unfold tailWord_1605204
  simp only [CollatzResearch.WordTrace]
  refine ⟨29273299838313764931175333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39031066451085019908233777 29273299838313764931175333)
  ·
    refine ⟨5488743719683830924595375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29273299838313764931175333 5488743719683830924595375)
    ·
      refine ⟨8233115579525746386893063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5488743719683830924595375 8233115579525746386893063)
      ·
        refine ⟨12349673369288619580339595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8233115579525746386893063 12349673369288619580339595)
        ·
          refine ⟨18524510053932929370509393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12349673369288619580339595 18524510053932929370509393)
          ·
            refine ⟨13893382540449697027882045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18524510053932929370509393 13893382540449697027882045)
            ·
              refine ⟨5210018452668636385455767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13893382540449697027882045 5210018452668636385455767)
              ·
                refine ⟨7815027679002954578183651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5210018452668636385455767 7815027679002954578183651)
                ·
                  refine ⟨11722541518504431867275477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7815027679002954578183651 11722541518504431867275477)
                  ·
                    refine ⟨274747066839947621889269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11722541518504431867275477 274747066839947621889269)
                    ·
                      rfl

theorem cell23_1605204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_1605204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605204 prefixEnd_1605204 := by exact prefixLift 1605204
  have htrace : WordTrace (prefixWord ++ tailWord_1605204) baseStart_1605204 baseEnd_1605204 := by
    simpa [prefixWord, tailWord_1605204, baseEnd_1605204] using wordTrace_append hprefix tailTrace_1605204
  have hstable : (prefixWord ++ tailWord_1605204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605204).length < 2 ^ (prefixWord ++ tailWord_1605204).sum := by decide
  have hdescent : baseEnd_1605204 < baseStart_1605204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605206 : List Nat := [5, 2, 2, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_1605206 : Nat := 118140960795 + 1605206 * 2 ^ 59
def prefixEnd_1605206 : Nat := 4983230072969 + 3 ^ 40 * 1605206 * 2
def baseEnd_1605206 : Nat := 824242227481151857842799

theorem tailTrace_1605206 : CollatzResearch.WordTrace tailWord_1605206 prefixEnd_1605206 824242227481151857842799 := by
  unfold tailWord_1605206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3659167038913767762745217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39031115081746856135948981 3659167038913767762745217)
  ·
    refine ⟨2744375279185325822058913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3659167038913767762745217 2744375279185325822058913)
    ·
      refine ⟨2058281459388994366544185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2744375279185325822058913 2058281459388994366544185)
      ·
        refine ⟨1543711094541745774908139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2058281459388994366544185 1543711094541745774908139)
        ·
          refine ⟨2315566641812618662362209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1543711094541745774908139 2315566641812618662362209)
          ·
            refine ⟨1736674981359463996771657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2315566641812618662362209 1736674981359463996771657)
            ·
              refine ⟨1302506236019597997578743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1736674981359463996771657 1302506236019597997578743)
              ·
                refine ⟨1953759354029396996368115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1302506236019597997578743 1953759354029396996368115)
                ·
                  refine ⟨2930639031044095494552173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1953759354029396996368115 2930639031044095494552173)
                  ·
                    refine ⟨1098989636641535810457065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2930639031044095494552173 1098989636641535810457065)
                    ·
                      refine ⟨824242227481151857842799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1098989636641535810457065 824242227481151857842799)
                      ·
                        rfl

theorem cell23_1605206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_1605206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605206 prefixEnd_1605206 := by exact prefixLift 1605206
  have htrace : WordTrace (prefixWord ++ tailWord_1605206) baseStart_1605206 baseEnd_1605206 := by
    simpa [prefixWord, tailWord_1605206, baseEnd_1605206] using wordTrace_append hprefix tailTrace_1605206
  have hstable : (prefixWord ++ tailWord_1605206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605206).length < 2 ^ (prefixWord ++ tailWord_1605206).sum := by decide
  have hdescent : baseEnd_1605206 < baseStart_1605206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605241 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 2, 4, 2]
def baseStart_1605241 : Nat := 118140960795 + 1605241 * 2 ^ 59
def prefixEnd_1605241 : Nat := 4983230072969 + 3 ^ 40 * 1605241 * 2
def baseEnd_1605241 : Nat := 824260199304059220905137

theorem tailTrace_1605241 : CollatzResearch.WordTrace tailWord_1605241 prefixEnd_1605241 824260199304059220905137 := by
  unfold tailWord_1605241
  simp only [CollatzResearch.WordTrace]
  refine ⟨58547949177493485181447577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39031966118328990120965051 58547949177493485181447577)
  ·
    refine ⟨43910961883120113886085683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58547949177493485181447577 43910961883120113886085683)
    ·
      refine ⟨65866442824680170829128525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43910961883120113886085683 65866442824680170829128525)
      ·
        refine ⟨24699916059255064060923197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65866442824680170829128525 24699916059255064060923197)
        ·
          refine ⟨9262468522220649022846199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24699916059255064060923197 9262468522220649022846199)
          ·
            refine ⟨13893702783330973534269299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9262468522220649022846199 13893702783330973534269299)
            ·
              refine ⟨20840554174996460301403949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13893702783330973534269299 20840554174996460301403949)
              ·
                refine ⟨7815207815623672613026481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20840554174996460301403949 7815207815623672613026481)
                ·
                  refine ⟨5861405861717754459769861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7815207815623672613026481 5861405861717754459769861)
                  ·
                    refine ⟨1099013599072078961206849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5861405861717754459769861 1099013599072078961206849)
                    ·
                      refine ⟨824260199304059220905137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1099013599072078961206849 824260199304059220905137)
                      ·
                        rfl

theorem cell23_1605241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_1605241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605241 prefixEnd_1605241 := by exact prefixLift 1605241
  have htrace : WordTrace (prefixWord ++ tailWord_1605241) baseStart_1605241 baseEnd_1605241 := by
    simpa [prefixWord, tailWord_1605241, baseEnd_1605241] using wordTrace_append hprefix tailTrace_1605241
  have hstable : (prefixWord ++ tailWord_1605241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605241).length < 2 ^ (prefixWord ++ tailWord_1605241).sum := by decide
  have hdescent : baseEnd_1605241 < baseStart_1605241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605278 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_1605278 : Nat := 118140960795 + 1605278 * 2 ^ 59
def prefixEnd_1605278 : Nat := 4983230072969 + 3 ^ 40 * 1605278 * 2
def baseEnd_1605278 : Nat := 824279198088275576142467

theorem tailTrace_1605278 : CollatzResearch.WordTrace tailWord_1605278 prefixEnd_1605278 824279198088275576142467 := by
  unfold tailWord_1605278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7318662334794930062568061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39032865785572960333696325 7318662334794930062568061)
  ·
    refine ⟨2744498375548098773463023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7318662334794930062568061 2744498375548098773463023)
    ·
      refine ⟨4116747563322148160194535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2744498375548098773463023 4116747563322148160194535)
      ·
        refine ⟨6175121344983222240291803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4116747563322148160194535 6175121344983222240291803)
        ·
          refine ⟨9262682017474833360437705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6175121344983222240291803 9262682017474833360437705)
          ·
            refine ⟨6947011513106125020328279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9262682017474833360437705 6947011513106125020328279)
            ·
              refine ⟨10420517269659187530492419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6947011513106125020328279 10420517269659187530492419)
              ·
                refine ⟨15630775904488781295738629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10420517269659187530492419 15630775904488781295738629)
                ·
                  refine ⟨2930770482091646492950993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15630775904488781295738629 2930770482091646492950993)
                  ·
                    refine ⟨2198077861568734869713245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2930770482091646492950993 2198077861568734869713245)
                    ·
                      refine ⟨824279198088275576142467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2198077861568734869713245 824279198088275576142467)
                      ·
                        rfl

theorem cell23_1605278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_1605278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605278 prefixEnd_1605278 := by exact prefixLift 1605278
  have htrace : WordTrace (prefixWord ++ tailWord_1605278) baseStart_1605278 baseEnd_1605278 := by
    simpa [prefixWord, tailWord_1605278, baseEnd_1605278] using wordTrace_append hprefix tailTrace_1605278
  have hstable : (prefixWord ++ tailWord_1605278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605278).length < 2 ^ (prefixWord ++ tailWord_1605278).sum := by decide
  have hdescent : baseEnd_1605278 < baseStart_1605278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605344 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 6]
def baseStart_1605344 : Nat := 118140960795 + 1605344 * 2 ^ 59
def prefixEnd_1605344 : Nat := 4983230072969 + 3 ^ 40 * 1605344 * 2
def baseEnd_1605344 : Nat := 824313087811472317917163

theorem tailTrace_1605344 : CollatzResearch.WordTrace tailWord_1605344 prefixEnd_1605344 824313087811472317917163 := by
  unfold tailWord_1605344
  simp only [CollatzResearch.WordTrace]
  refine ⟨29275852948060166886223543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39034470597413555848298057 29275852948060166886223543)
  ·
    refine ⟨43913779422090250329335315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29275852948060166886223543 43913779422090250329335315)
    ·
      refine ⟨65870669133135375494002973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43913779422090250329335315 65870669133135375494002973)
      ·
        refine ⟨24701500924925765810251115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65870669133135375494002973 24701500924925765810251115)
        ·
          refine ⟨37052251387388648715376673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24701500924925765810251115 37052251387388648715376673)
          ·
            refine ⟨27789188540541486536532505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37052251387388648715376673 27789188540541486536532505)
            ·
              refine ⟨20841891405406114902399379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27789188540541486536532505 20841891405406114902399379)
              ·
                refine ⟨31262837108109172353599069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20841891405406114902399379 31262837108109172353599069)
                ·
                  refine ⟨11723563915540939632599651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31262837108109172353599069 11723563915540939632599651)
                  ·
                    refine ⟨17585345873311409448899477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11723563915540939632599651 17585345873311409448899477)
                    ·
                      refine ⟨824313087811472317917163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17585345873311409448899477 824313087811472317917163)
                      ·
                        rfl

theorem cell23_1605344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_1605344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605344 prefixEnd_1605344 := by exact prefixLift 1605344
  have htrace : WordTrace (prefixWord ++ tailWord_1605344) baseStart_1605344 baseEnd_1605344 := by
    simpa [prefixWord, tailWord_1605344, baseEnd_1605344] using wordTrace_append hprefix tailTrace_1605344
  have hstable : (prefixWord ++ tailWord_1605344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605344).length < 2 ^ (prefixWord ++ tailWord_1605344).sum := by decide
  have hdescent : baseEnd_1605344 < baseStart_1605344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605358 : List Nat := [4, 1, 2, 1, 1, 2, 1, 5, 2, 4]
def baseStart_1605358 : Nat := 118140960795 + 1605358 * 2 ^ 59
def prefixEnd_1605358 : Nat := 4983230072969 + 3 ^ 40 * 1605358 * 2
def baseEnd_1605358 : Nat := 274773425513545087714033

theorem tailTrace_1605358 : CollatzResearch.WordTrace tailWord_1605358 prefixEnd_1605358 274773425513545087714033 := by
  unfold tailWord_1605358
  simp only [CollatzResearch.WordTrace]
  refine ⟨7319027064758701770432091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39034811012046409442304485 7319027064758701770432091)
  ·
    refine ⟨10978540597138052655648137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7319027064758701770432091 10978540597138052655648137)
    ·
      refine ⟨8233905447853539491736103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10978540597138052655648137 8233905447853539491736103)
      ·
        refine ⟨12350858171780309237604155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8233905447853539491736103 12350858171780309237604155)
        ·
          refine ⟨18526287257670463856406233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12350858171780309237604155 18526287257670463856406233)
          ·
            refine ⟨13894715443252847892304675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18526287257670463856406233 13894715443252847892304675)
            ·
              refine ⟨20842073164879271838457013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13894715443252847892304675 20842073164879271838457013)
              ·
                refine ⟨1953944359207431734855345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20842073164879271838457013 1953944359207431734855345)
                ·
                  refine ⟨1465458269405573801141509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1953944359207431734855345 1465458269405573801141509)
                  ·
                    refine ⟨274773425513545087714033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1465458269405573801141509 274773425513545087714033)
                    ·
                      rfl

theorem cell23_1605358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_1605358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605358 prefixEnd_1605358 := by exact prefixLift 1605358
  have htrace : WordTrace (prefixWord ++ tailWord_1605358) baseStart_1605358 baseEnd_1605358 := by
    simpa [prefixWord, tailWord_1605358, baseEnd_1605358] using wordTrace_append hprefix tailTrace_1605358
  have hstable : (prefixWord ++ tailWord_1605358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605358).length < 2 ^ (prefixWord ++ tailWord_1605358).sum := by decide
  have hdescent : baseEnd_1605358 < baseStart_1605358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605361 : List Nat := [1, 2, 2, 2, 2, 3, 1, 3, 1, 2, 4]
def baseStart_1605361 : Nat := 118140960795 + 1605361 * 2 ^ 59
def prefixEnd_1605361 : Nat := 4983230072969 + 3 ^ 40 * 1605361 * 2
def baseEnd_1605361 : Nat := 824321816982598751404585

theorem tailTrace_1605361 : CollatzResearch.WordTrace tailWord_1605361 prefixEnd_1605361 824321816982598751404585 := by
  unfold tailWord_1605361
  simp only [CollatzResearch.WordTrace]
  refine ⟨58552325937058745675815937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39034883958039163783877291 58552325937058745675815937)
  ·
    refine ⟨43914244452794059256861953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58552325937058745675815937 43914244452794059256861953)
    ·
      refine ⟨32935683339595544442646465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43914244452794059256861953 32935683339595544442646465)
      ·
        refine ⟨24701762504696658331984849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32935683339595544442646465 24701762504696658331984849)
        ·
          refine ⟨18526321878522493748988637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24701762504696658331984849 18526321878522493748988637)
          ·
            refine ⟨6947370704445935155870739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18526321878522493748988637 6947370704445935155870739)
            ·
              refine ⟨10421056056668902733806109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6947370704445935155870739 10421056056668902733806109)
              ·
                refine ⟨3907896021250838525177291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10421056056668902733806109 3907896021250838525177291)
                ·
                  refine ⟨5861844031876257787765937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3907896021250838525177291 5861844031876257787765937)
                  ·
                    refine ⟨4396383023907193340824453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5861844031876257787765937 4396383023907193340824453)
                    ·
                      refine ⟨824321816982598751404585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4396383023907193340824453 824321816982598751404585)
                      ·
                        rfl

theorem cell23_1605361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_1605361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605361 prefixEnd_1605361 := by exact prefixLift 1605361
  have htrace : WordTrace (prefixWord ++ tailWord_1605361) baseStart_1605361 baseEnd_1605361 := by
    simpa [prefixWord, tailWord_1605361, baseEnd_1605361] using wordTrace_append hprefix tailTrace_1605361
  have hstable : (prefixWord ++ tailWord_1605361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605361).length < 2 ^ (prefixWord ++ tailWord_1605361).sum := by decide
  have hdescent : baseEnd_1605361 < baseStart_1605361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605378 : List Nat := [3, 4, 1, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_1605378 : Nat := 118140960795 + 1605378 * 2 ^ 59
def prefixEnd_1605378 : Nat := 4983230072969 + 3 ^ 40 * 1605378 * 2
def baseEnd_1605378 : Nat := 824330546153725184892007

theorem tailTrace_1605378 : CollatzResearch.WordTrace tailWord_1605378 prefixEnd_1605378 824330546153725184892007 := by
  unfold tailWord_1605378
  simp only [CollatzResearch.WordTrace]
  refine ⟨14638236494499289394796197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39035297318664771719456525 14638236494499289394796197)
  ·
    refine ⟨2744669342718616761524287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14638236494499289394796197 2744669342718616761524287)
    ·
      refine ⟨4117004014077925142286431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2744669342718616761524287 4117004014077925142286431)
      ·
        refine ⟨6175506021116887713429647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4117004014077925142286431 6175506021116887713429647)
        ·
          refine ⟨9263259031675331570144471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6175506021116887713429647 9263259031675331570144471)
          ·
            refine ⟨13894888547512997355216707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9263259031675331570144471 13894888547512997355216707)
            ·
              refine ⟨20842332821269496032825061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13894888547512997355216707 20842332821269496032825061)
              ·
                refine ⟨3907937403988030506154699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20842332821269496032825061 3907937403988030506154699)
                ·
                  refine ⟨5861906105982045759232049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3907937403988030506154699 5861906105982045759232049)
                  ·
                    refine ⟨4396429579486534319424037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5861906105982045759232049 4396429579486534319424037)
                    ·
                      refine ⟨824330546153725184892007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4396429579486534319424037 824330546153725184892007)
                      ·
                        rfl

theorem cell23_1605378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_1605378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605378 prefixEnd_1605378 := by exact prefixLift 1605378
  have htrace : WordTrace (prefixWord ++ tailWord_1605378) baseStart_1605378 baseEnd_1605378 := by
    simpa [prefixWord, tailWord_1605378, baseEnd_1605378] using wordTrace_append hprefix tailTrace_1605378
  have hstable : (prefixWord ++ tailWord_1605378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605378).length < 2 ^ (prefixWord ++ tailWord_1605378).sum := by decide
  have hdescent : baseEnd_1605378 < baseStart_1605378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605422 : List Nat := [4, 1, 3, 2, 3, 1, 2, 7]
def baseStart_1605422 : Nat := 118140960795 + 1605422 * 2 ^ 59
def prefixEnd_1605422 : Nat := 4983230072969 + 3 ^ 40 * 1605422 * 2
def baseEnd_1605422 : Nat := 30531597751945296768215

theorem tailTrace_1605422 : CollatzResearch.WordTrace tailWord_1605422 prefixEnd_1605422 30531597751945296768215 := by
  unfold tailWord_1605422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7319318848729719136723315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39036367193225168729191013 7319318848729719136723315)
  ·
    refine ⟨10978978273094578705084973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7319318848729719136723315 10978978273094578705084973)
    ·
      refine ⟨4117116852410467014406865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10978978273094578705084973 4117116852410467014406865)
      ·
        refine ⟨3087837639307850260805149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4117116852410467014406865 3087837639307850260805149)
        ·
          refine ⟨1157939114740443847801931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3087837639307850260805149 1157939114740443847801931)
          ·
            refine ⟨1736908672110665771702897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157939114740443847801931 1736908672110665771702897)
            ·
              refine ⟨1302681504082999328777173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1736908672110665771702897 1302681504082999328777173)
              ·
                refine ⟨30531597751945296768215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1302681504082999328777173 30531597751945296768215)
                ·
                  rfl

theorem cell23_1605422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 7].length) (baseStart_1605422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605422 prefixEnd_1605422 := by exact prefixLift 1605422
  have htrace : WordTrace (prefixWord ++ tailWord_1605422) baseStart_1605422 baseEnd_1605422 := by
    simpa [prefixWord, tailWord_1605422, baseEnd_1605422] using wordTrace_append hprefix tailTrace_1605422
  have hstable : (prefixWord ++ tailWord_1605422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605422).length < 2 ^ (prefixWord ++ tailWord_1605422).sum := by decide
  have hdescent : baseEnd_1605422 < baseStart_1605422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605425 : List Nat := [1, 2, 2, 3, 2, 2, 1, 4, 1, 3, 2]
def baseStart_1605425 : Nat := 118140960795 + 1605425 * 2 ^ 59
def prefixEnd_1605425 : Nat := 4983230072969 + 3 ^ 40 * 1605425 * 2
def baseEnd_1605425 : Nat := 824354679744486501004291

theorem tailTrace_1605425 : CollatzResearch.WordTrace tailWord_1605425 prefixEnd_1605425 824354679744486501004291 := by
  unfold tailWord_1605425
  simp only [CollatzResearch.WordTrace]
  refine ⟨58554660208826884606145729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39036440139217923070763819 58554660208826884606145729)
  ·
    refine ⟨43915995156620163454609297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58554660208826884606145729 43915995156620163454609297)
    ·
      refine ⟨32936996367465122590956973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43915995156620163454609297 32936996367465122590956973)
      ·
        refine ⟨12351373637799420971608865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32936996367465122590956973 12351373637799420971608865)
        ·
          refine ⟨9263530228349565728706649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12351373637799420971608865 9263530228349565728706649)
          ·
            refine ⟨6947647671262174296529987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9263530228349565728706649 6947647671262174296529987)
            ·
              refine ⟨10421471506893261444794981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6947647671262174296529987 10421471506893261444794981)
              ·
                refine ⟨1954025907542486520899059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10421471506893261444794981 1954025907542486520899059)
                ·
                  refine ⟨2931038861313729781348589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1954025907542486520899059 2931038861313729781348589)
                  ·
                    refine ⟨1099139572992648668005721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2931038861313729781348589 1099139572992648668005721)
                    ·
                      refine ⟨824354679744486501004291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1099139572992648668005721 824354679744486501004291)
                      ·
                        rfl

theorem cell23_1605425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_1605425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605425 prefixEnd_1605425 := by exact prefixLift 1605425
  have htrace : WordTrace (prefixWord ++ tailWord_1605425) baseStart_1605425 baseEnd_1605425 := by
    simpa [prefixWord, tailWord_1605425, baseEnd_1605425] using wordTrace_append hprefix tailTrace_1605425
  have hstable : (prefixWord ++ tailWord_1605425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605425).length < 2 ^ (prefixWord ++ tailWord_1605425).sum := by decide
  have hdescent : baseEnd_1605425 < baseStart_1605425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605428 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_1605428 : Nat := 118140960795 + 1605428 * 2 ^ 59
def prefixEnd_1605428 : Nat := 4983230072969 + 3 ^ 40 * 1605428 * 2
def baseEnd_1605428 : Nat := 824356220186449989266777

theorem tailTrace_1605428 : CollatzResearch.WordTrace tailWord_1605428 prefixEnd_1605428 824356220186449989266777 := by
  unfold tailWord_1605428
  simp only [CollatzResearch.WordTrace]
  refine ⟨29277384813908008059252469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39036513085210677412336625 29277384813908008059252469)
  ·
    refine ⟨2744754826303875755554919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29277384813908008059252469 2744754826303875755554919)
    ·
      refine ⟨4117132239455813633332379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2744754826303875755554919 4117132239455813633332379)
      ·
        refine ⟨6175698359183720449998569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4117132239455813633332379 6175698359183720449998569)
        ·
          refine ⟨4631773769387790337498927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6175698359183720449998569 4631773769387790337498927)
          ·
            refine ⟨6947660654081685506248391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4631773769387790337498927 6947660654081685506248391)
            ·
              refine ⟨10421490981122528259372587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6947660654081685506248391 10421490981122528259372587)
              ·
                refine ⟨15632236471683792389058881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10421490981122528259372587 15632236471683792389058881)
                ·
                  refine ⟨11724177353762844291794161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15632236471683792389058881 11724177353762844291794161)
                  ·
                    refine ⟨8793133015322133218845621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11724177353762844291794161 8793133015322133218845621)
                    ·
                      refine ⟨824356220186449989266777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8793133015322133218845621 824356220186449989266777)
                      ·
                        rfl

theorem cell23_1605428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_1605428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605428 prefixEnd_1605428 := by exact prefixLift 1605428
  have htrace : WordTrace (prefixWord ++ tailWord_1605428) baseStart_1605428 baseEnd_1605428 := by
    simpa [prefixWord, tailWord_1605428, baseEnd_1605428] using wordTrace_append hprefix tailTrace_1605428
  have hstable : (prefixWord ++ tailWord_1605428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605428).length < 2 ^ (prefixWord ++ tailWord_1605428).sum := by decide
  have hdescent : baseEnd_1605428 < baseStart_1605428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605433 : List Nat := [1, 2, 1, 7, 2, 1, 1, 3, 1, 2, 2]
def baseStart_1605433 : Nat := 118140960795 + 1605433 * 2 ^ 59
def prefixEnd_1605433 : Nat := 4983230072969 + 3 ^ 40 * 1605433 * 2
def baseEnd_1605433 : Nat := 824358787589722469704255

theorem tailTrace_1605433 : CollatzResearch.WordTrace tailWord_1605433 prefixEnd_1605433 824358787589722469704255 := by
  unfold tailWord_1605433
  simp only [CollatzResearch.WordTrace]
  refine ⟨58554951992797901972436953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39036634661865267981624635 58554951992797901972436953)
  ·
    refine ⟨43916213994598426479327715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58554951992797901972436953 43916213994598426479327715)
    ·
      refine ⟨65874320991897639718991573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43916213994598426479327715 65874320991897639718991573)
      ·
        refine ⟨1543929398247600930913865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 65874320991897639718991573 1543929398247600930913865)
        ·
          refine ⟨1157947048685700698185399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1543929398247600930913865 1157947048685700698185399)
          ·
            refine ⟨1736920573028551047278099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157947048685700698185399 1736920573028551047278099)
            ·
              refine ⟨2605380859542826570917149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736920573028551047278099 2605380859542826570917149)
              ·
                refine ⟨977017822328559964093931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2605380859542826570917149 977017822328559964093931)
                ·
                  refine ⟨1465526733492839946140897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 977017822328559964093931 1465526733492839946140897)
                  ·
                    refine ⟨1099145050119629959605673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1465526733492839946140897 1099145050119629959605673)
                    ·
                      refine ⟨824358787589722469704255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1099145050119629959605673 824358787589722469704255)
                      ·
                        rfl

theorem cell23_1605433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_1605433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605433 prefixEnd_1605433 := by exact prefixLift 1605433
  have htrace : WordTrace (prefixWord ++ tailWord_1605433) baseStart_1605433 baseEnd_1605433 := by
    simpa [prefixWord, tailWord_1605433, baseEnd_1605433] using wordTrace_append hprefix tailTrace_1605433
  have hstable : (prefixWord ++ tailWord_1605433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605433).length < 2 ^ (prefixWord ++ tailWord_1605433).sum := by decide
  have hdescent : baseEnd_1605433 < baseStart_1605433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605472 : List Nat := [2, 1, 1, 3, 3, 3, 1, 3, 2, 2, 2]
def baseStart_1605472 : Nat := 118140960795 + 1605472 * 2 ^ 59
def prefixEnd_1605472 : Nat := 4983230072969 + 3 ^ 40 * 1605472 * 2
def baseEnd_1605472 : Nat := 824378813335247817116575

theorem tailTrace_1605472 : CollatzResearch.WordTrace tailWord_1605472 prefixEnd_1605472 824378813335247817116575 := by
  unfold tailWord_1605472
  simp only [CollatzResearch.WordTrace]
  refine ⟨29278187219828305816553335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39037582959771074422071113 29278187219828305816553335)
  ·
    refine ⟨43917280829742458724830003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29278187219828305816553335 43917280829742458724830003)
    ·
      refine ⟨65875921244613688087245005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43917280829742458724830003 65875921244613688087245005)
      ·
        refine ⟨24703470466730133032716877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65875921244613688087245005 24703470466730133032716877)
        ·
          refine ⟨9263801425023799887268829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24703470466730133032716877 9263801425023799887268829)
          ·
            refine ⟨3473925534383924957725811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9263801425023799887268829 3473925534383924957725811)
            ·
              refine ⟨5210888301575887436588717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3473925534383924957725811 5210888301575887436588717)
              ·
                refine ⟨1954083113090957788720769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5210888301575887436588717 1954083113090957788720769)
                ·
                  refine ⟨1465562334818218341540577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1954083113090957788720769 1465562334818218341540577)
                  ·
                    refine ⟨1099171751113663756155433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1465562334818218341540577 1099171751113663756155433)
                    ·
                      refine ⟨824378813335247817116575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1099171751113663756155433 824378813335247817116575)
                      ·
                        rfl

theorem cell23_1605472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_1605472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605472 prefixEnd_1605472 := by exact prefixLift 1605472
  have htrace : WordTrace (prefixWord ++ tailWord_1605472) baseStart_1605472 baseEnd_1605472 := by
    simpa [prefixWord, tailWord_1605472, baseEnd_1605472] using wordTrace_append hprefix tailTrace_1605472
  have hstable : (prefixWord ++ tailWord_1605472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605472).length < 2 ^ (prefixWord ++ tailWord_1605472).sum := by decide
  have hdescent : baseEnd_1605472 < baseStart_1605472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605508 : List Nat := [2, 3, 2, 1, 1, 1, 4, 2, 2, 5]
def baseStart_1605508 : Nat := 118140960795 + 1605508 * 2 ^ 59
def prefixEnd_1605508 : Nat := 4983230072969 + 3 ^ 40 * 1605508 * 2
def baseEnd_1605508 : Nat := 274799099546269892088803

theorem tailTrace_1605508 : CollatzResearch.WordTrace tailWord_1605508 prefixEnd_1605508 274799099546269892088803 := by
  unfold tailWord_1605508
  simp only [CollatzResearch.WordTrace]
  refine ⟨29278843733763094890708589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39038458311684126520944785 29278843733763094890708589)
  ·
    refine ⟨10979566400161160584015721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29278843733763094890708589 10979566400161160584015721)
    ·
      refine ⟨8234674800120870438011791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10979566400161160584015721 8234674800120870438011791)
      ·
        refine ⟨12352012200181305657017687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8234674800120870438011791 12352012200181305657017687)
        ·
          refine ⟨18528018300271958485526531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12352012200181305657017687 18528018300271958485526531)
          ·
            refine ⟨27792027450407937728289797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18528018300271958485526531 27792027450407937728289797)
            ·
              refine ⟨5211005146951488324054337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27792027450407937728289797 5211005146951488324054337)
              ·
                refine ⟨3908253860213616243040753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5211005146951488324054337 3908253860213616243040753)
                ·
                  refine ⟨2931190395160212182280565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3908253860213616243040753 2931190395160212182280565)
                  ·
                    refine ⟨274799099546269892088803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2931190395160212182280565 274799099546269892088803)
                    ·
                      rfl

theorem cell23_1605508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_1605508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605508 prefixEnd_1605508 := by exact prefixLift 1605508
  have htrace : WordTrace (prefixWord ++ tailWord_1605508) baseStart_1605508 baseEnd_1605508 := by
    simpa [prefixWord, tailWord_1605508, baseEnd_1605508] using wordTrace_append hprefix tailTrace_1605508
  have hstable : (prefixWord ++ tailWord_1605508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605508).length < 2 ^ (prefixWord ++ tailWord_1605508).sum := by decide
  have hdescent : baseEnd_1605508 < baseStart_1605508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605541 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 4, 1, 6]
def baseStart_1605541 : Nat := 118140960795 + 1605541 * 2 ^ 59
def prefixEnd_1605541 : Nat := 4983230072969 + 3 ^ 40 * 1605541 * 2
def baseEnd_1605541 : Nat := 824414243500408047153757

theorem tailTrace_1605541 : CollatzResearch.WordTrace tailWord_1605541 prefixEnd_1605541 824414243500408047153757 := by
  unfold tailWord_1605541
  simp only [CollatzResearch.WordTrace]
  refine ⟨58558891076406636417368477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39039260717604424278245651 58558891076406636417368477)
  ·
    refine ⟨21959584153652488656513179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58558891076406636417368477 21959584153652488656513179)
    ·
      refine ⟨32939376230478732984769769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21959584153652488656513179 32939376230478732984769769)
      ·
        refine ⟨24704532172859049738577327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32939376230478732984769769 24704532172859049738577327)
        ·
          refine ⟨37056798259288574607865991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24704532172859049738577327 37056798259288574607865991)
          ·
            refine ⟨55585197388932861911798987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37056798259288574607865991 55585197388932861911798987)
            ·
              refine ⟨83377796083399292867698481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55585197388932861911798987 83377796083399292867698481)
              ·
                refine ⟨62533347062549469650773861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83377796083399292867698481 62533347062549469650773861)
                ·
                  refine ⟨11725002574228025559520099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62533347062549469650773861 11725002574228025559520099)
                  ·
                    refine ⟨17587503861342038339280149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11725002574228025559520099 17587503861342038339280149)
                    ·
                      refine ⟨824414243500408047153757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17587503861342038339280149 824414243500408047153757)
                      ·
                        rfl

theorem cell23_1605541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_1605541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605541 prefixEnd_1605541 := by exact prefixLift 1605541
  have htrace : WordTrace (prefixWord ++ tailWord_1605541) baseStart_1605541 baseEnd_1605541 := by
    simpa [prefixWord, tailWord_1605541, baseEnd_1605541] using wordTrace_append hprefix tailTrace_1605541
  have hstable : (prefixWord ++ tailWord_1605541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605541).length < 2 ^ (prefixWord ++ tailWord_1605541).sum := by decide
  have hdescent : baseEnd_1605541 < baseStart_1605541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605551 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 8]
def baseStart_1605551 : Nat := 118140960795 + 1605551 * 2 ^ 59
def prefixEnd_1605551 : Nat := 4983230072969 + 3 ^ 40 * 1605551 * 2
def baseEnd_1605551 : Nat := 91602153145217000892079

theorem tailTrace_1605551 : CollatzResearch.WordTrace tailWord_1605551 prefixEnd_1605551 91602153145217000892079 := by
  unfold tailWord_1605551
  simp only [CollatzResearch.WordTrace]
  refine ⟨58559255806370408125232507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39039503870913605416821671 58559255806370408125232507)
  ·
    refine ⟨87838883709555612187848761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58559255806370408125232507 87838883709555612187848761)
    ·
      refine ⟨65879162782166709140886571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87838883709555612187848761 65879162782166709140886571)
      ·
        refine ⟨98818744173250063711329857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65879162782166709140886571 98818744173250063711329857)
        ·
          refine ⟨74114058129937547783497393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98818744173250063711329857 74114058129937547783497393)
          ·
            refine ⟨55585543597453160837623045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74114058129937547783497393 55585543597453160837623045)
            ·
              refine ⟨10422289424522467657054321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55585543597453160837623045 10422289424522467657054321)
              ·
                refine ⟨7816717068391850742790741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10422289424522467657054321 7816717068391850742790741)
                ·
                  refine ⟨91602153145217000892079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7816717068391850742790741 91602153145217000892079)
                  ·
                    rfl

theorem cell23_1605551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 8].length) (baseStart_1605551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605551 prefixEnd_1605551 := by exact prefixLift 1605551
  have htrace : WordTrace (prefixWord ++ tailWord_1605551) baseStart_1605551 baseEnd_1605551 := by
    simpa [prefixWord, tailWord_1605551, baseEnd_1605551] using wordTrace_append hprefix tailTrace_1605551
  have hstable : (prefixWord ++ tailWord_1605551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605551).length < 2 ^ (prefixWord ++ tailWord_1605551).sum := by decide
  have hdescent : baseEnd_1605551 < baseStart_1605551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605588 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1605588 : Nat := 118140960795 + 1605588 * 2 ^ 59
def prefixEnd_1605588 : Nat := 4983230072969 + 3 ^ 40 * 1605588 * 2
def baseEnd_1605588 : Nat := 824438377091169363266041

theorem tailTrace_1605588 : CollatzResearch.WordTrace tailWord_1605588 prefixEnd_1605588 824438377091169363266041 := by
  unfold tailWord_1605588
  simp only [CollatzResearch.WordTrace]
  refine ⟨29280302653618181722164709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39040403538157575629552945 29280302653618181722164709)
  ·
    refine ⟨5490056747553409072905883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29280302653618181722164709 5490056747553409072905883)
    ·
      refine ⟨8235085121330113609358825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5490056747553409072905883 8235085121330113609358825)
      ·
        refine ⟨6176313840997585207019119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8235085121330113609358825 6176313840997585207019119)
        ·
          refine ⟨9264470761496377810528679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6176313840997585207019119 9264470761496377810528679)
          ·
            refine ⟨13896706142244566715793019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9264470761496377810528679 13896706142244566715793019)
            ·
              refine ⟨20845059213366850073689529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13896706142244566715793019 20845059213366850073689529)
              ·
                refine ⟨15633794410025137555267147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20845059213366850073689529 15633794410025137555267147)
                ·
                  refine ⟨23450691615037706332900721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15633794410025137555267147 23450691615037706332900721)
                  ·
                    refine ⟨17588018711278279749675541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23450691615037706332900721 17588018711278279749675541)
                    ·
                      refine ⟨824438377091169363266041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17588018711278279749675541 824438377091169363266041)
                      ·
                        rfl

theorem cell23_1605588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1605588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605588 prefixEnd_1605588 := by exact prefixLift 1605588
  have htrace : WordTrace (prefixWord ++ tailWord_1605588) baseStart_1605588 baseEnd_1605588 := by
    simpa [prefixWord, tailWord_1605588, baseEnd_1605588] using wordTrace_append hprefix tailTrace_1605588
  have hstable : (prefixWord ++ tailWord_1605588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605588).length < 2 ^ (prefixWord ++ tailWord_1605588).sum := by decide
  have hdescent : baseEnd_1605588 < baseStart_1605588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605636 : List Nat := [2, 3, 2, 4, 2, 1, 2, 1, 6]
def baseStart_1605636 : Nat := 118140960795 + 1605636 * 2 ^ 59
def prefixEnd_1605636 : Nat := 4983230072969 + 3 ^ 40 * 1605636 * 2
def baseEnd_1605636 : Nat := 91607002684731686162869

theorem tailTrace_1605636 : CollatzResearch.WordTrace tailWord_1605636 prefixEnd_1605636 91607002684731686162869 := by
  unfold tailWord_1605636
  simp only [CollatzResearch.WordTrace]
  refine ⟨29281178005531233821038381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39041570674041645094717841 29281178005531233821038381)
  ·
    refine ⟨10980441752074212682889393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29281178005531233821038381 10980441752074212682889393)
    ·
      refine ⟨8235331314055659512167045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10980441752074212682889393 8235331314055659512167045)
      ·
        refine ⟨1544124621385436158531321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8235331314055659512167045 1544124621385436158531321)
        ·
          refine ⟨1158093466039077118898491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1544124621385436158531321 1158093466039077118898491)
          ·
            refine ⟨1737140199058615678347737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158093466039077118898491 1737140199058615678347737)
            ·
              refine ⟨1302855149293961758760803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1737140199058615678347737 1302855149293961758760803)
              ·
                refine ⟨1954282723940942638141205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1302855149293961758760803 1954282723940942638141205)
                ·
                  refine ⟨91607002684731686162869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1954282723940942638141205 91607002684731686162869)
                  ·
                    rfl

theorem cell23_1605636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_1605636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605636 prefixEnd_1605636 := by exact prefixLift 1605636
  have htrace : WordTrace (prefixWord ++ tailWord_1605636) baseStart_1605636 baseEnd_1605636 := by
    simpa [prefixWord, tailWord_1605636, baseEnd_1605636] using wordTrace_append hprefix tailTrace_1605636
  have hstable : (prefixWord ++ tailWord_1605636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605636).length < 2 ^ (prefixWord ++ tailWord_1605636).sum := by decide
  have hdescent : baseEnd_1605636 < baseStart_1605636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605658 : List Nat := [3, 1, 1, 3, 1, 3, 2, 9]
def baseStart_1605658 : Nat := 118140960795 + 1605658 * 2 ^ 59
def prefixEnd_1605658 : Nat := 4983230072969 + 3 ^ 40 * 1605658 * 2
def baseEnd_1605658 : Nat := 30536085953221632940397

theorem tailTrace_1605658 : CollatzResearch.WordTrace tailWord_1605658 prefixEnd_1605658 30536085953221632940397 := by
  unfold tailWord_1605658
  simp only [CollatzResearch.WordTrace]
  refine ⟨14640789604245691349844407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39042105611321843599585085 14640789604245691349844407)
  ·
    refine ⟨21961184406368537024766611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14640789604245691349844407 21961184406368537024766611)
    ·
      refine ⟨32941776609552805537149917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21961184406368537024766611 32941776609552805537149917)
      ·
        refine ⟨12353166228582302076431219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32941776609552805537149917 12353166228582302076431219)
        ·
          refine ⟨18529749342873453114646829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12353166228582302076431219 18529749342873453114646829)
          ·
            refine ⟨6948656003577544917992561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18529749342873453114646829 6948656003577544917992561)
            ·
              refine ⟨5211492002683158688494421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6948656003577544917992561 5211492002683158688494421)
              ·
                refine ⟨30536085953221632940397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5211492002683158688494421 30536085953221632940397)
                ·
                  rfl

theorem cell23_1605658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 9].length) (baseStart_1605658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605658 prefixEnd_1605658 := by exact prefixLift 1605658
  have htrace : WordTrace (prefixWord ++ tailWord_1605658) baseStart_1605658 baseEnd_1605658 := by
    simpa [prefixWord, tailWord_1605658, baseEnd_1605658] using wordTrace_append hprefix tailTrace_1605658
  have hstable : (prefixWord ++ tailWord_1605658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605658).length < 2 ^ (prefixWord ++ tailWord_1605658).sum := by decide
  have hdescent : baseEnd_1605658 < baseStart_1605658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605765 : List Nat := [1, 3, 1, 1, 5, 1, 2, 2, 7]
def baseStart_1605765 : Nat := 118140960795 + 1605765 * 2 ^ 59
def prefixEnd_1605765 : Nat := 4983230072969 + 3 ^ 40 * 1605765 * 2
def baseEnd_1605765 : Nat := 91614362574112796750303

theorem tailTrace_1605765 : CollatzResearch.WordTrace tailWord_1605765 prefixEnd_1605765 91614362574112796750303 := by
  unfold tailWord_1605765
  simp only [CollatzResearch.WordTrace]
  refine ⟨58567061027595122673522749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39044707351730081782348499 58567061027595122673522749)
  ·
    refine ⟨21962647885348171002571031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58567061027595122673522749 21962647885348171002571031)
    ·
      refine ⟨32943971828022256503856547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21962647885348171002571031 32943971828022256503856547)
      ·
        refine ⟨49415957742033384755784821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32943971828022256503856547 49415957742033384755784821)
        ·
          refine ⟨4632746038315629820854827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49415957742033384755784821 4632746038315629820854827)
          ·
            refine ⟨6949119057473444731282241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4632746038315629820854827 6949119057473444731282241)
            ·
              refine ⟨5211839293105083548461681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6949119057473444731282241 5211839293105083548461681)
              ·
                refine ⟨3908879469828812661346261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5211839293105083548461681 3908879469828812661346261)
                ·
                  refine ⟨91614362574112796750303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3908879469828812661346261 91614362574112796750303)
                  ·
                    rfl

theorem cell23_1605765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 7].length) (baseStart_1605765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605765 prefixEnd_1605765 := by exact prefixLift 1605765
  have htrace : WordTrace (prefixWord ++ tailWord_1605765) baseStart_1605765 baseEnd_1605765 := by
    simpa [prefixWord, tailWord_1605765, baseEnd_1605765] using wordTrace_append hprefix tailTrace_1605765
  have hstable : (prefixWord ++ tailWord_1605765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605765).length < 2 ^ (prefixWord ++ tailWord_1605765).sum := by decide
  have hdescent : baseEnd_1605765 < baseStart_1605765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605799 : List Nat := [1, 1, 6, 2, 2, 2, 1, 1, 7]
def baseStart_1605799 : Nat := 118140960795 + 1605799 * 2 ^ 59
def prefixEnd_1605799 : Nat := 4983230072969 + 3 ^ 40 * 1605799 * 2
def baseEnd_1605799 : Nat := 91616302389918670858619

theorem tailTrace_1605799 : CollatzResearch.WordTrace tailWord_1605799 prefixEnd_1605799 91616302389918670858619 := by
  unfold tailWord_1605799
  simp only [CollatzResearch.WordTrace]
  refine ⟨58568301109471946480260451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39045534072981297653506967 58568301109471946480260451)
  ·
    refine ⟨87852451664207919720390677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58568301109471946480260451 87852451664207919720390677)
    ·
      refine ⟨4118083671759746236893313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87852451664207919720390677 4118083671759746236893313)
      ·
        refine ⟨3088562753819809677669985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4118083671759746236893313 3088562753819809677669985)
        ·
          refine ⟨2316422065364857258252489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3088562753819809677669985 2316422065364857258252489)
          ·
            refine ⟨1737316549023642943689367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2316422065364857258252489 1737316549023642943689367)
            ·
              refine ⟨2605974823535464415534051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1737316549023642943689367 2605974823535464415534051)
              ·
                refine ⟨3908962235303196623301077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2605974823535464415534051 3908962235303196623301077)
                ·
                  refine ⟨91616302389918670858619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3908962235303196623301077 91616302389918670858619)
                  ·
                    rfl

theorem cell23_1605799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 7].length) (baseStart_1605799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605799 prefixEnd_1605799 := by exact prefixLift 1605799
  have htrace : WordTrace (prefixWord ++ tailWord_1605799) baseStart_1605799 baseEnd_1605799 := by
    simpa [prefixWord, tailWord_1605799, baseEnd_1605799] using wordTrace_append hprefix tailTrace_1605799
  have hstable : (prefixWord ++ tailWord_1605799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605799).length < 2 ^ (prefixWord ++ tailWord_1605799).sum := by decide
  have hdescent : baseEnd_1605799 < baseStart_1605799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605832 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 4, 4, 2]
def baseStart_1605832 : Nat := 118140960795 + 1605832 * 2 ^ 59
def prefixEnd_1605832 : Nat := 4983230072969 + 3 ^ 40 * 1605832 * 2
def baseEnd_1605832 : Nat := 824563666370866408614919

theorem tailTrace_1605832 : CollatzResearch.WordTrace tailWord_1605832 prefixEnd_1605832 824563666370866408614919 := by
  unfold tailWord_1605832
  simp only [CollatzResearch.WordTrace]
  refine ⟨29284752359176196558105875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39046336478901595410807833 29284752359176196558105875)
  ·
    refine ⟨43927128538764294837158813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29284752359176196558105875 43927128538764294837158813)
    ·
      refine ⟨16472673202036610563934555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43927128538764294837158813 16472673202036610563934555)
      ·
        refine ⟨24709009803054915845901833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16472673202036610563934555 24709009803054915845901833)
        ·
          refine ⟨18531757352291186884426375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24709009803054915845901833 18531757352291186884426375)
          ·
            refine ⟨27797636028436780326639563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18531757352291186884426375 27797636028436780326639563)
            ·
              refine ⟨41696454042655170489959345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27797636028436780326639563 41696454042655170489959345)
              ·
                refine ⟨31272340531991377867469509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41696454042655170489959345 31272340531991377867469509)
                ·
                  refine ⟨5863563849748383350150533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31272340531991377867469509 5863563849748383350150533)
                  ·
                    refine ⟨1099418221827821878153225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5863563849748383350150533 1099418221827821878153225)
                    ·
                      refine ⟨824563666370866408614919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1099418221827821878153225 824563666370866408614919)
                      ·
                        rfl

theorem cell23_1605832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_1605832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605832 prefixEnd_1605832 := by exact prefixLift 1605832
  have htrace : WordTrace (prefixWord ++ tailWord_1605832) baseStart_1605832 baseEnd_1605832 := by
    simpa [prefixWord, tailWord_1605832, baseEnd_1605832] using wordTrace_append hprefix tailTrace_1605832
  have hstable : (prefixWord ++ tailWord_1605832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605832).length < 2 ^ (prefixWord ++ tailWord_1605832).sum := by decide
  have hdescent : baseEnd_1605832 < baseStart_1605832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605909 : List Nat := [1, 3, 2, 1, 2, 1, 2, 4, 2, 3, 2]
def baseStart_1605909 : Nat := 118140960795 + 1605909 * 2 ^ 59
def prefixEnd_1605909 : Nat := 4983230072969 + 3 ^ 40 * 1605909 * 2
def baseEnd_1605909 : Nat := 824603204381262607352065

theorem tailTrace_1605909 : CollatzResearch.WordTrace tailWord_1605909 prefixEnd_1605909 824603204381262607352065 := by
  unfold tailWord_1605909
  simp only [CollatzResearch.WordTrace]
  refine ⟨58572313139073435266764781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39048208759382290177843187 58572313139073435266764781)
  ·
    refine ⟨21964617427152538225036793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58572313139073435266764781 21964617427152538225036793)
    ·
      refine ⟨16473463070364403668777595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21964617427152538225036793 16473463070364403668777595)
      ·
        refine ⟨24710194605546605503166393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16473463070364403668777595 24710194605546605503166393)
        ·
          refine ⟨18532645954159954127374795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24710194605546605503166393 18532645954159954127374795)
          ·
            refine ⟨27798968931239931191062193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18532645954159954127374795 27798968931239931191062193)
            ·
              refine ⟨20849226698429948393296645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27798968931239931191062193 20849226698429948393296645)
              ·
                refine ⟨3909230005955615323743121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20849226698429948393296645 3909230005955615323743121)
                ·
                  refine ⟨2931922504466711492807341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3909230005955615323743121 2931922504466711492807341)
                  ·
                    refine ⟨1099470939175016809802753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2931922504466711492807341 1099470939175016809802753)
                    ·
                      refine ⟨824603204381262607352065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1099470939175016809802753 824603204381262607352065)
                      ·
                        rfl

theorem cell23_1605909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_1605909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605909 prefixEnd_1605909 := by exact prefixLift 1605909
  have htrace : WordTrace (prefixWord ++ tailWord_1605909) baseStart_1605909 baseEnd_1605909 := by
    simpa [prefixWord, tailWord_1605909, baseEnd_1605909] using wordTrace_append hprefix tailTrace_1605909
  have hstable : (prefixWord ++ tailWord_1605909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605909).length < 2 ^ (prefixWord ++ tailWord_1605909).sum := by decide
  have hdescent : baseEnd_1605909 < baseStart_1605909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605915 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 3, 6]
def baseStart_1605915 : Nat := 118140960795 + 1605915 * 2 ^ 59
def prefixEnd_1605915 : Nat := 4983230072969 + 3 ^ 40 * 1605915 * 2
def baseEnd_1605915 : Nat := 274868761755063194625679

theorem tailTrace_1605915 : CollatzResearch.WordTrace tailWord_1605915 prefixEnd_1605915 274868761755063194625679 := by
  unfold tailWord_1605915
  simp only [CollatzResearch.WordTrace]
  refine ⟨58572531977051698291483199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39048354651367798860988799 58572531977051698291483199)
  ·
    refine ⟨87858797965577547437224799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58572531977051698291483199 87858797965577547437224799)
    ·
      refine ⟨131788196948366321155837199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87858797965577547437224799 131788196948366321155837199)
      ·
        refine ⟨197682295422549481733755799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131788196948366321155837199 197682295422549481733755799)
        ·
          refine ⟨296523443133824222600633699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197682295422549481733755799 296523443133824222600633699)
          ·
            refine ⟨444785164700736333900950549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296523443133824222600633699 444785164700736333900950549)
            ·
              refine ⟨20849304595347015651607057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 444785164700736333900950549 20849304595347015651607057)
              ·
                refine ⟨15636978446510261738705293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20849304595347015651607057 15636978446510261738705293)
                ·
                  refine ⟨5863866917441348152014485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15636978446510261738705293 5863866917441348152014485)
                  ·
                    refine ⟨274868761755063194625679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5863866917441348152014485 274868761755063194625679)
                    ·
                      rfl

theorem cell23_1605915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 6].length) (baseStart_1605915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605915 prefixEnd_1605915 := by exact prefixLift 1605915
  have htrace : WordTrace (prefixWord ++ tailWord_1605915) baseStart_1605915 baseEnd_1605915 := by
    simpa [prefixWord, tailWord_1605915, baseEnd_1605915] using wordTrace_append hprefix tailTrace_1605915
  have hstable : (prefixWord ++ tailWord_1605915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605915).length < 2 ^ (prefixWord ++ tailWord_1605915).sum := by decide
  have hdescent : baseEnd_1605915 < baseStart_1605915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605932 : List Nat := [2, 2, 1, 1, 1, 3, 5, 1, 1, 6]
def baseStart_1605932 : Nat := 118140960795 + 1605932 * 2 ^ 59
def prefixEnd_1605932 : Nat := 4983230072969 + 3 ^ 40 * 1605932 * 2
def baseEnd_1605932 : Nat := 274871671478772005788153

theorem tailTrace_1605932 : CollatzResearch.WordTrace tailWord_1605932 prefixEnd_1605932 274871671478772005788153 := by
  unfold tailWord_1605932
  simp only [CollatzResearch.WordTrace]
  refine ⟨29286576008995055097426025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39048768011993406796568033 29286576008995055097426025)
  ·
    refine ⟨21964932006746291323069519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29286576008995055097426025 21964932006746291323069519)
    ·
      refine ⟨32947398010119436984604279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21964932006746291323069519 32947398010119436984604279)
      ·
        refine ⟨49421097015179155476906419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32947398010119436984604279 49421097015179155476906419)
        ·
          refine ⟨74131645522768733215359629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49421097015179155476906419 74131645522768733215359629)
          ·
            refine ⟨27799367071038274955759861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74131645522768733215359629 27799367071038274955759861)
            ·
              refine ⟨2606190662909838277102487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27799367071038274955759861 2606190662909838277102487)
              ·
                refine ⟨3909285994364757415653731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2606190662909838277102487 3909285994364757415653731)
                ·
                  refine ⟨5863928991547136123480597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3909285994364757415653731 5863928991547136123480597)
                  ·
                    refine ⟨274871671478772005788153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5863928991547136123480597 274871671478772005788153)
                    ·
                      rfl

theorem cell23_1605932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 6].length) (baseStart_1605932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605932 prefixEnd_1605932 := by exact prefixLift 1605932
  have htrace : WordTrace (prefixWord ++ tailWord_1605932) baseStart_1605932 baseEnd_1605932 := by
    simpa [prefixWord, tailWord_1605932, baseEnd_1605932] using wordTrace_append hprefix tailTrace_1605932
  have hstable : (prefixWord ++ tailWord_1605932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605932).length < 2 ^ (prefixWord ++ tailWord_1605932).sum := by decide
  have hdescent : baseEnd_1605932 < baseStart_1605932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605939 : List Nat := [1, 1, 1, 2, 5, 1, 4, 2, 1, 1, 4]
def baseStart_1605939 : Nat := 118140960795 + 1605939 * 2 ^ 59
def prefixEnd_1605939 : Nat := 4983230072969 + 3 ^ 40 * 1605939 * 2
def baseEnd_1605939 : Nat := 824618608800897489976927

theorem tailTrace_1605939 : CollatzResearch.WordTrace tailWord_1605939 prefixEnd_1605939 824618608800897489976927 := by
  unfold tailWord_1605939
  simp only [CollatzResearch.WordTrace]
  refine ⟨58573407328964750390356871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39048938219309833593571247 58573407328964750390356871)
  ·
    refine ⟨87860110993447125585535307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58573407328964750390356871 87860110993447125585535307)
    ·
      refine ⟨131790166490170688378302961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87860110993447125585535307 131790166490170688378302961)
      ·
        refine ⟨98842624867628016283727221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131790166490170688378302961 98842624867628016283727221)
        ·
          refine ⟨9266496081340126526599427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98842624867628016283727221 9266496081340126526599427)
          ·
            refine ⟨13899744122010189789899141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9266496081340126526599427 13899744122010189789899141)
            ·
              refine ⟨2606202022876910585606089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13899744122010189789899141 2606202022876910585606089)
              ·
                refine ⟨1954651517157682939204567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2606202022876910585606089 1954651517157682939204567)
                ·
                  refine ⟨2931977275736524408806851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1954651517157682939204567 2931977275736524408806851)
                  ·
                    refine ⟨4397965913604786613210277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2931977275736524408806851 4397965913604786613210277)
                    ·
                      refine ⟨824618608800897489976927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4397965913604786613210277 824618608800897489976927)
                      ·
                        rfl

theorem cell23_1605939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 1, 4].length) (baseStart_1605939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605939 prefixEnd_1605939 := by exact prefixLift 1605939
  have htrace : WordTrace (prefixWord ++ tailWord_1605939) baseStart_1605939 baseEnd_1605939 := by
    simpa [prefixWord, tailWord_1605939, baseEnd_1605939] using wordTrace_append hprefix tailTrace_1605939
  have hstable : (prefixWord ++ tailWord_1605939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605939).length < 2 ^ (prefixWord ++ tailWord_1605939).sum := by decide
  have hdescent : baseEnd_1605939 < baseStart_1605939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605950 : List Nat := [4, 2, 1, 2, 1, 4, 1, 3, 1, 1, 3]
def baseStart_1605950 : Nat := 118140960795 + 1605950 * 2 ^ 59
def prefixEnd_1605950 : Nat := 4983230072969 + 3 ^ 40 * 1605950 * 2
def baseEnd_1605950 : Nat := 824624257088096946939377

theorem tailTrace_1605950 : CollatzResearch.WordTrace tailWord_1605950 prefixEnd_1605950 824624257088096946939377 := by
  unfold tailWord_1605950
  simp only [CollatzResearch.WordTrace]
  refine ⟨7321726066490612408625913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39049205687949932846004869 7321726066490612408625913)
  ·
    refine ⟨5491294549867959306469435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7321726066490612408625913 5491294549867959306469435)
    ·
      refine ⟨8236941824801938959704153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5491294549867959306469435 8236941824801938959704153)
      ·
        refine ⟨6177706368601454219778115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8236941824801938959704153 6177706368601454219778115)
        ·
          refine ⟨9266559552902181329667173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6177706368601454219778115 9266559552902181329667173)
          ·
            refine ⟨1737479916169158999312595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9266559552902181329667173 1737479916169158999312595)
            ·
              refine ⟨2606219874253738498968893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1737479916169158999312595 2606219874253738498968893)
              ·
                refine ⟨977332452845151937113335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2606219874253738498968893 977332452845151937113335)
                ·
                  refine ⟨1465998679267727905670003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 977332452845151937113335 1465998679267727905670003)
                  ·
                    refine ⟨2198998018901591858505005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1465998679267727905670003 2198998018901591858505005)
                    ·
                      refine ⟨824624257088096946939377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2198998018901591858505005 824624257088096946939377)
                      ·
                        rfl

theorem cell23_1605950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_1605950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605950 prefixEnd_1605950 := by exact prefixLift 1605950
  have htrace : WordTrace (prefixWord ++ tailWord_1605950) baseStart_1605950 baseEnd_1605950 := by
    simpa [prefixWord, tailWord_1605950, baseEnd_1605950] using wordTrace_append hprefix tailTrace_1605950
  have hstable : (prefixWord ++ tailWord_1605950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605950).length < 2 ^ (prefixWord ++ tailWord_1605950).sum := by decide
  have hdescent : baseEnd_1605950 < baseStart_1605950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605959 : List Nat := [1, 1, 4, 1, 2, 2, 1, 5, 1, 2, 3]
def baseStart_1605959 : Nat := 118140960795 + 1605959 * 2 ^ 59
def prefixEnd_1605959 : Nat := 4983230072969 + 3 ^ 40 * 1605959 * 2
def baseEnd_1605959 : Nat := 824628878413987411726835

theorem tailTrace_1605959 : CollatzResearch.WordTrace tailWord_1605959 prefixEnd_1605959 824628878413987411726835 := by
  unfold tailWord_1605959
  simp only [CollatzResearch.WordTrace]
  refine ⟨58574136788892293806084931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39049424525928195870723287 58574136788892293806084931)
  ·
    refine ⟨87861205183338440709127397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58574136788892293806084931 87861205183338440709127397)
    ·
      refine ⟨16473975971875957632961387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87861205183338440709127397 16473975971875957632961387)
      ·
        refine ⟨24710963957813936449442081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16473975971875957632961387 24710963957813936449442081)
        ·
          refine ⟨18533222968360452337081561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24710963957813936449442081 18533222968360452337081561)
          ·
            refine ⟨13899917226270339252811171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18533222968360452337081561 13899917226270339252811171)
            ·
              refine ⟨20849875839405508879216757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13899917226270339252811171 20849875839405508879216757)
              ·
                refine ⟨1954675859944266457426571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20849875839405508879216757 1954675859944266457426571)
                ·
                  refine ⟨2932013789916399686139857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1954675859944266457426571 2932013789916399686139857)
                  ·
                    refine ⟨2199010342437299764604893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2932013789916399686139857 2199010342437299764604893)
                    ·
                      refine ⟨824628878413987411726835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2199010342437299764604893 824628878413987411726835)
                      ·
                        rfl

theorem cell23_1605959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_1605959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1605959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1605959 prefixEnd_1605959 := by exact prefixLift 1605959
  have htrace : WordTrace (prefixWord ++ tailWord_1605959) baseStart_1605959 baseEnd_1605959 := by
    simpa [prefixWord, tailWord_1605959, baseEnd_1605959] using wordTrace_append hprefix tailTrace_1605959
  have hstable : (prefixWord ++ tailWord_1605959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605959).length < 2 ^ (prefixWord ++ tailWord_1605959).sum := by decide
  have hdescent : baseEnd_1605959 < baseStart_1605959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606052 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 9]
def baseStart_1606052 : Nat := 118140960795 + 1606052 * 2 ^ 59
def prefixEnd_1606052 : Nat := 4983230072969 + 3 ^ 40 * 1606052 * 2
def baseEnd_1606052 : Nat := 91630736901650616429323

theorem tailTrace_1606052 : CollatzResearch.WordTrace tailWord_1606052 prefixEnd_1606052 91630736901650616429323 := by
  unfold tailWord_1606052
  simp only [CollatzResearch.WordTrace]
  refine ⟨29288764388777685344610205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39051685851703580459480273 29288764388777685344610205)
  ·
    refine ⟨10983286645791632004228827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29288764388777685344610205 10983286645791632004228827)
    ·
      refine ⟨16474929968687448006343241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10983286645791632004228827 16474929968687448006343241)
      ·
        refine ⟨12356197476515586004757431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16474929968687448006343241 12356197476515586004757431)
        ·
          refine ⟨18534296214773379007136147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12356197476515586004757431 18534296214773379007136147)
          ·
            refine ⟨27801444322160068510704221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18534296214773379007136147 27801444322160068510704221)
            ·
              refine ⟨10425541620810025691514083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27801444322160068510704221 10425541620810025691514083)
              ·
                refine ⟨15638312431215038537271125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10425541620810025691514083 15638312431215038537271125)
                ·
                  refine ⟨91630736901650616429323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15638312431215038537271125 91630736901650616429323)
                  ·
                    rfl

theorem cell23_1606052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_1606052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606052 prefixEnd_1606052 := by exact prefixLift 1606052
  have htrace : WordTrace (prefixWord ++ tailWord_1606052) baseStart_1606052 baseEnd_1606052 := by
    simpa [prefixWord, tailWord_1606052, baseEnd_1606052] using wordTrace_append hprefix tailTrace_1606052
  have hstable : (prefixWord ++ tailWord_1606052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606052).length < 2 ^ (prefixWord ++ tailWord_1606052).sum := by decide
  have hdescent : baseEnd_1606052 < baseStart_1606052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606089 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 1, 7, 2]
def baseStart_1606089 : Nat := 118140960795 + 1606089 * 2 ^ 59
def prefixEnd_1606089 : Nat := 4983230072969 + 3 ^ 40 * 1606089 * 2
def baseEnd_1606089 : Nat := 824695630899071903101237

theorem tailTrace_1606089 : CollatzResearch.WordTrace tailWord_1606089 prefixEnd_1606089 824695630899071903101237 := by
  unfold tailWord_1606089
  simp only [CollatzResearch.WordTrace]
  refine ⟨58578878278421326008317321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39052585518947550672211547 58578878278421326008317321)
  ·
    refine ⟨43934158708815994506237991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58578878278421326008317321 43934158708815994506237991)
    ·
      refine ⟨65901238063223991759356987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43934158708815994506237991 65901238063223991759356987)
      ·
        refine ⟨98851857094835987639035481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65901238063223991759356987 98851857094835987639035481)
        ·
          refine ⟨74138892821126990729276611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98851857094835987639035481 74138892821126990729276611)
          ·
            refine ⟨111208339231690486093914917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74138892821126990729276611 111208339231690486093914917)
            ·
              refine ⟨20851563605941966142609047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111208339231690486093914917 20851563605941966142609047)
              ·
                refine ⟨31277345408912949213913571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20851563605941966142609047 31277345408912949213913571)
                ·
                  refine ⟨46916018113369423820870357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31277345408912949213913571 46916018113369423820870357)
                  ·
                    refine ⟨1099594174532095870801649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46916018113369423820870357 1099594174532095870801649)
                    ·
                      refine ⟨824695630899071903101237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1099594174532095870801649 824695630899071903101237)
                      ·
                        rfl

theorem cell23_1606089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 7, 2].length) (baseStart_1606089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606089 prefixEnd_1606089 := by exact prefixLift 1606089
  have htrace : WordTrace (prefixWord ++ tailWord_1606089) baseStart_1606089 baseEnd_1606089 := by
    simpa [prefixWord, tailWord_1606089, baseEnd_1606089] using wordTrace_append hprefix tailTrace_1606089
  have hstable : (prefixWord ++ tailWord_1606089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606089).length < 2 ^ (prefixWord ++ tailWord_1606089).sum := by decide
  have hdescent : baseEnd_1606089 < baseStart_1606089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606112 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 2, 8]
def baseStart_1606112 : Nat := 118140960795 + 1606112 * 2 ^ 59
def prefixEnd_1606112 : Nat := 4983230072969 + 3 ^ 40 * 1606112 * 2
def baseEnd_1606112 : Nat := 274902480318041771037877

theorem tailTrace_1606112 : CollatzResearch.WordTrace tailWord_1606112 prefixEnd_1606112 274902480318041771037877 := by
  unfold tailWord_1606112
  simp only [CollatzResearch.WordTrace]
  refine ⟨29289858578669000468202295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39053144771558667290936393 29289858578669000468202295)
  ·
    refine ⟨43934787868003500702303443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29289858578669000468202295 43934787868003500702303443)
    ·
      refine ⟨65902181802005251053455165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43934787868003500702303443 65902181802005251053455165)
      ·
        refine ⟨24713318175751969145045687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65902181802005251053455165 24713318175751969145045687)
        ·
          refine ⟨37069977263627953717568531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24713318175751969145045687 37069977263627953717568531)
          ·
            refine ⟨55604965895441930576352797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37069977263627953717568531 55604965895441930576352797)
            ·
              refine ⟨20851862210790723966132299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55604965895441930576352797 20851862210790723966132299)
              ·
                refine ⟨31277793316186085949198449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20851862210790723966132299 31277793316186085949198449)
                ·
                  refine ⟨23458344987139564461898837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31277793316186085949198449 23458344987139564461898837)
                  ·
                    refine ⟨274902480318041771037877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23458344987139564461898837 274902480318041771037877)
                    ·
                      rfl

theorem cell23_1606112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 2, 8].length) (baseStart_1606112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606112 prefixEnd_1606112 := by exact prefixLift 1606112
  have htrace : WordTrace (prefixWord ++ tailWord_1606112) baseStart_1606112 baseEnd_1606112 := by
    simpa [prefixWord, tailWord_1606112, baseEnd_1606112] using wordTrace_append hprefix tailTrace_1606112
  have hstable : (prefixWord ++ tailWord_1606112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606112).length < 2 ^ (prefixWord ++ tailWord_1606112).sum := by decide
  have hdescent : baseEnd_1606112 < baseStart_1606112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606119 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1606119 : Nat := 118140960795 + 1606119 * 2 ^ 59
def prefixEnd_1606119 : Nat := 4983230072969 + 3 ^ 40 * 1606119 * 2
def baseEnd_1606119 : Nat := 824711035318706785726099

theorem tailTrace_1606119 : CollatzResearch.WordTrace tailWord_1606119 prefixEnd_1606119 824711035318706785726099 := by
  unfold tailWord_1606119
  simp only [CollatzResearch.WordTrace]
  refine ⟨58579972468312641131909411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39053314978875094087939607 58579972468312641131909411)
  ·
    refine ⟨87869958702468961697864117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58579972468312641131909411 87869958702468961697864117)
    ·
      refine ⟨8237808628356465159174761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87869958702468961697864117 8237808628356465159174761)
      ·
        refine ⟨6178356471267348869381071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8237808628356465159174761 6178356471267348869381071)
        ·
          refine ⟨9267534706901023304071607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6178356471267348869381071 9267534706901023304071607)
          ·
            refine ⟨13901302060351534956107411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9267534706901023304071607 13901302060351534956107411)
            ·
              refine ⟨20851953090527302434161117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13901302060351534956107411 20851953090527302434161117)
              ·
                refine ⟨7819482408947738412810419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20851953090527302434161117 7819482408947738412810419)
                ·
                  refine ⟨11729223613421607619215629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7819482408947738412810419 11729223613421607619215629)
                  ·
                    refine ⟨4398458855033102857205861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11729223613421607619215629 4398458855033102857205861)
                    ·
                      refine ⟨824711035318706785726099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4398458855033102857205861 824711035318706785726099)
                      ·
                        rfl

theorem cell23_1606119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1606119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606119 prefixEnd_1606119 := by exact prefixLift 1606119
  have htrace : WordTrace (prefixWord ++ tailWord_1606119) baseStart_1606119 baseEnd_1606119 := by
    simpa [prefixWord, tailWord_1606119, baseEnd_1606119] using wordTrace_append hprefix tailTrace_1606119
  have hstable : (prefixWord ++ tailWord_1606119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606119).length < 2 ^ (prefixWord ++ tailWord_1606119).sum := by decide
  have hdescent : baseEnd_1606119 < baseStart_1606119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606133 : List Nat := [1, 3, 5, 1, 2, 1, 1, 2, 2, 5]
def baseStart_1606133 : Nat := 118140960795 + 1606133 * 2 ^ 59
def prefixEnd_1606133 : Nat := 4983230072969 + 3 ^ 40 * 1606133 * 2
def baseEnd_1606133 : Nat := 274906074682623243650345

theorem tailTrace_1606133 : CollatzResearch.WordTrace tailWord_1606133 prefixEnd_1606133 274906074682623243650345 := by
  unfold tailWord_1606133
  simp only [CollatzResearch.WordTrace]
  refine ⟨58580483090261921522919053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39053655393507947681946035 58580483090261921522919053)
  ·
    refine ⟨21967681158848220571094645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58580483090261921522919053 21967681158848220571094645)
    ·
      refine ⟨2059470108642020678540123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21967681158848220571094645 2059470108642020678540123)
      ·
        refine ⟨3089205162963031017810185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2059470108642020678540123 3089205162963031017810185)
        ·
          refine ⟨2316903872222273263357639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3089205162963031017810185 2316903872222273263357639)
          ·
            refine ⟨3475355808333409895036459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2316903872222273263357639 3475355808333409895036459)
            ·
              refine ⟨5213033712500114842554689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3475355808333409895036459 5213033712500114842554689)
              ·
                refine ⟨3909775284375086131916017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5213033712500114842554689 3909775284375086131916017)
                ·
                  refine ⟨2932331463281314598937013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3909775284375086131916017 2932331463281314598937013)
                  ·
                    refine ⟨274906074682623243650345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2932331463281314598937013 274906074682623243650345)
                    ·
                      rfl

theorem cell23_1606133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_1606133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606133 prefixEnd_1606133 := by exact prefixLift 1606133
  have htrace : WordTrace (prefixWord ++ tailWord_1606133) baseStart_1606133 baseEnd_1606133 := by
    simpa [prefixWord, tailWord_1606133, baseEnd_1606133] using wordTrace_append hprefix tailTrace_1606133
  have hstable : (prefixWord ++ tailWord_1606133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606133).length < 2 ^ (prefixWord ++ tailWord_1606133).sum := by decide
  have hdescent : baseEnd_1606133 < baseStart_1606133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606173 : List Nat := [1, 4, 2, 2, 1, 3, 2, 1, 2, 2, 3]
def baseStart_1606173 : Nat := 118140960795 + 1606173 * 2 ^ 59
def prefixEnd_1606173 : Nat := 4983230072969 + 3 ^ 40 * 1606173 * 2
def baseEnd_1606173 : Nat := 824738763274049574450851

theorem tailTrace_1606173 : CollatzResearch.WordTrace tailWord_1606173 prefixEnd_1606173 824738763274049574450851 := by
  unfold tailWord_1606173
  simp only [CollatzResearch.WordTrace]
  refine ⟨58581942010117008354375173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39054628006744672236250115 58581942010117008354375173)
  ·
    refine ⟨10984114126896939066445345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58581942010117008354375173 10984114126896939066445345)
    ·
      refine ⟨8238085595172704299834009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10984114126896939066445345 8238085595172704299834009)
      ·
        refine ⟨6178564196379528224875507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8238085595172704299834009 6178564196379528224875507)
        ·
          refine ⟨9267846294569292337313261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6178564196379528224875507 9267846294569292337313261)
          ·
            refine ⟨3475442360463484626492473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9267846294569292337313261 3475442360463484626492473)
            ·
              refine ⟨2606581770347613469869355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3475442360463484626492473 2606581770347613469869355)
              ·
                refine ⟨3909872655521420204804033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2606581770347613469869355 3909872655521420204804033)
                ·
                  refine ⟨2932404491641065153603025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3909872655521420204804033 2932404491641065153603025)
                  ·
                    refine ⟨2199303368730798865202269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2932404491641065153603025 2199303368730798865202269)
                    ·
                      refine ⟨824738763274049574450851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2199303368730798865202269 824738763274049574450851)
                      ·
                        rfl

theorem cell23_1606173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_1606173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606173 prefixEnd_1606173 := by exact prefixLift 1606173
  have htrace : WordTrace (prefixWord ++ tailWord_1606173) baseStart_1606173 baseEnd_1606173 := by
    simpa [prefixWord, tailWord_1606173, baseEnd_1606173] using wordTrace_append hprefix tailTrace_1606173
  have hstable : (prefixWord ++ tailWord_1606173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606173).length < 2 ^ (prefixWord ++ tailWord_1606173).sum := by decide
  have hdescent : baseEnd_1606173 < baseStart_1606173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606219 : List Nat := [1, 1, 1, 1, 3, 1, 5, 3, 1, 6]
def baseStart_1606219 : Nat := 118140960795 + 1606219 * 2 ^ 59
def prefixEnd_1606219 : Nat := 4983230072969 + 3 ^ 40 * 1606219 * 2
def baseEnd_1606219 : Nat := 274920794461385464825213

theorem tailTrace_1606219 : CollatzResearch.WordTrace tailWord_1606219 prefixEnd_1606219 274920794461385464825213 := by
  unfold tailWord_1606219
  simp only [CollatzResearch.WordTrace]
  refine ⟨58583619767950358210549711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39055746511966905473699807 58583619767950358210549711)
  ·
    refine ⟨87875429651925537315824567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58583619767950358210549711 87875429651925537315824567)
    ·
      refine ⟨131813144477888305973736851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87875429651925537315824567 131813144477888305973736851)
      ·
        refine ⟨197719716716832458960605277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131813144477888305973736851 197719716716832458960605277)
        ·
          refine ⟨74144893768812172110226979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197719716716832458960605277 74144893768812172110226979)
          ·
            refine ⟨111217340653218258165340469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74144893768812172110226979 111217340653218258165340469)
            ·
              refine ⟨10426625686239211703000669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111217340653218258165340469 10426625686239211703000669)
              ·
                refine ⟨3909984632339704388625251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10426625686239211703000669 3909984632339704388625251)
                ·
                  refine ⟨5864976948509556582937877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3909984632339704388625251 5864976948509556582937877)
                  ·
                    refine ⟨274920794461385464825213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5864976948509556582937877 274920794461385464825213)
                    ·
                      rfl

theorem cell23_1606219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 6].length) (baseStart_1606219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606219 prefixEnd_1606219 := by exact prefixLift 1606219
  have htrace : WordTrace (prefixWord ++ tailWord_1606219) baseStart_1606219 baseEnd_1606219 := by
    simpa [prefixWord, tailWord_1606219, baseEnd_1606219] using wordTrace_append hprefix tailTrace_1606219
  have hstable : (prefixWord ++ tailWord_1606219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606219).length < 2 ^ (prefixWord ++ tailWord_1606219).sum := by decide
  have hdescent : baseEnd_1606219 < baseStart_1606219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606226 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_1606226 : Nat := 118140960795 + 1606226 * 2 ^ 59
def prefixEnd_1606226 : Nat := 4983230072969 + 3 ^ 40 * 1606226 * 2
def baseEnd_1606226 : Nat := 824765977748737867088107

theorem tailTrace_1606226 : CollatzResearch.WordTrace tailWord_1606226 prefixEnd_1606226 824765977748737867088107 := by
  unfold tailWord_1606226
  simp only [CollatzResearch.WordTrace]
  refine ⟨14645968769731249601513633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39055916719283332270703021 14645968769731249601513633)
  ·
    refine ⟨10984476577298437201135225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14645968769731249601513633 10984476577298437201135225)
    ·
      refine ⟨8238357432973827900851419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10984476577298437201135225 8238357432973827900851419)
      ·
        refine ⟨12357536149460741851277129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8238357432973827900851419 12357536149460741851277129)
        ·
          refine ⟨9268152112095556388457847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12357536149460741851277129 9268152112095556388457847)
          ·
            refine ⟨13902228168143334582686771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9268152112095556388457847 13902228168143334582686771)
            ·
              refine ⟨20853342252215001874030157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13902228168143334582686771 20853342252215001874030157)
              ·
                refine ⟨7820003344580625702761309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20853342252215001874030157 7820003344580625702761309)
                ·
                  refine ⟨2932501254217734638535491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7820003344580625702761309 2932501254217734638535491)
                  ·
                    refine ⟨4398751881326601957803237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2932501254217734638535491 4398751881326601957803237)
                    ·
                      refine ⟨824765977748737867088107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4398751881326601957803237 824765977748737867088107)
                      ·
                        rfl

theorem cell23_1606226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_1606226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606226 prefixEnd_1606226 := by exact prefixLift 1606226
  have htrace : WordTrace (prefixWord ++ tailWord_1606226) baseStart_1606226 baseEnd_1606226 := by
    simpa [prefixWord, tailWord_1606226, baseEnd_1606226] using wordTrace_append hprefix tailTrace_1606226
  have hstable : (prefixWord ++ tailWord_1606226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606226).length < 2 ^ (prefixWord ++ tailWord_1606226).sum := by decide
  have hdescent : baseEnd_1606226 < baseStart_1606226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606243 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 5, 2, 2]
def baseStart_1606243 : Nat := 118140960795 + 1606243 * 2 ^ 59
def prefixEnd_1606243 : Nat := 4983230072969 + 3 ^ 40 * 1606243 * 2
def baseEnd_1606243 : Nat := 824774706919864300575529

theorem tailTrace_1606243 : CollatzResearch.WordTrace tailWord_1606243 prefixEnd_1606243 824774706919864300575529 := by
  unfold tailWord_1606243
  simp only [CollatzResearch.WordTrace]
  refine ⟨58584495119863410309423383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39056330079908940206282255 58584495119863410309423383)
  ·
    refine ⟨87876742679795115464135075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58584495119863410309423383 87876742679795115464135075)
    ·
      refine ⟨131815114019692673196202613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87876742679795115464135075 131815114019692673196202613)
      ·
        refine ⟨12357666939346188112143995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131815114019692673196202613 12357666939346188112143995)
        ·
          refine ⟨18536500409019282168215993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12357666939346188112143995 18536500409019282168215993)
          ·
            refine ⟨13902375306764461626161995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18536500409019282168215993 13902375306764461626161995)
            ·
              refine ⟨20853562960146692439242993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13902375306764461626161995 20853562960146692439242993)
              ·
                refine ⟨15640172220110019329432245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20853562960146692439242993 15640172220110019329432245)
                ·
                  refine ⟨1466266145635314312134273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15640172220110019329432245 1466266145635314312134273)
                  ·
                    refine ⟨1099699609226485734100705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1466266145635314312134273 1099699609226485734100705)
                    ·
                      refine ⟨824774706919864300575529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1099699609226485734100705 824774706919864300575529)
                      ·
                        rfl

theorem cell23_1606243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_1606243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606243 prefixEnd_1606243 := by exact prefixLift 1606243
  have htrace : WordTrace (prefixWord ++ tailWord_1606243) baseStart_1606243 baseEnd_1606243 := by
    simpa [prefixWord, tailWord_1606243, baseEnd_1606243] using wordTrace_append hprefix tailTrace_1606243
  have hstable : (prefixWord ++ tailWord_1606243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606243).length < 2 ^ (prefixWord ++ tailWord_1606243).sum := by decide
  have hdescent : baseEnd_1606243 < baseStart_1606243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606253 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 4, 4]
def baseStart_1606253 : Nat := 118140960795 + 1606253 * 2 ^ 59
def prefixEnd_1606253 : Nat := 4983230072969 + 3 ^ 40 * 1606253 * 2
def baseEnd_1606253 : Nat := 274926613908803087150161

theorem tailTrace_1606253 : CollatzResearch.WordTrace tailWord_1606253 prefixEnd_1606253 274926613908803087150161 := by
  unfold tailWord_1606253
  simp only [CollatzResearch.WordTrace]
  refine ⟨58584859849827182017287413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39056573233218121344858275 58584859849827182017287413)
  ·
    refine ⟨5492330610921298314120695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58584859849827182017287413 5492330610921298314120695)
    ·
      refine ⟨8238495916381947471181043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5492330610921298314120695 8238495916381947471181043)
      ·
        refine ⟨12357743874572921206771565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8238495916381947471181043 12357743874572921206771565)
        ·
          refine ⟨4634153952964845452539337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12357743874572921206771565 4634153952964845452539337)
          ·
            refine ⟨3475615464723634089404503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4634153952964845452539337 3475615464723634089404503)
            ·
              refine ⟨5213423197085451134106755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3475615464723634089404503 5213423197085451134106755)
              ·
                refine ⟨7820134795628176701160133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5213423197085451134106755 7820134795628176701160133)
                ·
                  refine ⟨1466275274180283131467525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7820134795628176701160133 1466275274180283131467525)
                  ·
                    refine ⟨274926613908803087150161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1466275274180283131467525 274926613908803087150161)
                    ·
                      rfl

theorem cell23_1606253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_1606253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606253 prefixEnd_1606253 := by exact prefixLift 1606253
  have htrace : WordTrace (prefixWord ++ tailWord_1606253) baseStart_1606253 baseEnd_1606253 := by
    simpa [prefixWord, tailWord_1606253, baseEnd_1606253] using wordTrace_append hprefix tailTrace_1606253
  have hstable : (prefixWord ++ tailWord_1606253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606253).length < 2 ^ (prefixWord ++ tailWord_1606253).sum := by decide
  have hdescent : baseEnd_1606253 < baseStart_1606253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606274 : List Nat := [3, 4, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1606274 : Nat := 118140960795 + 1606274 * 2 ^ 59
def prefixEnd_1606274 : Nat := 4983230072969 + 3 ^ 40 * 1606274 * 2
def baseEnd_1606274 : Nat := 274930208273384559762629

theorem tailTrace_1606274 : CollatzResearch.WordTrace tailWord_1606274 prefixEnd_1606274 274930208273384559762629 := by
  unfold tailWord_1606274
  simp only [CollatzResearch.WordTrace]
  refine ⟨14646406445687775650950469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39057083855167401735867917 14646406445687775650950469)
  ·
    refine ⟨2746201208566457934553213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14646406445687775650950469 2746201208566457934553213)
    ·
      refine ⟨1029825453212421725457455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2746201208566457934553213 1029825453212421725457455)
      ·
        refine ⟨1544738179818632588186183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1029825453212421725457455 1544738179818632588186183)
        ·
          refine ⟨2317107269727948882279275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1544738179818632588186183 2317107269727948882279275)
          ·
            refine ⟨3475660904591923323418913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2317107269727948882279275 3475660904591923323418913)
            ·
              refine ⟨2606745678443942492564185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3475660904591923323418913 2606745678443942492564185)
              ·
                refine ⟨1955059258832956869423139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2606745678443942492564185 1955059258832956869423139)
                ·
                  refine ⟨2932588888249435304134709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1955059258832956869423139 2932588888249435304134709)
                  ·
                    refine ⟨274930208273384559762629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2932588888249435304134709 274930208273384559762629)
                    ·
                      rfl

theorem cell23_1606274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1606274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606274 prefixEnd_1606274 := by exact prefixLift 1606274
  have htrace : WordTrace (prefixWord ++ tailWord_1606274) baseStart_1606274 baseEnd_1606274 := by
    simpa [prefixWord, tailWord_1606274, baseEnd_1606274] using wordTrace_append hprefix tailTrace_1606274
  have hstable : (prefixWord ++ tailWord_1606274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606274).length < 2 ^ (prefixWord ++ tailWord_1606274).sum := by decide
  have hdescent : baseEnd_1606274 < baseStart_1606274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606311 : List Nat := [1, 1, 6, 3, 2, 1, 1, 1, 3, 2, 2]
def baseStart_1606311 : Nat := 118140960795 + 1606311 * 2 ^ 59
def prefixEnd_1606311 : Nat := 4983230072969 + 3 ^ 40 * 1606311 * 2
def baseEnd_1606311 : Nat := 824809623604370034525217

theorem tailTrace_1606311 : CollatzResearch.WordTrace tailWord_1606311 prefixEnd_1606311 824809623604370034525217 := by
  unfold tailWord_1606311
  simp only [CollatzResearch.WordTrace]
  refine ⟨58586975283617057922898787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39057983522411371948599191 58586975283617057922898787)
  ·
    refine ⟨87880462925425586884348181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58586975283617057922898787 87880462925425586884348181)
    ·
      refine ⟨4119396699629324385203821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87880462925425586884348181 4119396699629324385203821)
      ·
        refine ⟨1544773762360996644451433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4119396699629324385203821 1544773762360996644451433)
        ·
          refine ⟨1158580321770747483338575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1544773762360996644451433 1158580321770747483338575)
          ·
            refine ⟨1737870482656121225007863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158580321770747483338575 1737870482656121225007863)
            ·
              refine ⟨2606805723984181837511795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1737870482656121225007863 2606805723984181837511795)
              ·
                refine ⟨3910208585976272756267693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2606805723984181837511795 3910208585976272756267693)
                ·
                  refine ⟨1466328219741102283600385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3910208585976272756267693 1466328219741102283600385)
                  ·
                    refine ⟨1099746164805826712700289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1466328219741102283600385 1099746164805826712700289)
                    ·
                      refine ⟨824809623604370034525217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1099746164805826712700289 824809623604370034525217)
                      ·
                        rfl

theorem cell23_1606311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_1606311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606311 prefixEnd_1606311 := by exact prefixLift 1606311
  have htrace : WordTrace (prefixWord ++ tailWord_1606311) baseStart_1606311 baseEnd_1606311 := by
    simpa [prefixWord, tailWord_1606311, baseEnd_1606311] using wordTrace_append hprefix tailTrace_1606311
  have hstable : (prefixWord ++ tailWord_1606311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606311).length < 2 ^ (prefixWord ++ tailWord_1606311).sum := by decide
  have hdescent : baseEnd_1606311 < baseStart_1606311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606336 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 5]
def baseStart_1606336 : Nat := 118140960795 + 1606336 * 2 ^ 59
def prefixEnd_1606336 : Nat := 4983230072969 + 3 ^ 40 * 1606336 * 2
def baseEnd_1606336 : Nat := 824822460620732436712601

theorem tailTrace_1606336 : CollatzResearch.WordTrace tailWord_1606336 prefixEnd_1606336 824822460620732436712601 := by
  unfold tailWord_1606336
  simp only [CollatzResearch.WordTrace]
  refine ⟨29293943554263243596279431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39058591405684324795039241 29293943554263243596279431)
  ·
    refine ⟨43940915331394865394419147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29293943554263243596279431 43940915331394865394419147)
    ·
      refine ⟨65911372997092298091628721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43940915331394865394419147 65911372997092298091628721)
      ·
        refine ⟨49433529747819223568721541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65911372997092298091628721 49433529747819223568721541)
        ·
          refine ⟨9268786827716104419135289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49433529747819223568721541 9268786827716104419135289)
          ·
            refine ⟨6951590120787078314351467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9268786827716104419135289 6951590120787078314351467)
            ·
              refine ⟨10427385181180617471527201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6951590120787078314351467 10427385181180617471527201)
              ·
                refine ⟨7820538885885463103645401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10427385181180617471527201 7820538885885463103645401)
                ·
                  refine ⟨5865404164414097327734051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7820538885885463103645401 5865404164414097327734051)
                  ·
                    refine ⟨8798106246621145991601077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5865404164414097327734051 8798106246621145991601077)
                    ·
                      refine ⟨824822460620732436712601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8798106246621145991601077 824822460620732436712601)
                      ·
                        rfl

theorem cell23_1606336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_1606336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606336 prefixEnd_1606336 := by exact prefixLift 1606336
  have htrace : WordTrace (prefixWord ++ tailWord_1606336) baseStart_1606336 baseEnd_1606336 := by
    simpa [prefixWord, tailWord_1606336, baseEnd_1606336] using wordTrace_append hprefix tailTrace_1606336
  have hstable : (prefixWord ++ tailWord_1606336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606336).length < 2 ^ (prefixWord ++ tailWord_1606336).sum := by decide
  have hdescent : baseEnd_1606336 < baseStart_1606336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606350 : List Nat := [4, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2]
def baseStart_1606350 : Nat := 118140960795 + 1606350 * 2 ^ 59
def prefixEnd_1606350 : Nat := 4983230072969 + 3 ^ 40 * 1606350 * 2
def baseEnd_1606350 : Nat := 824829649349895381937537

theorem tailTrace_1606350 : CollatzResearch.WordTrace tailWord_1606350 prefixEnd_1606350 824829649349895381937537 := by
  unfold tailWord_1606350
  simp only [CollatzResearch.WordTrace]
  refine ⟨7323549716309470947946063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39058931820317178389045669 7323549716309470947946063)
  ·
    refine ⟨10985324574464206421919095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7323549716309470947946063 10985324574464206421919095)
    ·
      refine ⟨16477986861696309632878643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10985324574464206421919095 16477986861696309632878643)
      ·
        refine ⟨24716980292544464449317965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16477986861696309632878643 24716980292544464449317965)
        ·
          refine ⟨9268867609704174168494237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24716980292544464449317965 9268867609704174168494237)
          ·
            refine ⟨3475825353639065313185339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9268867609704174168494237 3475825353639065313185339)
            ·
              refine ⟨5213738030458597969778009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3475825353639065313185339 5213738030458597969778009)
              ·
                refine ⟨3910303522843948477333507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5213738030458597969778009 3910303522843948477333507)
                ·
                  refine ⟨5865455284265922716000261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3910303522843948477333507 5865455284265922716000261)
                  ·
                    refine ⟨1099772865799860509250049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5865455284265922716000261 1099772865799860509250049)
                    ·
                      refine ⟨824829649349895381937537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1099772865799860509250049 824829649349895381937537)
                      ·
                        rfl

theorem cell23_1606350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_1606350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606350 prefixEnd_1606350 := by exact prefixLift 1606350
  have htrace : WordTrace (prefixWord ++ tailWord_1606350) baseStart_1606350 baseEnd_1606350 := by
    simpa [prefixWord, tailWord_1606350, baseEnd_1606350] using wordTrace_append hprefix tailTrace_1606350
  have hstable : (prefixWord ++ tailWord_1606350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606350).length < 2 ^ (prefixWord ++ tailWord_1606350).sum := by decide
  have hdescent : baseEnd_1606350 < baseStart_1606350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606354 : List Nat := [3, 2, 2, 2, 3, 1, 3, 1, 1, 3, 2]
def baseStart_1606354 : Nat := 118140960795 + 1606354 * 2 ^ 59
def prefixEnd_1606354 : Nat := 4983230072969 + 3 ^ 40 * 1606354 * 2
def baseEnd_1606354 : Nat := 824831703272513366287519

theorem tailTrace_1606354 : CollatzResearch.WordTrace tailWord_1606354 prefixEnd_1606354 824831703272513366287519 := by
  unfold tailWord_1606354
  simp only [CollatzResearch.WordTrace]
  refine ⟨14647135905615319066678529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39059029081640850844476077 14647135905615319066678529)
  ·
    refine ⟨10985351929211489300008897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14647135905615319066678529 10985351929211489300008897)
    ·
      refine ⟨8239013946908616975006673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10985351929211489300008897 8239013946908616975006673)
      ·
        refine ⟨6179260460181462731255005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8239013946908616975006673 6179260460181462731255005)
        ·
          refine ⟨2317222672568048524220627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6179260460181462731255005 2317222672568048524220627)
          ·
            refine ⟨3475834008852072786330941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2317222672568048524220627 3475834008852072786330941)
            ·
              refine ⟨1303437753319527294874103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3475834008852072786330941 1303437753319527294874103)
              ·
                refine ⟨1955156629979290942311155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303437753319527294874103 1955156629979290942311155)
                ·
                  refine ⟨2932734944968936413466733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1955156629979290942311155 2932734944968936413466733)
                  ·
                    refine ⟨1099775604363351155050025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2932734944968936413466733 1099775604363351155050025)
                    ·
                      refine ⟨824831703272513366287519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1099775604363351155050025 824831703272513366287519)
                      ·
                        rfl

theorem cell23_1606354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_1606354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606354 prefixEnd_1606354 := by exact prefixLift 1606354
  have htrace : WordTrace (prefixWord ++ tailWord_1606354) baseStart_1606354 baseEnd_1606354 := by
    simpa [prefixWord, tailWord_1606354, baseEnd_1606354] using wordTrace_append hprefix tailTrace_1606354
  have hstable : (prefixWord ++ tailWord_1606354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606354).length < 2 ^ (prefixWord ++ tailWord_1606354).sum := by decide
  have hdescent : baseEnd_1606354 < baseStart_1606354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606367 : List Nat := [1, 1, 2, 3, 2, 4, 2, 2, 2, 2, 2]
def baseStart_1606367 : Nat := 118140960795 + 1606367 * 2 ^ 59
def prefixEnd_1606367 : Nat := 4983230072969 + 3 ^ 40 * 1606367 * 2
def baseEnd_1606367 : Nat := 824838378521021815424959

theorem tailTrace_1606367 : CollatzResearch.WordTrace tailWord_1606367 prefixEnd_1606367 824838378521021815424959 := by
  unfold tailWord_1606367
  simp only [CollatzResearch.WordTrace]
  refine ⟨58589017771414179486937355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39059345180942786324624903 58589017771414179486937355)
  ·
    refine ⟨87883526657121269230406033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58589017771414179486937355 87883526657121269230406033)
    ·
      refine ⟨65912644992840951922804525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87883526657121269230406033 65912644992840951922804525)
      ·
        refine ⟨24717241872315356971051697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65912644992840951922804525 24717241872315356971051697)
        ·
          refine ⟨18537931404236517728288773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24717241872315356971051697 18537931404236517728288773)
          ·
            refine ⟨3475862138294347074054145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18537931404236517728288773 3475862138294347074054145)
            ·
              refine ⟨2606896603720760305540609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3475862138294347074054145 2606896603720760305540609)
              ·
                refine ⟨1955172452790570229155457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2606896603720760305540609 1955172452790570229155457)
                ·
                  refine ⟨1466379339592927671866593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1955172452790570229155457 1466379339592927671866593)
                  ·
                    refine ⟨1099784504694695753899945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1466379339592927671866593 1099784504694695753899945)
                    ·
                      refine ⟨824838378521021815424959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1099784504694695753899945 824838378521021815424959)
                      ·
                        rfl

theorem cell23_1606367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_1606367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606367 prefixEnd_1606367 := by exact prefixLift 1606367
  have htrace : WordTrace (prefixWord ++ tailWord_1606367) baseStart_1606367 baseEnd_1606367 := by
    simpa [prefixWord, tailWord_1606367, baseEnd_1606367] using wordTrace_append hprefix tailTrace_1606367
  have hstable : (prefixWord ++ tailWord_1606367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606367).length < 2 ^ (prefixWord ++ tailWord_1606367).sum := by decide
  have hdescent : baseEnd_1606367 < baseStart_1606367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606383 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 3]
def baseStart_1606383 : Nat := 118140960795 + 1606383 * 2 ^ 59
def prefixEnd_1606383 : Nat := 4983230072969 + 3 ^ 40 * 1606383 * 2
def baseEnd_1606383 : Nat := 824846594211493752824885

theorem tailTrace_1606383 : CollatzResearch.WordTrace tailWord_1606383 prefixEnd_1606383 824846594211493752824885 := by
  unfold tailWord_1606383
  simp only [CollatzResearch.WordTrace]
  refine ⟨58589601339356214219519803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39059734226237476146346535 58589601339356214219519803)
  ·
    refine ⟨87884402009034321329279705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58589601339356214219519803 87884402009034321329279705)
    ·
      refine ⟨65913301506775740996959779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87884402009034321329279705 65913301506775740996959779)
      ·
        refine ⟨98869952260163611495439669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65913301506775740996959779 98869952260163611495439669)
        ·
          refine ⟨9269058024390338577697469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98869952260163611495439669 9269058024390338577697469)
          ·
            refine ⟨3475896759146376966636551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9269058024390338577697469 3475896759146376966636551)
            ·
              refine ⟨5213845138719565449954827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3475896759146376966636551 5213845138719565449954827)
              ·
                refine ⟨7820767708079348174932241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5213845138719565449954827 7820767708079348174932241)
                ·
                  refine ⟨5865575781059511131199181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7820767708079348174932241 5865575781059511131199181)
                  ·
                    refine ⟨2199590917897316674199693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5865575781059511131199181 2199590917897316674199693)
                    ·
                      refine ⟨824846594211493752824885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2199590917897316674199693 824846594211493752824885)
                      ·
                        rfl

theorem cell23_1606383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 3].length) (baseStart_1606383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606383 prefixEnd_1606383 := by exact prefixLift 1606383
  have htrace : WordTrace (prefixWord ++ tailWord_1606383) baseStart_1606383 baseEnd_1606383 := by
    simpa [prefixWord, tailWord_1606383, baseEnd_1606383] using wordTrace_append hprefix tailTrace_1606383
  have hstable : (prefixWord ++ tailWord_1606383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606383).length < 2 ^ (prefixWord ++ tailWord_1606383).sum := by decide
  have hdescent : baseEnd_1606383 < baseStart_1606383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606418 : List Nat := [3, 2, 4, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_1606418 : Nat := 118140960795 + 1606418 * 2 ^ 59
def prefixEnd_1606418 : Nat := 4983230072969 + 3 ^ 40 * 1606418 * 2
def baseEnd_1606418 : Nat := 824864566034401115887225

theorem tailTrace_1606418 : CollatzResearch.WordTrace tailWord_1606418 prefixEnd_1606418 824864566034401115887225 := by
  unfold tailWord_1606418
  simp only [CollatzResearch.WordTrace]
  refine ⟨14647719473557353799260977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39060585262819610131362605 14647719473557353799260977)
  ·
    refine ⟨10985789605168015349445733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14647719473557353799260977 10985789605168015349445733)
    ·
      refine ⟨2059835550969002878021075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10985789605168015349445733 2059835550969002878021075)
      ·
        refine ⟨3089753326453504317031613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2059835550969002878021075 3089753326453504317031613)
        ·
          refine ⟨1158657497420064118886855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3089753326453504317031613 1158657497420064118886855)
          ·
            refine ⟨1737986246130096178330283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158657497420064118886855 1737986246130096178330283)
            ·
              refine ⟨2606979369195144267495425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1737986246130096178330283 2606979369195144267495425)
              ·
                refine ⟨1955234526896358200621569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2606979369195144267495425 1955234526896358200621569)
                ·
                  refine ⟨1466425895172268650466177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1955234526896358200621569 1466425895172268650466177)
                  ·
                    refine ⟨1099819421379201487849633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1466425895172268650466177 1099819421379201487849633)
                    ·
                      refine ⟨824864566034401115887225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1099819421379201487849633 824864566034401115887225)
                      ·
                        rfl

theorem cell23_1606418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_1606418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606418 prefixEnd_1606418 := by exact prefixLift 1606418
  have htrace : WordTrace (prefixWord ++ tailWord_1606418) baseStart_1606418 baseEnd_1606418 := by
    simpa [prefixWord, tailWord_1606418, baseEnd_1606418] using wordTrace_append hprefix tailTrace_1606418
  have hstable : (prefixWord ++ tailWord_1606418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606418).length < 2 ^ (prefixWord ++ tailWord_1606418).sum := by decide
  have hdescent : baseEnd_1606418 < baseStart_1606418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606440 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 2, 4, 2]
def baseStart_1606440 : Nat := 118140960795 + 1606440 * 2 ^ 59
def prefixEnd_1606440 : Nat := 4983230072969 + 3 ^ 40 * 1606440 * 2
def baseEnd_1606440 : Nat := 824875862608800029812123

theorem tailTrace_1606440 : CollatzResearch.WordTrace tailWord_1606440 prefixEnd_1606440 824875862608800029812123 := by
  unfold tailWord_1606440
  simp only [CollatzResearch.WordTrace]
  refine ⟨29295840150074856477172387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39061120200099808636229849 29295840150074856477172387)
  ·
    refine ⟨43943760225112284715758581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29295840150074856477172387 43943760225112284715758581)
    ·
      refine ⟨4119727521104276692102367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43943760225112284715758581 4119727521104276692102367)
      ·
        refine ⟨6179591281656415038153551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4119727521104276692102367 6179591281656415038153551)
        ·
          refine ⟨9269386922484622557230327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6179591281656415038153551 9269386922484622557230327)
          ·
            refine ⟨13904080383726933835845491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9269386922484622557230327 13904080383726933835845491)
            ·
              refine ⟨20856120575590400753768237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13904080383726933835845491 20856120575590400753768237)
              ·
                refine ⟨7821045215846400282663089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20856120575590400753768237 7821045215846400282663089)
                ·
                  refine ⟨5865783911884800211997317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7821045215846400282663089 5865783911884800211997317)
                  ·
                    refine ⟨1099834483478400039749497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5865783911884800211997317 1099834483478400039749497)
                    ·
                      refine ⟨824875862608800029812123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1099834483478400039749497 824875862608800029812123)
                      ·
                        rfl

theorem cell23_1606440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_1606440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606440 prefixEnd_1606440 := by exact prefixLift 1606440
  have htrace : WordTrace (prefixWord ++ tailWord_1606440) baseStart_1606440 baseEnd_1606440 := by
    simpa [prefixWord, tailWord_1606440, baseEnd_1606440] using wordTrace_append hprefix tailTrace_1606440
  have hstable : (prefixWord ++ tailWord_1606440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606440).length < 2 ^ (prefixWord ++ tailWord_1606440).sum := by decide
  have hdescent : baseEnd_1606440 < baseStart_1606440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606484 : List Nat := [2, 4, 1, 1, 5, 1, 1, 1, 3, 4]
def baseStart_1606484 : Nat := 118140960795 + 1606484 * 2 ^ 59
def prefixEnd_1606484 : Nat := 4983230072969 + 3 ^ 40 * 1606484 * 2
def baseEnd_1606484 : Nat := 274966151919199285887307

theorem tailTrace_1606484 : CollatzResearch.WordTrace tailWord_1606484 prefixEnd_1606484 274966151919199285887307 := by
  unfold tailWord_1606484
  simp only [CollatzResearch.WordTrace]
  refine ⟨29296642555995154234473253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39062190074660205645964337 29296642555995154234473253)
  ·
    refine ⟨5493120479249091418963735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29296642555995154234473253 5493120479249091418963735)
    ·
      refine ⟨8239680718873637128445603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5493120479249091418963735 8239680718873637128445603)
      ·
        refine ⟨12359521078310455692668405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8239680718873637128445603 12359521078310455692668405)
        ·
          refine ⟨1158705101091605221187663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12359521078310455692668405 1158705101091605221187663)
          ·
            refine ⟨1738057651637407831781495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158705101091605221187663 1738057651637407831781495)
            ·
              refine ⟨2607086477456111747672243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738057651637407831781495 2607086477456111747672243)
              ·
                refine ⟨3910629716184167621508365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2607086477456111747672243 3910629716184167621508365)
                ·
                  refine ⟨1466486143569062858065637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3910629716184167621508365 1466486143569062858065637)
                  ·
                    refine ⟨274966151919199285887307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1466486143569062858065637 274966151919199285887307)
                    ·
                      rfl

theorem cell23_1606484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_1606484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606484 prefixEnd_1606484 := by exact prefixLift 1606484
  have htrace : WordTrace (prefixWord ++ tailWord_1606484) baseStart_1606484 baseEnd_1606484 := by
    simpa [prefixWord, tailWord_1606484, baseEnd_1606484] using wordTrace_append hprefix tailTrace_1606484
  have hstable : (prefixWord ++ tailWord_1606484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606484).length < 2 ^ (prefixWord ++ tailWord_1606484).sum := by decide
  have hdescent : baseEnd_1606484 < baseStart_1606484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606517 : List Nat := [1, 3, 4, 1, 1, 2, 1, 3, 2, 3, 2]
def baseStart_1606517 : Nat := 118140960795 + 1606517 * 2 ^ 59
def prefixEnd_1606517 : Nat := 4983230072969 + 3 ^ 40 * 1606517 * 2
def baseEnd_1606517 : Nat := 824915400619196228549269

theorem tailTrace_1606517 : CollatzResearch.WordTrace tailWord_1606517 prefixEnd_1606517 824915400619196228549269 := by
  unfold tailWord_1606517
  simp only [CollatzResearch.WordTrace]
  refine ⟨58594488720870755104897805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39062992480580503403265203 58594488720870755104897805)
  ·
    refine ⟨21972933270326533164336677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58594488720870755104897805 21972933270326533164336677)
    ·
      refine ⟨4119924988186224968313127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21972933270326533164336677 4119924988186224968313127)
      ·
        refine ⟨6179887482279337452469691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4119924988186224968313127 6179887482279337452469691)
        ·
          refine ⟨9269831223419006178704537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6179887482279337452469691 9269831223419006178704537)
          ·
            refine ⟨6952373417564254634028403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9269831223419006178704537 6952373417564254634028403)
            ·
              refine ⟨10428560126346381951042605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6952373417564254634028403 10428560126346381951042605)
              ·
                refine ⟨3910710047379893231640977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10428560126346381951042605 3910710047379893231640977)
                ·
                  refine ⟨2933032535534919923730733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3910710047379893231640977 2933032535534919923730733)
                  ·
                    refine ⟨1099887200825594971399025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2933032535534919923730733 1099887200825594971399025)
                    ·
                      refine ⟨824915400619196228549269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1099887200825594971399025 824915400619196228549269)
                      ·
                        rfl

theorem cell23_1606517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_1606517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606517 prefixEnd_1606517 := by exact prefixLift 1606517
  have htrace : WordTrace (prefixWord ++ tailWord_1606517) baseStart_1606517 baseEnd_1606517 := by
    simpa [prefixWord, tailWord_1606517, baseEnd_1606517] using wordTrace_append hprefix tailTrace_1606517
  have hstable : (prefixWord ++ tailWord_1606517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606517).length < 2 ^ (prefixWord ++ tailWord_1606517).sum := by decide
  have hdescent : baseEnd_1606517 < baseStart_1606517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606523 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 6, 4]
def baseStart_1606523 : Nat := 118140960795 + 1606523 * 2 ^ 59
def prefixEnd_1606523 : Nat := 4983230072969 + 3 ^ 40 * 1606523 * 2
def baseEnd_1606523 : Nat := 274972827167707735024747

theorem tailTrace_1606523 : CollatzResearch.WordTrace tailWord_1606523 prefixEnd_1606523 274972827167707735024747 := by
  unfold tailWord_1606523
  simp only [CollatzResearch.WordTrace]
  refine ⟨58594707558849018129616223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39063138372566012086410815 58594707558849018129616223)
  ·
    refine ⟨87892061338273527194424335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58594707558849018129616223 87892061338273527194424335)
    ·
      refine ⟨131838092007410290791636503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87892061338273527194424335 131838092007410290791636503)
      ·
        refine ⟨197757138011115436187454755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131838092007410290791636503 197757138011115436187454755)
        ·
          refine ⟨296635707016673154281182133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197757138011115436187454755 296635707016673154281182133)
          ·
            refine ⟨27809597532813108213860825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 296635707016673154281182133 27809597532813108213860825)
            ·
              refine ⟨20857198149609831160395619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27809597532813108213860825 20857198149609831160395619)
              ·
                refine ⟨31285797224414746740593429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20857198149609831160395619 31285797224414746740593429)
                ·
                  refine ⟨1466521744894441253465317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31285797224414746740593429 1466521744894441253465317)
                  ·
                    refine ⟨274972827167707735024747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1466521744894441253465317 274972827167707735024747)
                    ·
                      rfl

theorem cell23_1606523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6, 4].length) (baseStart_1606523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606523 prefixEnd_1606523 := by exact prefixLift 1606523
  have htrace : WordTrace (prefixWord ++ tailWord_1606523) baseStart_1606523 baseEnd_1606523 := by
    simpa [prefixWord, tailWord_1606523, baseEnd_1606523] using wordTrace_append hprefix tailTrace_1606523
  have hstable : (prefixWord ++ tailWord_1606523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606523).length < 2 ^ (prefixWord ++ tailWord_1606523).sum := by decide
  have hdescent : baseEnd_1606523 < baseStart_1606523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606540 : List Nat := [2, 2, 1, 2, 1, 2, 3, 4, 2, 4]
def baseStart_1606540 : Nat := 118140960795 + 1606540 * 2 ^ 59
def prefixEnd_1606540 : Nat := 4983230072969 + 3 ^ 40 * 1606540 * 2
def baseEnd_1606540 : Nat := 274975736891416546187221

theorem tailTrace_1606540 : CollatzResearch.WordTrace tailWord_1606540 prefixEnd_1606540 274975736891416546187221 := by
  unfold tailWord_1606540
  simp only [CollatzResearch.WordTrace]
  refine ⟨29297663799893715016492537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39063551733191620021990049 29297663799893715016492537)
  ·
    refine ⟨21973247849920286262369403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29297663799893715016492537 21973247849920286262369403)
    ·
      refine ⟨32959871774880429393554105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21973247849920286262369403 32959871774880429393554105)
      ·
        refine ⟨24719903831160322045165579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32959871774880429393554105 24719903831160322045165579)
        ·
          refine ⟨37079855746740483067748369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24719903831160322045165579 37079855746740483067748369)
          ·
            refine ⟨27809891810055362300811277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37079855746740483067748369 27809891810055362300811277)
            ·
              refine ⟨10428709428770760862804229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27809891810055362300811277 10428709428770760862804229)
              ·
                refine ⟨1955383017894517661775793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10428709428770760862804229 1955383017894517661775793)
                ·
                  refine ⟨1466537263420888246331845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1955383017894517661775793 1466537263420888246331845)
                  ·
                    refine ⟨274975736891416546187221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1466537263420888246331845 274975736891416546187221)
                    ·
                      rfl

theorem cell23_1606540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 2, 4].length) (baseStart_1606540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606540 prefixEnd_1606540 := by exact prefixLift 1606540
  have htrace : WordTrace (prefixWord ++ tailWord_1606540) baseStart_1606540 baseEnd_1606540 := by
    simpa [prefixWord, tailWord_1606540, baseEnd_1606540] using wordTrace_append hprefix tailTrace_1606540
  have hstable : (prefixWord ++ tailWord_1606540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606540).length < 2 ^ (prefixWord ++ tailWord_1606540).sum := by decide
  have hdescent : baseEnd_1606540 < baseStart_1606540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606581 : List Nat := [1, 3, 3, 2, 1, 1, 4, 3, 1, 2, 2]
def baseStart_1606581 : Nat := 118140960795 + 1606581 * 2 ^ 59
def prefixEnd_1606581 : Nat := 4983230072969 + 3 ^ 40 * 1606581 * 2
def baseEnd_1606581 : Nat := 824948263381083978148975

theorem tailTrace_1606581 : CollatzResearch.WordTrace tailWord_1606581 prefixEnd_1606581 824948263381083978148975 := by
  unfold tailWord_1606581
  simp only [CollatzResearch.WordTrace]
  refine ⟨58596822992638894035227597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39064548661759262690151731 58596822992638894035227597)
  ·
    refine ⟨21973808622239585263210349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58596822992638894035227597 21973808622239585263210349)
    ·
      refine ⟨8240178233339844473703881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21973808622239585263210349 8240178233339844473703881)
      ·
        refine ⟨6180133675004883355277911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8240178233339844473703881 6180133675004883355277911)
        ·
          refine ⟨9270200512507325032916867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6180133675004883355277911 9270200512507325032916867)
          ·
            refine ⟨13905300768760987549375301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9270200512507325032916867 13905300768760987549375301)
            ·
              refine ⟨2607243894142685165507869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13905300768760987549375301 2607243894142685165507869)
              ·
                refine ⟨977716460303506937065451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2607243894142685165507869 977716460303506937065451)
                ·
                  refine ⟨1466574690455260405598177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 977716460303506937065451 1466574690455260405598177)
                  ·
                    refine ⟨1099931017841445304198633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1466574690455260405598177 1099931017841445304198633)
                    ·
                      refine ⟨824948263381083978148975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1099931017841445304198633 824948263381083978148975)
                      ·
                        rfl

theorem cell23_1606581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_1606581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606581 prefixEnd_1606581 := by exact prefixLift 1606581
  have htrace : WordTrace (prefixWord ++ tailWord_1606581) baseStart_1606581 baseEnd_1606581 := by
    simpa [prefixWord, tailWord_1606581, baseEnd_1606581] using wordTrace_append hprefix tailTrace_1606581
  have hstable : (prefixWord ++ tailWord_1606581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606581).length < 2 ^ (prefixWord ++ tailWord_1606581).sum := by decide
  have hdescent : baseEnd_1606581 < baseStart_1606581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606584 : List Nat := [2, 1, 2, 1, 2, 6, 2, 1, 1, 2, 3]
def baseStart_1606584 : Nat := 118140960795 + 1606584 * 2 ^ 59
def prefixEnd_1606584 : Nat := 4983230072969 + 3 ^ 40 * 1606584 * 2
def baseEnd_1606584 : Nat := 824949803823047466411461

theorem tailTrace_1606584 : CollatzResearch.WordTrace tailWord_1606584 prefixEnd_1606584 824949803823047466411461 := by
  unfold tailWord_1606584
  simp only [CollatzResearch.WordTrace]
  refine ⟨29298466205814012773793403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39064621607752017031724537 29298466205814012773793403)
  ·
    refine ⟨43947699308721019160690105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29298466205814012773793403 43947699308721019160690105)
    ·
      refine ⟨32960774481540764370517579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43947699308721019160690105 32960774481540764370517579)
      ·
        refine ⟨49441161722311146555776369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32960774481540764370517579 49441161722311146555776369)
        ·
          refine ⟨37080871291733359916832277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49441161722311146555776369 37080871291733359916832277)
          ·
            refine ⟨1738165841800001246101513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37080871291733359916832277 1738165841800001246101513)
            ·
              refine ⟨1303624381350000934576135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1738165841800001246101513 1303624381350000934576135)
              ·
                refine ⟨1955436572025001401864203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303624381350000934576135 1955436572025001401864203)
                ·
                  refine ⟨2933154858037502102796305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1955436572025001401864203 2933154858037502102796305)
                  ·
                    refine ⟨2199866143528126577097229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2933154858037502102796305 2199866143528126577097229)
                    ·
                      refine ⟨824949803823047466411461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2199866143528126577097229 824949803823047466411461)
                      ·
                        rfl

theorem cell23_1606584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 1, 2, 3].length) (baseStart_1606584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606584 prefixEnd_1606584 := by exact prefixLift 1606584
  have htrace : WordTrace (prefixWord ++ tailWord_1606584) baseStart_1606584 baseEnd_1606584 := by
    simpa [prefixWord, tailWord_1606584, baseEnd_1606584] using wordTrace_append hprefix tailTrace_1606584
  have hstable : (prefixWord ++ tailWord_1606584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606584).length < 2 ^ (prefixWord ++ tailWord_1606584).sum := by decide
  have hdescent : baseEnd_1606584 < baseStart_1606584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606614 : List Nat := [5, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_1606614 : Nat := 118140960795 + 1606614 * 2 ^ 59
def prefixEnd_1606614 : Nat := 4983230072969 + 3 ^ 40 * 1606614 * 2
def baseEnd_1606614 : Nat := 824965208242682349036323

theorem tailTrace_1606614 : CollatzResearch.WordTrace tailWord_1606614 prefixEnd_1606614 824965208242682349036323 := by
  unfold tailWord_1606614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3662376662594958791948681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39065351067679560447452597 3662376662594958791948681)
  ·
    refine ⟨2746782496946219093961511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3662376662594958791948681 2746782496946219093961511)
    ·
      refine ⟨4120173745419328640942267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2746782496946219093961511 4120173745419328640942267)
      ·
        refine ⟨6180260618128992961413401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4120173745419328640942267 6180260618128992961413401)
        ·
          refine ⟨4635195463596744721060051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6180260618128992961413401 4635195463596744721060051)
          ·
            refine ⟨6952793195395117081590077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4635195463596744721060051 6952793195395117081590077)
            ·
              refine ⟨2607297448273168905596279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6952793195395117081590077 2607297448273168905596279)
              ·
                refine ⟨3910946172409753358394419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2607297448273168905596279 3910946172409753358394419)
                ·
                  refine ⟨5866419258614630037591629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3910946172409753358394419 5866419258614630037591629)
                  ·
                    refine ⟨2199907221980486264096861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5866419258614630037591629 2199907221980486264096861)
                    ·
                      refine ⟨824965208242682349036323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2199907221980486264096861 824965208242682349036323)
                      ·
                        rfl

theorem cell23_1606614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_1606614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606614 prefixEnd_1606614 := by exact prefixLift 1606614
  have htrace : WordTrace (prefixWord ++ tailWord_1606614) baseStart_1606614 baseEnd_1606614 := by
    simpa [prefixWord, tailWord_1606614, baseEnd_1606614] using wordTrace_append hprefix tailTrace_1606614
  have hstable : (prefixWord ++ tailWord_1606614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606614).length < 2 ^ (prefixWord ++ tailWord_1606614).sum := by decide
  have hdescent : baseEnd_1606614 < baseStart_1606614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606653 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_1606653 : Nat := 118140960795 + 1606653 * 2 ^ 59
def prefixEnd_1606653 : Nat := 4983230072969 + 3 ^ 40 * 1606653 * 2
def baseEnd_1606653 : Nat := 824985233988207696448643

theorem tailTrace_1606653 : CollatzResearch.WordTrace tailWord_1606653 prefixEnd_1606653 824985233988207696448643 := by
  unfold tailWord_1606653
  simp only [CollatzResearch.WordTrace]
  refine ⟨58599449048378050331848613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39066299365585366887899075 58599449048378050331848613)
  ·
    refine ⟨10987396696570884437221615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58599449048378050331848613 10987396696570884437221615)
    ·
      refine ⟨16481095044856326655832423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10987396696570884437221615 16481095044856326655832423)
      ·
        refine ⟨24721642567284489983748635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16481095044856326655832423 24721642567284489983748635)
        ·
          refine ⟨37082463850926734975622953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24721642567284489983748635 37082463850926734975622953)
          ·
            refine ⟨27811847888195051231717215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37082463850926734975622953 27811847888195051231717215)
            ·
              refine ⟨41717771832292576847575823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27811847888195051231717215 41717771832292576847575823)
              ·
                refine ⟨62576657748438865271363735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41717771832292576847575823 62576657748438865271363735)
                ·
                  refine ⟨93864986622658297907045603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62576657748438865271363735 93864986622658297907045603)
                  ·
                    refine ⟨140797479933987446860568405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93864986622658297907045603 140797479933987446860568405)
                    ·
                      refine ⟨824985233988207696448643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 140797479933987446860568405 824985233988207696448643)
                      ·
                        rfl

theorem cell23_1606653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_1606653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606653 prefixEnd_1606653 := by exact prefixLift 1606653
  have htrace : WordTrace (prefixWord ++ tailWord_1606653) baseStart_1606653 baseEnd_1606653 := by
    simpa [prefixWord, tailWord_1606653, baseEnd_1606653] using wordTrace_append hprefix tailTrace_1606653
  have hstable : (prefixWord ++ tailWord_1606653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606653).length < 2 ^ (prefixWord ++ tailWord_1606653).sum := by decide
  have hdescent : baseEnd_1606653 < baseStart_1606653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606673 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 3, 7]
def baseStart_1606673 : Nat := 118140960795 + 1606673 * 2 ^ 59
def prefixEnd_1606673 : Nat := 4983230072969 + 3 ^ 40 * 1606673 * 2
def baseEnd_1606673 : Nat := 274998501200432539399517

theorem tailTrace_1606673 : CollatzResearch.WordTrace tailWord_1606673 prefixEnd_1606673 274998501200432539399517 := by
  unfold tailWord_1606673
  simp only [CollatzResearch.WordTrace]
  refine ⟨58600178508305593747576673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39066785672203729165051115 58600178508305593747576673)
  ·
    refine ⟨43950133881229195310682505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58600178508305593747576673 43950133881229195310682505)
    ·
      refine ⟨32962600410921896483011879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43950133881229195310682505 32962600410921896483011879)
      ·
        refine ⟨49443900616382844724517819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32962600410921896483011879 49443900616382844724517819)
        ·
          refine ⟨74165850924574267086776729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49443900616382844724517819 74165850924574267086776729)
          ·
            refine ⟨55624388193430700315082547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74165850924574267086776729 55624388193430700315082547)
            ·
              refine ⟨83436582290146050472623821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55624388193430700315082547 83436582290146050472623821)
              ·
                refine ⟨31288718358804768927233933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83436582290146050472623821 31288718358804768927233933)
                ·
                  refine ⟨11733269384551788347712725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31288718358804768927233933 11733269384551788347712725)
                  ·
                    refine ⟨274998501200432539399517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11733269384551788347712725 274998501200432539399517)
                    ·
                      rfl

theorem cell23_1606673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_1606673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606673 prefixEnd_1606673 := by exact prefixLift 1606673
  have htrace : WordTrace (prefixWord ++ tailWord_1606673) baseStart_1606673 baseEnd_1606673 := by
    simpa [prefixWord, tailWord_1606673, baseEnd_1606673] using wordTrace_append hprefix tailTrace_1606673
  have hstable : (prefixWord ++ tailWord_1606673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606673).length < 2 ^ (prefixWord ++ tailWord_1606673).sum := by decide
  have hdescent : baseEnd_1606673 < baseStart_1606673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606703 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 4, 8]
def baseStart_1606703 : Nat := 118140960795 + 1606703 * 2 ^ 59
def prefixEnd_1606703 : Nat := 4983230072969 + 3 ^ 40 * 1606703 * 2
def baseEnd_1606703 : Nat := 275003636006977500274471

theorem tailTrace_1606703 : CollatzResearch.WordTrace tailWord_1606703 prefixEnd_1606703 275003636006977500274471 := by
  unfold tailWord_1606703
  simp only [CollatzResearch.WordTrace]
  refine ⟨58601272698196908871168763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39067515132131272580779175 58601272698196908871168763)
  ·
    refine ⟨87901909047295363306753145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58601272698196908871168763 87901909047295363306753145)
    ·
      refine ⟨65926431785471522480064859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87901909047295363306753145 65926431785471522480064859)
      ·
        refine ⟨98889647678207283720097289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65926431785471522480064859 98889647678207283720097289)
        ·
          refine ⟨74167235758655462790072967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98889647678207283720097289 74167235758655462790072967)
          ·
            refine ⟨111250853637983194185109451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74167235758655462790072967 111250853637983194185109451)
            ·
              refine ⟨166876280456974791277664177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111250853637983194185109451 166876280456974791277664177)
              ·
                refine ⟨125157210342731093458248133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166876280456974791277664177 125157210342731093458248133)
                ·
                  refine ⟨23466976939262080023421525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125157210342731093458248133 23466976939262080023421525)
                  ·
                    refine ⟨275003636006977500274471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23466976939262080023421525 275003636006977500274471)
                    ·
                      rfl

theorem cell23_1606703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 8].length) (baseStart_1606703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606703 prefixEnd_1606703 := by exact prefixLift 1606703
  have htrace : WordTrace (prefixWord ++ tailWord_1606703) baseStart_1606703 baseEnd_1606703 := by
    simpa [prefixWord, tailWord_1606703, baseEnd_1606703] using wordTrace_append hprefix tailTrace_1606703
  have hstable : (prefixWord ++ tailWord_1606703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606703).length < 2 ^ (prefixWord ++ tailWord_1606703).sum := by decide
  have hdescent : baseEnd_1606703 < baseStart_1606703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606727 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 1, 6, 2]
def baseStart_1606727 : Nat := 118140960795 + 1606727 * 2 ^ 59
def prefixEnd_1606727 : Nat := 4983230072969 + 3 ^ 40 * 1606727 * 2
def baseEnd_1606727 : Nat := 825023231556640406923303

theorem tailTrace_1606727 : CollatzResearch.WordTrace tailWord_1606727 prefixEnd_1606727 825023231556640406923303 := by
  unfold tailWord_1606727
  simp only [CollatzResearch.WordTrace]
  refine ⟨58602148050109960970042435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39068098700073307313361623 58602148050109960970042435)
  ·
    refine ⟨87903222075164941455063653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58602148050109960970042435 87903222075164941455063653)
    ·
      refine ⟨16481854139093426522824435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87903222075164941455063653 16481854139093426522824435)
      ·
        refine ⟨24722781208640139784236653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16481854139093426522824435 24722781208640139784236653)
        ·
          refine ⟨9271042953240052419088745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24722781208640139784236653 9271042953240052419088745)
          ·
            refine ⟨6953282214930039314316559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9271042953240052419088745 6953282214930039314316559)
            ·
              refine ⟨10429923322395058971474839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6953282214930039314316559 10429923322395058971474839)
              ·
                refine ⟨15644884983592588457212259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10429923322395058971474839 15644884983592588457212259)
                ·
                  refine ⟨23467327475388882685818389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15644884983592588457212259 23467327475388882685818389)
                  ·
                    refine ⟨1100030975408853875897737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23467327475388882685818389 1100030975408853875897737)
                    ·
                      refine ⟨825023231556640406923303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1100030975408853875897737 825023231556640406923303)
                      ·
                        rfl

theorem cell23_1606727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_1606727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606727 prefixEnd_1606727 := by exact prefixLift 1606727
  have htrace : WordTrace (prefixWord ++ tailWord_1606727) baseStart_1606727 baseEnd_1606727 := by
    simpa [prefixWord, tailWord_1606727, baseEnd_1606727] using wordTrace_append hprefix tailTrace_1606727
  have hstable : (prefixWord ++ tailWord_1606727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606727).length < 2 ^ (prefixWord ++ tailWord_1606727).sum := by decide
  have hdescent : baseEnd_1606727 < baseStart_1606727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606770 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_1606770 : Nat := 118140960795 + 1606770 * 2 ^ 59
def prefixEnd_1606770 : Nat := 4983230072969 + 3 ^ 40 * 1606770 * 2
def baseEnd_1606770 : Nat := 825045311224783738685605

theorem tailTrace_1606770 : CollatzResearch.WordTrace tailWord_1606770 prefixEnd_1606770 825045311224783738685605 := by
  unfold tailWord_1606770
  simp only [CollatzResearch.WordTrace]
  refine ⟨14650929097238544828464441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39069144259302786209238509 14650929097238544828464441)
  ·
    refine ⟨10988196822928908621348331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14650929097238544828464441 10988196822928908621348331)
    ·
      refine ⟨16482295234393362932022497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10988196822928908621348331 16482295234393362932022497)
      ·
        refine ⟨12361721425795022199016873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16482295234393362932022497 12361721425795022199016873)
        ·
          refine ⟨9271291069346266649262655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12361721425795022199016873 9271291069346266649262655)
          ·
            refine ⟨13906936604019399973893983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9271291069346266649262655 13906936604019399973893983)
            ·
              refine ⟨20860404906029099960840975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13906936604019399973893983 20860404906029099960840975)
              ·
                refine ⟨31290607359043649941261463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20860404906029099960840975 31290607359043649941261463)
                ·
                  refine ⟨46935911038565474911892195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31290607359043649941261463 46935911038565474911892195)
                  ·
                    refine ⟨70403866557848212367838293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46935911038565474911892195 70403866557848212367838293)
                    ·
                      refine ⟨825045311224783738685605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 70403866557848212367838293 825045311224783738685605)
                      ·
                        rfl

theorem cell23_1606770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_1606770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606770 prefixEnd_1606770 := by exact prefixLift 1606770
  have htrace : WordTrace (prefixWord ++ tailWord_1606770) baseStart_1606770 baseEnd_1606770 := by
    simpa [prefixWord, tailWord_1606770, baseEnd_1606770] using wordTrace_append hprefix tailTrace_1606770
  have hstable : (prefixWord ++ tailWord_1606770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606770).length < 2 ^ (prefixWord ++ tailWord_1606770).sum := by decide
  have hdescent : baseEnd_1606770 < baseStart_1606770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606787 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 3, 5, 2]
def baseStart_1606787 : Nat := 118140960795 + 1606787 * 2 ^ 59
def prefixEnd_1606787 : Nat := 4983230072969 + 3 ^ 40 * 1606787 * 2
def baseEnd_1606787 : Nat := 825054040395910172173027

theorem tailTrace_1606787 : CollatzResearch.WordTrace tailWord_1606787 prefixEnd_1606787 825054040395910172173027 := by
  unfold tailWord_1606787
  simp only [CollatzResearch.WordTrace]
  refine ⟨58604336429892591217226615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39069557619928394144817743 58604336429892591217226615)
  ·
    refine ⟨87906504644838886825839923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58604336429892591217226615 87906504644838886825839923)
    ·
      refine ⟨131859756967258330238759885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87906504644838886825839923 131859756967258330238759885)
      ·
        refine ⟨49447408862721873839534957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131859756967258330238759885 49447408862721873839534957)
        ·
          refine ⟨18542778323520702689825609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49447408862721873839534957 18542778323520702689825609)
          ·
            refine ⟨13907083742640527017369207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18542778323520702689825609 13907083742640527017369207)
            ·
              refine ⟨20860625613960790526053811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13907083742640527017369207 20860625613960790526053811)
              ·
                refine ⟨31290938420941185789080717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20860625613960790526053811 31290938420941185789080717)
                ·
                  refine ⟨11734101907852944670905269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31290938420941185789080717 11734101907852944670905269)
                  ·
                    refine ⟨1100072053861213562897369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11734101907852944670905269 1100072053861213562897369)
                    ·
                      refine ⟨825054040395910172173027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1100072053861213562897369 825054040395910172173027)
                      ·
                        rfl

theorem cell23_1606787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 5, 2].length) (baseStart_1606787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606787 prefixEnd_1606787 := by exact prefixLift 1606787
  have htrace : WordTrace (prefixWord ++ tailWord_1606787) baseStart_1606787 baseEnd_1606787 := by
    simpa [prefixWord, tailWord_1606787, baseEnd_1606787] using wordTrace_append hprefix tailTrace_1606787
  have hstable : (prefixWord ++ tailWord_1606787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606787).length < 2 ^ (prefixWord ++ tailWord_1606787).sum := by decide
  have hdescent : baseEnd_1606787 < baseStart_1606787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606794 : List Nat := [3, 1, 2, 3, 1, 1, 1, 4, 3, 1, 3]
def baseStart_1606794 : Nat := 118140960795 + 1606794 * 2 ^ 59
def prefixEnd_1606794 : Nat := 4983230072969 + 3 ^ 40 * 1606794 * 2
def baseEnd_1606794 : Nat := 825057634760491644785495

theorem tailTrace_1606794 : CollatzResearch.WordTrace tailWord_1606794 prefixEnd_1606794 825057634760491644785495 := by
  unfold tailWord_1606794
  simp only [CollatzResearch.WordTrace]
  refine ⟨14651147935216807853182859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39069727827244820941820957 14651147935216807853182859)
  ·
    refine ⟨21976721902825211779774289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14651147935216807853182859 21976721902825211779774289)
    ·
      refine ⟨16482541427118908834830717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21976721902825211779774289 16482541427118908834830717)
      ·
        refine ⟨6180953035169590813061519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16482541427118908834830717 6180953035169590813061519)
        ·
          refine ⟨9271429552754386219592279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6180953035169590813061519 9271429552754386219592279)
          ·
            refine ⟨13907144329131579329388419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9271429552754386219592279 13907144329131579329388419)
            ·
              refine ⟨20860716493697368994082629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13907144329131579329388419 20860716493697368994082629)
              ·
                refine ⟨3911384342568256686390493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20860716493697368994082629 3911384342568256686390493)
                ·
                  refine ⟨1466769128463096257396435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3911384342568256686390493 1466769128463096257396435)
                  ·
                    refine ⟨2200153692694644386094653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1466769128463096257396435 2200153692694644386094653)
                    ·
                      refine ⟨825057634760491644785495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2200153692694644386094653 825057634760491644785495)
                      ·
                        rfl

theorem cell23_1606794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_1606794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606794 prefixEnd_1606794 := by exact prefixLift 1606794
  have htrace : WordTrace (prefixWord ++ tailWord_1606794) baseStart_1606794 baseEnd_1606794 := by
    simpa [prefixWord, tailWord_1606794, baseEnd_1606794] using wordTrace_append hprefix tailTrace_1606794
  have hstable : (prefixWord ++ tailWord_1606794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606794).length < 2 ^ (prefixWord ++ tailWord_1606794).sum := by decide
  have hdescent : baseEnd_1606794 < baseStart_1606794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606867 : List Nat := [1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 3]
def baseStart_1606867 : Nat := 118140960795 + 1606867 * 2 ^ 59
def prefixEnd_1606867 : Nat := 4983230072969 + 3 ^ 40 * 1606867 * 2
def baseEnd_1606867 : Nat := 825095118848269859172659

theorem tailTrace_1606867 : CollatzResearch.WordTrace tailWord_1606867 prefixEnd_1606867 825095118848269859172659 := by
  unfold tailWord_1606867
  simp only [CollatzResearch.WordTrace]
  refine ⟨58607254269602764880138855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39071502846401843253425903 58607254269602764880138855)
  ·
    refine ⟨87910881404404147320208283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58607254269602764880138855 87910881404404147320208283)
    ·
      refine ⟨131866322106606220980312425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87910881404404147320208283 131866322106606220980312425)
      ·
        refine ⟨98899741579954665735234319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131866322106606220980312425 98899741579954665735234319)
        ·
          refine ⟨148349612369931998602851479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98899741579954665735234319 148349612369931998602851479)
          ·
            refine ⟨222524418554897997904277219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148349612369931998602851479 222524418554897997904277219)
            ·
              refine ⟨333786627832346996856415829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222524418554897997904277219 333786627832346996856415829)
              ·
                refine ⟨3911562044910316369411123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 333786627832346996856415829 3911562044910316369411123)
                ·
                  refine ⟨5867343067365474554116685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3911562044910316369411123 5867343067365474554116685)
                  ·
                    refine ⟨2200253650262052957793757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5867343067365474554116685 2200253650262052957793757)
                    ·
                      refine ⟨825095118848269859172659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2200253650262052957793757 825095118848269859172659)
                      ·
                        rfl

theorem cell23_1606867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 3].length) (baseStart_1606867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606867 prefixEnd_1606867 := by exact prefixLift 1606867
  have htrace : WordTrace (prefixWord ++ tailWord_1606867) baseStart_1606867 baseEnd_1606867 := by
    simpa [prefixWord, tailWord_1606867, baseEnd_1606867] using wordTrace_append hprefix tailTrace_1606867
  have hstable : (prefixWord ++ tailWord_1606867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606867).length < 2 ^ (prefixWord ++ tailWord_1606867).sum := by decide
  have hdescent : baseEnd_1606867 < baseStart_1606867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606884 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 4, 1, 3]
def baseStart_1606884 : Nat := 118140960795 + 1606884 * 2 ^ 59
def prefixEnd_1606884 : Nat := 4983230072969 + 3 ^ 40 * 1606884 * 2
def baseEnd_1606884 : Nat := 825103848019396292660081

theorem tailTrace_1606884 : CollatzResearch.WordTrace tailWord_1606884 prefixEnd_1606884 825103848019396292660081 := by
  unfold tailWord_1606884
  simp only [CollatzResearch.WordTrace]
  refine ⟨29303937155270588391753853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39071916207027451189005137 29303937155270588391753853)
  ·
    refine ⟨10988976433226470646907695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29303937155270588391753853 10988976433226470646907695)
    ·
      refine ⟨16483464649839705970361543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10988976433226470646907695 16483464649839705970361543)
      ·
        refine ⟨24725196974759558955542315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16483464649839705970361543 24725196974759558955542315)
        ·
          refine ⟨37087795462139338433313473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24725196974759558955542315 37087795462139338433313473)
          ·
            refine ⟨27815846596604503824985105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37087795462139338433313473 27815846596604503824985105)
            ·
              refine ⟨20861884947453377868738829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27815846596604503824985105 20861884947453377868738829)
              ·
                refine ⟨7823206855295016700777061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20861884947453377868738829 7823206855295016700777061)
                ·
                  refine ⟨1466851285367815631395699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7823206855295016700777061 1466851285367815631395699)
                  ·
                    refine ⟨2200276928051723447093549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1466851285367815631395699 2200276928051723447093549)
                    ·
                      refine ⟨825103848019396292660081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2200276928051723447093549 825103848019396292660081)
                      ·
                        rfl

theorem cell23_1606884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_1606884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606884 prefixEnd_1606884 := by exact prefixLift 1606884
  have htrace : WordTrace (prefixWord ++ tailWord_1606884) baseStart_1606884 baseEnd_1606884 := by
    simpa [prefixWord, tailWord_1606884, baseEnd_1606884] using wordTrace_append hprefix tailTrace_1606884
  have hstable : (prefixWord ++ tailWord_1606884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606884).length < 2 ^ (prefixWord ++ tailWord_1606884).sum := by decide
  have hdescent : baseEnd_1606884 < baseStart_1606884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606885 : List Nat := [1, 3, 1, 4, 3, 1, 1, 4, 1, 2, 2]
def baseStart_1606885 : Nat := 118140960795 + 1606885 * 2 ^ 59
def prefixEnd_1606885 : Nat := 4983230072969 + 3 ^ 40 * 1606885 * 2
def baseEnd_1606885 : Nat := 825104361500050788747577

theorem tailTrace_1606885 : CollatzResearch.WordTrace tailWord_1606885 prefixEnd_1606885 825104361500050788747577 := by
  unfold tailWord_1606885
  simp only [CollatzResearch.WordTrace]
  refine ⟨58607910783537553954294109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39071940522358369302862739 58607910783537553954294109)
  ·
    refine ⟨21977966543826582732860291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58607910783537553954294109 21977966543826582732860291)
    ·
      refine ⟨32966949815739874099290437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21977966543826582732860291 32966949815739874099290437)
      ·
        refine ⟨6181303090451226393616957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32966949815739874099290437 6181303090451226393616957)
        ·
          refine ⟨2317988658919209897606359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6181303090451226393616957 2317988658919209897606359)
          ·
            refine ⟨3476982988378814846409539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2317988658919209897606359 3476982988378814846409539)
            ·
              refine ⟨5215474482568222269614309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3476982988378814846409539 5215474482568222269614309)
              ·
                refine ⟨977901465481541675552683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5215474482568222269614309 977901465481541675552683)
                ·
                  refine ⟨1466852198222312513329025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 977901465481541675552683 1466852198222312513329025)
                  ·
                    refine ⟨1100139148666734384996769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1466852198222312513329025 1100139148666734384996769)
                    ·
                      refine ⟨825104361500050788747577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1100139148666734384996769 825104361500050788747577)
                      ·
                        rfl

theorem cell23_1606885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_1606885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606885 prefixEnd_1606885 := by exact prefixLift 1606885
  have htrace : WordTrace (prefixWord ++ tailWord_1606885) baseStart_1606885 baseEnd_1606885 := by
    simpa [prefixWord, tailWord_1606885, baseEnd_1606885] using wordTrace_append hprefix tailTrace_1606885
  have hstable : (prefixWord ++ tailWord_1606885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606885).length < 2 ^ (prefixWord ++ tailWord_1606885).sum := by decide
  have hdescent : baseEnd_1606885 < baseStart_1606885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606947 : List Nat := [1, 1, 1, 4, 2, 3, 1, 3, 7]
def baseStart_1606947 : Nat := 118140960795 + 1606947 * 2 ^ 59
def prefixEnd_1606947 : Nat := 4983230072969 + 3 ^ 40 * 1606947 * 2
def baseEnd_1606947 : Nat := 91681799700069949574699

theorem tailTrace_1606947 : CollatzResearch.WordTrace tailWord_1606947 prefixEnd_1606947 91681799700069949574699 := by
  unfold tailWord_1606947
  simp only [CollatzResearch.WordTrace]
  refine ⟨58610172109312938543051095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39073448072875292362034063 58610172109312938543051095)
  ·
    refine ⟨87915258163969407814576643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58610172109312938543051095 87915258163969407814576643)
    ·
      refine ⟨131872887245954111721864965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87915258163969407814576643 131872887245954111721864965)
      ·
        refine ⟨24726166358616395947849681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131872887245954111721864965 24726166358616395947849681)
        ·
          refine ⟨18544624768962296960887261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24726166358616395947849681 18544624768962296960887261)
          ·
            refine ⟨6954234288360861360332723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18544624768962296960887261 6954234288360861360332723)
            ·
              refine ⟨10431351432541292040499085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6954234288360861360332723 10431351432541292040499085)
              ·
                refine ⟨3911756787202984515187157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10431351432541292040499085 3911756787202984515187157)
                ·
                  refine ⟨91681799700069949574699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3911756787202984515187157 91681799700069949574699)
                  ·
                    rfl

theorem cell23_1606947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 7].length) (baseStart_1606947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606947 prefixEnd_1606947 := by exact prefixLift 1606947
  have htrace : WordTrace (prefixWord ++ tailWord_1606947) baseStart_1606947 baseEnd_1606947 := by
    simpa [prefixWord, tailWord_1606947, baseEnd_1606947] using wordTrace_append hprefix tailTrace_1606947
  have hstable : (prefixWord ++ tailWord_1606947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606947).length < 2 ^ (prefixWord ++ tailWord_1606947).sum := by decide
  have hdescent : baseEnd_1606947 < baseStart_1606947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606964 : List Nat := [2, 5, 1, 1, 1, 1, 1, 4, 7]
def baseStart_1606964 : Nat := 118140960795 + 1606964 * 2 ^ 59
def prefixEnd_1606964 : Nat := 4983230072969 + 3 ^ 40 * 1606964 * 2
def baseEnd_1606964 : Nat := 91682769607972886628857

theorem tailTrace_1606964 : CollatzResearch.WordTrace tailWord_1606964 prefixEnd_1606964 91682769607972886628857 := by
  unfold tailWord_1606964
  simp only [CollatzResearch.WordTrace]
  refine ⟨29305396075125675223209973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39073861433500900297613297 29305396075125675223209973)
  ·
    refine ⟨2747380882043032052175935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29305396075125675223209973 2747380882043032052175935)
    ·
      refine ⟨4121071323064548078263903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2747380882043032052175935 4121071323064548078263903)
      ·
        refine ⟨6181606984596822117395855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4121071323064548078263903 6181606984596822117395855)
        ·
          refine ⟨9272410476895233176093783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6181606984596822117395855 9272410476895233176093783)
          ·
            refine ⟨13908615715342849764140675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9272410476895233176093783 13908615715342849764140675)
            ·
              refine ⟨20862923573014274646211013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13908615715342849764140675 20862923573014274646211013)
              ·
                refine ⟨3911798169940176496164565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20862923573014274646211013 3911798169940176496164565)
                ·
                  refine ⟨91682769607972886628857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3911798169940176496164565 91682769607972886628857)
                  ·
                    rfl

theorem cell23_1606964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_1606964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606964 prefixEnd_1606964 := by exact prefixLift 1606964
  have htrace : WordTrace (prefixWord ++ tailWord_1606964) baseStart_1606964 baseEnd_1606964 := by
    simpa [prefixWord, tailWord_1606964, baseEnd_1606964] using wordTrace_append hprefix tailTrace_1606964
  have hstable : (prefixWord ++ tailWord_1606964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606964).length < 2 ^ (prefixWord ++ tailWord_1606964).sum := by decide
  have hdescent : baseEnd_1606964 < baseStart_1606964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606984 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 1, 7, 2]
def baseStart_1606984 : Nat := 118140960795 + 1606984 * 2 ^ 59
def prefixEnd_1606984 : Nat := 4983230072969 + 3 ^ 40 * 1606984 * 2
def baseEnd_1606984 : Nat := 825155196084845901409621

theorem tailTrace_1606984 : CollatzResearch.WordTrace tailWord_1606984 prefixEnd_1606984 825155196084845901409621 := by
  unfold tailWord_1606984
  simp only [CollatzResearch.WordTrace]
  refine ⟨29305760805089446931074003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39074347740119262574765337 29305760805089446931074003)
  ·
    refine ⟨43958641207634170396611005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29305760805089446931074003 43958641207634170396611005)
    ·
      refine ⟨16484490452862813898729127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43958641207634170396611005 16484490452862813898729127)
      ·
        refine ⟨24726735679294220848093691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16484490452862813898729127 24726735679294220848093691)
        ·
          refine ⟨37090103518941331272140537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24726735679294220848093691 37090103518941331272140537)
          ·
            refine ⟨27817577639205998454105403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37090103518941331272140537 27817577639205998454105403)
            ·
              refine ⟨41726366458808997681158105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27817577639205998454105403 41726366458808997681158105)
              ·
                refine ⟨31294774844106748260868579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41726366458808997681158105 31294774844106748260868579)
                ·
                  refine ⟨46942162266160122391302869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31294774844106748260868579 46942162266160122391302869)
                  ·
                    refine ⟨1100206928113127868546161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46942162266160122391302869 1100206928113127868546161)
                    ·
                      refine ⟨825155196084845901409621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1100206928113127868546161 825155196084845901409621)
                      ·
                        rfl

theorem cell23_1606984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_1606984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1606984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1606984 prefixEnd_1606984 := by exact prefixLift 1606984
  have htrace : WordTrace (prefixWord ++ tailWord_1606984) baseStart_1606984 baseEnd_1606984 := by
    simpa [prefixWord, tailWord_1606984, baseEnd_1606984] using wordTrace_append hprefix tailTrace_1606984
  have hstable : (prefixWord ++ tailWord_1606984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606984).length < 2 ^ (prefixWord ++ tailWord_1606984).sum := by decide
  have hdescent : baseEnd_1606984 < baseStart_1606984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607024 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 5, 4]
def baseStart_1607024 : Nat := 118140960795 + 1607024 * 2 ^ 59
def prefixEnd_1607024 : Nat := 4983230072969 + 3 ^ 40 * 1607024 * 2
def baseEnd_1607024 : Nat := 275058578437008581636479

theorem tailTrace_1607024 : CollatzResearch.WordTrace tailWord_1607024 prefixEnd_1607024 275058578437008581636479 := by
  unfold tailWord_1607024
  simp only [CollatzResearch.WordTrace]
  refine ⟨29306490265016990346802063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39075320353355987129069417 29306490265016990346802063)
  ·
    refine ⟨43959735397525485520203095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29306490265016990346802063 43959735397525485520203095)
    ·
      refine ⟨65939603096288228280304643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43959735397525485520203095 65939603096288228280304643)
      ·
        refine ⟨98909404644432342420456965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65939603096288228280304643 98909404644432342420456965)
        ·
          refine ⟨18545513370831064203835681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98909404644432342420456965 18545513370831064203835681)
          ·
            refine ⟨13909135028123298152876761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18545513370831064203835681 13909135028123298152876761)
            ·
              refine ⟨10431851271092473614657571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13909135028123298152876761 10431851271092473614657571)
              ·
                refine ⟨15647776906638710421986357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10431851271092473614657571 15647776906638710421986357)
                ·
                  refine ⟨1466979084997379102061221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15647776906638710421986357 1466979084997379102061221)
                  ·
                    refine ⟨275058578437008581636479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1466979084997379102061221 275058578437008581636479)
                    ·
                      rfl

theorem cell23_1607024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 5, 4].length) (baseStart_1607024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607024 prefixEnd_1607024 := by exact prefixLift 1607024
  have htrace : WordTrace (prefixWord ++ tailWord_1607024) baseStart_1607024 baseEnd_1607024 := by
    simpa [prefixWord, tailWord_1607024, baseEnd_1607024] using wordTrace_append hprefix tailTrace_1607024
  have hstable : (prefixWord ++ tailWord_1607024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607024).length < 2 ^ (prefixWord ++ tailWord_1607024).sum := by decide
  have hdescent : baseEnd_1607024 < baseStart_1607024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607034 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3]
def baseStart_1607034 : Nat := 118140960795 + 1607034 * 2 ^ 59
def prefixEnd_1607034 : Nat := 4983230072969 + 3 ^ 40 * 1607034 * 2
def baseEnd_1607034 : Nat := 825180870117570705784391

theorem tailTrace_1607034 : CollatzResearch.WordTrace tailWord_1607034 prefixEnd_1607034 825180870117570705784391 := by
  unfold tailWord_1607034
  simp only [CollatzResearch.WordTrace]
  refine ⟨14653336314999438100367039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39075563506665168267645437 14653336314999438100367039)
  ·
    refine ⟨21980004472499157150550559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14653336314999438100367039 21980004472499157150550559)
    ·
      refine ⟨32970006708748735725825839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21980004472499157150550559 32970006708748735725825839)
      ·
        refine ⟨49455010063123103588738759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32970006708748735725825839 49455010063123103588738759)
        ·
          refine ⟨74182515094684655383108139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49455010063123103588738759 74182515094684655383108139)
          ·
            refine ⟨111273772642026983074662209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74182515094684655383108139 111273772642026983074662209)
            ·
              refine ⟨83455329481520237305996657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111273772642026983074662209 83455329481520237305996657)
              ·
                refine ⟨62591497111140177979497493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83455329481520237305996657 62591497111140177979497493)
                ·
                  refine ⟨2933976427084695842788945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62591497111140177979497493 2933976427084695842788945)
                  ·
                    refine ⟨2200482320313521882091709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2933976427084695842788945 2200482320313521882091709)
                    ·
                      refine ⟨825180870117570705784391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2200482320313521882091709 825180870117570705784391)
                      ·
                        rfl

theorem cell23_1607034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3].length) (baseStart_1607034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607034 prefixEnd_1607034 := by exact prefixLift 1607034
  have htrace : WordTrace (prefixWord ++ tailWord_1607034) baseStart_1607034 baseEnd_1607034 := by
    simpa [prefixWord, tailWord_1607034, baseEnd_1607034] using wordTrace_append hprefix tailTrace_1607034
  have hstable : (prefixWord ++ tailWord_1607034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607034).length < 2 ^ (prefixWord ++ tailWord_1607034).sum := by decide
  have hdescent : baseEnd_1607034 < baseStart_1607034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607057 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 8]
def baseStart_1607057 : Nat := 118140960795 + 1607057 * 2 ^ 59
def prefixEnd_1607057 : Nat := 4983230072969 + 3 ^ 40 * 1607057 * 2
def baseEnd_1607057 : Nat := 825192680172624115796785

theorem tailTrace_1607057 : CollatzResearch.WordTrace tailWord_1607057 prefixEnd_1607057 825192680172624115796785 := by
  unfold tailWord_1607057
  simp only [CollatzResearch.WordTrace]
  refine ⟨58614184138914427329555425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39076122759276284886370283 58614184138914427329555425)
  ·
    refine ⟨43960638104185820497166569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58614184138914427329555425 43960638104185820497166569)
    ·
      refine ⟨32970478578139365372874927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43960638104185820497166569 32970478578139365372874927)
      ·
        refine ⟨49455717867209048059312391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32970478578139365372874927 49455717867209048059312391)
        ·
          refine ⟨74183576800813572088968587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49455717867209048059312391 74183576800813572088968587)
          ·
            refine ⟨111275365201220358133452881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74183576800813572088968587 111275365201220358133452881)
            ·
              refine ⟨83456523900915268600089661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111275365201220358133452881 83456523900915268600089661)
              ·
                refine ⟨31296196462843225725033623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83456523900915268600089661 31296196462843225725033623)
                ·
                  refine ⟨46944294694264838587550435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31296196462843225725033623 46944294694264838587550435)
                  ·
                    refine ⟨70416442041397257881325653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46944294694264838587550435 70416442041397257881325653)
                    ·
                      refine ⟨825192680172624115796785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 70416442041397257881325653 825192680172624115796785)
                      ·
                        rfl

theorem cell23_1607057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_1607057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607057 prefixEnd_1607057 := by exact prefixLift 1607057
  have htrace : WordTrace (prefixWord ++ tailWord_1607057) baseStart_1607057 baseEnd_1607057 := by
    simpa [prefixWord, tailWord_1607057, baseEnd_1607057] using wordTrace_append hprefix tailTrace_1607057
  have hstable : (prefixWord ++ tailWord_1607057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607057).length < 2 ^ (prefixWord ++ tailWord_1607057).sum := by decide
  have hdescent : baseEnd_1607057 < baseStart_1607057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607084 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 3, 5]
def baseStart_1607084 : Nat := 118140960795 + 1607084 * 2 ^ 59
def prefixEnd_1607084 : Nat := 4983230072969 + 3 ^ 40 * 1607084 * 2
def baseEnd_1607084 : Nat := 275068848050098503386387

theorem tailTrace_1607084 : CollatzResearch.WordTrace tailWord_1607084 prefixEnd_1607084 275068848050098503386387 := by
  unfold tailWord_1607084
  simp only [CollatzResearch.WordTrace]
  refine ⟨29307584454908305470394153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39076779273211073960525537 29307584454908305470394153)
  ·
    refine ⟨21980688341181229102795615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29307584454908305470394153 21980688341181229102795615)
    ·
      refine ⟨32971032511771843654193423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21980688341181229102795615 32971032511771843654193423)
      ·
        refine ⟨49456548767657765481290135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32971032511771843654193423 49456548767657765481290135)
        ·
          refine ⟨74184823151486648221935203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49456548767657765481290135 74184823151486648221935203)
          ·
            refine ⟨111277234727229972332902805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74184823151486648221935203 111277234727229972332902805)
            ·
              refine ⟨5216120377838904953104819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111277234727229972332902805 5216120377838904953104819)
              ·
                refine ⟨7824180566758357429657229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5216120377838904953104819 7824180566758357429657229)
                ·
                  refine ⟨2934067712534384036121461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7824180566758357429657229 2934067712534384036121461)
                  ·
                    refine ⟨275068848050098503386387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2934067712534384036121461 275068848050098503386387)
                    ·
                      rfl

theorem cell23_1607084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_1607084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607084 prefixEnd_1607084 := by exact prefixLift 1607084
  have htrace : WordTrace (prefixWord ++ tailWord_1607084) baseStart_1607084 baseEnd_1607084 := by
    simpa [prefixWord, tailWord_1607084, baseEnd_1607084] using wordTrace_append hprefix tailTrace_1607084
  have hstable : (prefixWord ++ tailWord_1607084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607084).length < 2 ^ (prefixWord ++ tailWord_1607084).sum := by decide
  have hdescent : baseEnd_1607084 < baseStart_1607084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607085 : List Nat := [1, 5, 2, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_1607085 : Nat := 118140960795 + 1607085 * 2 ^ 59
def prefixEnd_1607085 : Nat := 4983230072969 + 3 ^ 40 * 1607085 * 2
def baseEnd_1607085 : Nat := 825207057630950006246657

theorem tailTrace_1607085 : CollatzResearch.WordTrace tailWord_1607085 prefixEnd_1607085 825207057630950006246657 := by
  unfold tailWord_1607085
  simp only [CollatzResearch.WordTrace]
  refine ⟨58615205382812988111574709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39076803588541992074383139 58615205382812988111574709)
  ·
    refine ⟨5495175504638717635460129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58615205382812988111574709 5495175504638717635460129)
    ·
      refine ⟨4121381628479038226595097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5495175504638717635460129 4121381628479038226595097)
      ·
        refine ⟨3091036221359278669946323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4121381628479038226595097 3091036221359278669946323)
        ·
          refine ⟨4636554332038918004919485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3091036221359278669946323 4636554332038918004919485)
          ·
            refine ⟨1738707874514594251844807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4636554332038918004919485 1738707874514594251844807)
            ·
              refine ⟨2608061811771891377767211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738707874514594251844807 2608061811771891377767211)
              ·
                refine ⟨3912092717657837066650817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2608061811771891377767211 3912092717657837066650817)
                ·
                  refine ⟨2934069538243377799988113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3912092717657837066650817 2934069538243377799988113)
                  ·
                    refine ⟨2200552153682533349991085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2934069538243377799988113 2200552153682533349991085)
                    ·
                      refine ⟨825207057630950006246657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2200552153682533349991085 825207057630950006246657)
                      ·
                        rfl

theorem cell23_1607085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_1607085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607085 prefixEnd_1607085 := by exact prefixLift 1607085
  have htrace : WordTrace (prefixWord ++ tailWord_1607085) baseStart_1607085 baseEnd_1607085 := by
    simpa [prefixWord, tailWord_1607085, baseEnd_1607085] using wordTrace_append hprefix tailTrace_1607085
  have hstable : (prefixWord ++ tailWord_1607085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607085).length < 2 ^ (prefixWord ++ tailWord_1607085).sum := by decide
  have hdescent : baseEnd_1607085 < baseStart_1607085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607101 : List Nat := [1, 4, 1, 2, 2, 1, 3, 3, 1, 5]
def baseStart_1607101 : Nat := 118140960795 + 1607101 * 2 ^ 59
def prefixEnd_1607101 : Nat := 4983230072969 + 3 ^ 40 * 1607101 * 2
def baseEnd_1607101 : Nat := 275071757773807314548861

theorem tailTrace_1607101 : CollatzResearch.WordTrace tailWord_1607101 prefixEnd_1607101 275071757773807314548861 := by
  unfold tailWord_1607101
  simp only [CollatzResearch.WordTrace]
  refine ⟨58615788950755022844157157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39077192633836681896104771 58615788950755022844157157)
  ·
    refine ⟨10990460428266566783279467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58615788950755022844157157 10990460428266566783279467)
    ·
      refine ⟨16485690642399850174919201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10990460428266566783279467 16485690642399850174919201)
      ·
        refine ⟨12364267981799887631189401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16485690642399850174919201 12364267981799887631189401)
        ·
          refine ⟨9273200986349915723392051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12364267981799887631189401 9273200986349915723392051)
          ·
            refine ⟨13909801479524873585088077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9273200986349915723392051 13909801479524873585088077)
            ·
              refine ⟨5216175554821827594408029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13909801479524873585088077 5216175554821827594408029)
              ·
                refine ⟨1956065833058185347903011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5216175554821827594408029 1956065833058185347903011)
                ·
                  refine ⟨2934098749587278021854517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1956065833058185347903011 2934098749587278021854517)
                  ·
                    refine ⟨275071757773807314548861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2934098749587278021854517 275071757773807314548861)
                    ·
                      rfl

theorem cell23_1607101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_1607101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607101 prefixEnd_1607101 := by exact prefixLift 1607101
  have htrace : WordTrace (prefixWord ++ tailWord_1607101) baseStart_1607101 baseEnd_1607101 := by
    simpa [prefixWord, tailWord_1607101, baseEnd_1607101] using wordTrace_append hprefix tailTrace_1607101
  have hstable : (prefixWord ++ tailWord_1607101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607101).length < 2 ^ (prefixWord ++ tailWord_1607101).sum := by decide
  have hdescent : baseEnd_1607101 < baseStart_1607101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607144 : List Nat := [2, 1, 4, 1, 1, 2, 3, 9]
def baseStart_1607144 : Nat := 118140960795 + 1607144 * 2 ^ 59
def prefixEnd_1607144 : Nat := 4983230072969 + 3 ^ 40 * 1607144 * 2
def baseEnd_1607144 : Nat := 30564346407020936126255

theorem tailTrace_1607144 : CollatzResearch.WordTrace tailWord_1607144 prefixEnd_1607144 30564346407020936126255 := by
  unfold tailWord_1607144
  simp only [CollatzResearch.WordTrace]
  refine ⟨29308678644799620593986243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39078238193066160791981657 29308678644799620593986243)
  ·
    refine ⟨43963017967199430890979365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29308678644799620593986243 43963017967199430890979365)
    ·
      refine ⟨8243065868849893292058631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43963017967199430890979365 8243065868849893292058631)
      ·
        refine ⟨12364598803274839938087947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8243065868849893292058631 12364598803274839938087947)
        ·
          refine ⟨18546898204912259907131921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12364598803274839938087947 18546898204912259907131921)
          ·
            refine ⟨13910173653684194930348941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18546898204912259907131921 13910173653684194930348941)
            ·
              refine ⟨5216315120131573098880853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13910173653684194930348941 5216315120131573098880853)
              ·
                refine ⟨30564346407020936126255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5216315120131573098880853 30564346407020936126255)
                ·
                  rfl

theorem cell23_1607144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 9].length) (baseStart_1607144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607144 prefixEnd_1607144 := by exact prefixLift 1607144
  have htrace : WordTrace (prefixWord ++ tailWord_1607144) baseStart_1607144 baseEnd_1607144 := by
    simpa [prefixWord, tailWord_1607144, baseEnd_1607144] using wordTrace_append hprefix tailTrace_1607144
  have hstable : (prefixWord ++ tailWord_1607144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607144).length < 2 ^ (prefixWord ++ tailWord_1607144).sum := by decide
  have hdescent : baseEnd_1607144 < baseStart_1607144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607149 : List Nat := [1, 5, 1, 3, 2, 2, 1, 3, 1, 1, 3]
def baseStart_1607149 : Nat := 118140960795 + 1607149 * 2 ^ 59
def prefixEnd_1607149 : Nat := 4983230072969 + 3 ^ 40 * 1607149 * 2
def baseEnd_1607149 : Nat := 825239920392837755846363

theorem tailTrace_1607149 : CollatzResearch.WordTrace tailWord_1607149 prefixEnd_1607149 825239920392837755846363 := by
  unfold tailWord_1607149
  simp only [CollatzResearch.WordTrace]
  refine ⟨58617539654581127041904501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39078359769720751361269667 58617539654581127041904501)
  ·
    refine ⟨5495394342616980660178547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58617539654581127041904501 5495394342616980660178547)
    ·
      refine ⟨8243091513925470990267821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5495394342616980660178547 8243091513925470990267821)
      ·
        refine ⟨3091159317722051621350433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8243091513925470990267821 3091159317722051621350433)
        ·
          refine ⟨2318369488291538716012825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3091159317722051621350433 2318369488291538716012825)
          ·
            refine ⟨1738777116218654037009619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2318369488291538716012825 1738777116218654037009619)
            ·
              refine ⟨2608165674327981055514429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738777116218654037009619 2608165674327981055514429)
              ·
                refine ⟨978062127872992895817911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2608165674327981055514429 978062127872992895817911)
                ·
                  refine ⟨1467093191809489343726867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 978062127872992895817911 1467093191809489343726867)
                  ·
                    refine ⟨2200639787714234015590301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1467093191809489343726867 2200639787714234015590301)
                    ·
                      refine ⟨825239920392837755846363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2200639787714234015590301 825239920392837755846363)
                      ·
                        rfl

theorem cell23_1607149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_1607149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607149 prefixEnd_1607149 := by exact prefixLift 1607149
  have htrace : WordTrace (prefixWord ++ tailWord_1607149) baseStart_1607149 baseEnd_1607149 := by
    simpa [prefixWord, tailWord_1607149, baseEnd_1607149] using wordTrace_append hprefix tailTrace_1607149
  have hstable : (prefixWord ++ tailWord_1607149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607149).length < 2 ^ (prefixWord ++ tailWord_1607149).sum := by decide
  have hdescent : baseEnd_1607149 < baseStart_1607149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607155 : List Nat := [1, 1, 1, 2, 2, 2, 2, 7, 1, 2, 2]
def baseStart_1607155 : Nat := 118140960795 + 1607155 * 2 ^ 59
def prefixEnd_1607155 : Nat := 4983230072969 + 3 ^ 40 * 1607155 * 2
def baseEnd_1607155 : Nat := 825243001276764732371335

theorem tailTrace_1607155 : CollatzResearch.WordTrace tailWord_1607155 prefixEnd_1607155 825243001276764732371335 := by
  unfold tailWord_1607155
  simp only [CollatzResearch.WordTrace]
  refine ⟨58617758492559390066622919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39078505661706260044415279 58617758492559390066622919)
  ·
    refine ⟨87926637738839085099934379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58617758492559390066622919 87926637738839085099934379)
    ·
      refine ⟨131889956608258627649901569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87926637738839085099934379 131889956608258627649901569)
      ·
        refine ⟨98917467456193970737426177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131889956608258627649901569 98917467456193970737426177)
        ·
          refine ⟨74188100592145478053069633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98917467456193970737426177 74188100592145478053069633)
          ·
            refine ⟨55641075444109108539802225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74188100592145478053069633 55641075444109108539802225)
            ·
              refine ⟨41730806583081831404851669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55641075444109108539802225 41730806583081831404851669)
              ·
                refine ⟨978065779290980423551211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 41730806583081831404851669 978065779290980423551211)
                ·
                  refine ⟨1467098668936470635326817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 978065779290980423551211 1467098668936470635326817)
                  ·
                    refine ⟨1100324001702352976495113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1467098668936470635326817 1100324001702352976495113)
                    ·
                      refine ⟨825243001276764732371335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1100324001702352976495113 825243001276764732371335)
                      ·
                        rfl

theorem cell23_1607155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 1, 2, 2].length) (baseStart_1607155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607155 prefixEnd_1607155 := by exact prefixLift 1607155
  have htrace : WordTrace (prefixWord ++ tailWord_1607155) baseStart_1607155 baseEnd_1607155 := by
    simpa [prefixWord, tailWord_1607155, baseEnd_1607155] using wordTrace_append hprefix tailTrace_1607155
  have hstable : (prefixWord ++ tailWord_1607155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607155).length < 2 ^ (prefixWord ++ tailWord_1607155).sum := by decide
  have hdescent : baseEnd_1607155 < baseStart_1607155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607158 : List Nat := [5, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5]
def baseStart_1607158 : Nat := 118140960795 + 1607158 * 2 ^ 59
def prefixEnd_1607158 : Nat := 4983230072969 + 3 ^ 40 * 1607158 * 2
def baseEnd_1607158 : Nat := 825244541718728220633821

theorem tailTrace_1607158 : CollatzResearch.WordTrace tailWord_1607158 prefixEnd_1607158 825244541718728220633821 := by
  unfold tailWord_1607158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3663616744471782598686383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39078578607699014385988085 3663616744471782598686383)
  ·
    refine ⟨5495425116707673898029575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3663616744471782598686383 5495425116707673898029575)
    ·
      refine ⟨8243137675061510847044363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5495425116707673898029575 8243137675061510847044363)
      ·
        refine ⟨12364706512592266270566545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8243137675061510847044363 12364706512592266270566545)
        ·
          refine ⟨9273529884444199702924909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12364706512592266270566545 9273529884444199702924909)
          ·
            refine ⟨3477573706666574888596841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9273529884444199702924909 3477573706666574888596841)
            ·
              refine ⟨2608180279999931166447631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3477573706666574888596841 2608180279999931166447631)
              ·
                refine ⟨3912270419999896749671447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2608180279999931166447631 3912270419999896749671447)
                ·
                  refine ⟨5868405629999845124507171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3912270419999896749671447 5868405629999845124507171)
                  ·
                    refine ⟨8802608444999767686760757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5868405629999845124507171 8802608444999767686760757)
                    ·
                      refine ⟨825244541718728220633821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8802608444999767686760757 825244541718728220633821)
                      ·
                        rfl

theorem cell23_1607158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_1607158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607158 prefixEnd_1607158 := by exact prefixLift 1607158
  have htrace : WordTrace (prefixWord ++ tailWord_1607158) baseStart_1607158 baseEnd_1607158 := by
    simpa [prefixWord, tailWord_1607158, baseEnd_1607158] using wordTrace_append hprefix tailTrace_1607158
  have hstable : (prefixWord ++ tailWord_1607158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607158).length < 2 ^ (prefixWord ++ tailWord_1607158).sum := by decide
  have hdescent : baseEnd_1607158 < baseStart_1607158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607166 : List Nat := [4, 2, 2, 3, 1, 1, 3, 2, 1, 1, 3]
def baseStart_1607166 : Nat := 118140960795 + 1607166 * 2 ^ 59
def prefixEnd_1607166 : Nat := 4983230072969 + 3 ^ 40 * 1607166 * 2
def baseEnd_1607166 : Nat := 825248649563964189333785

theorem tailTrace_1607166 : CollatzResearch.WordTrace tailWord_1607166 prefixEnd_1607166 825248649563964189333785 := by
  unfold tailWord_1607166
  simp only [CollatzResearch.WordTrace]
  refine ⟨7327269961939942368159169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39078773130346359296848901 7327269961939942368159169)
  ·
    refine ⟨5495452471454956776119377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7327269961939942368159169 5495452471454956776119377)
    ·
      refine ⟨4121589353591217582089533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5495452471454956776119377 4121589353591217582089533)
      ·
        refine ⟨1545596007596706593283575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4121589353591217582089533 1545596007596706593283575)
        ·
          refine ⟨2318394011395059889925363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1545596007596706593283575 2318394011395059889925363)
          ·
            refine ⟨3477591017092589834888045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318394011395059889925363 3477591017092589834888045)
            ·
              refine ⟨1304096631409721188083017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3477591017092589834888045 1304096631409721188083017)
              ·
                refine ⟨978072473557290891062263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1304096631409721188083017 978072473557290891062263)
                ·
                  refine ⟨1467108710335936336593395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 978072473557290891062263 1467108710335936336593395)
                  ·
                    refine ⟨2200663065503904504890093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1467108710335936336593395 2200663065503904504890093)
                    ·
                      refine ⟨825248649563964189333785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2200663065503904504890093 825248649563964189333785)
                      ·
                        rfl

theorem cell23_1607166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_1607166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607166 prefixEnd_1607166 := by exact prefixLift 1607166
  have htrace : WordTrace (prefixWord ++ tailWord_1607166) baseStart_1607166 baseEnd_1607166 := by
    simpa [prefixWord, tailWord_1607166, baseEnd_1607166] using wordTrace_append hprefix tailTrace_1607166
  have hstable : (prefixWord ++ tailWord_1607166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607166).length < 2 ^ (prefixWord ++ tailWord_1607166).sum := by decide
  have hdescent : baseEnd_1607166 < baseStart_1607166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607182 : List Nat := [4, 1, 1, 2, 4, 2, 2, 1, 2, 4]
def baseStart_1607182 : Nat := 118140960795 + 1607182 * 2 ^ 59
def prefixEnd_1607182 : Nat := 4983230072969 + 3 ^ 40 * 1607182 * 2
def baseEnd_1607182 : Nat := 275085621751478708911237

theorem tailTrace_1607182 : CollatzResearch.WordTrace tailWord_1607182 prefixEnd_1607182 275085621751478708911237 := by
  unfold tailWord_1607182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7327342907932696709731975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39079162175641049118570533 7327342907932696709731975)
  ·
    refine ⟨10991014361899045064597963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7327342907932696709731975 10991014361899045064597963)
    ·
      refine ⟨16486521542848567596896945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10991014361899045064597963 16486521542848567596896945)
      ·
        refine ⟨12364891157136425697672709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16486521542848567596896945 12364891157136425697672709)
        ·
          refine ⟨2318417091963079818313633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12364891157136425697672709 2318417091963079818313633)
          ·
            refine ⟨1738812818972309863735225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2318417091963079818313633 1738812818972309863735225)
            ·
              refine ⟨1304109614229232397801419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1738812818972309863735225 1304109614229232397801419)
              ·
                refine ⟨1956164421343848596702129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1304109614229232397801419 1956164421343848596702129)
                ·
                  refine ⟨1467123316007886447526597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1956164421343848596702129 1467123316007886447526597)
                  ·
                    refine ⟨275085621751478708911237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1467123316007886447526597 275085621751478708911237)
                    ·
                      rfl

theorem cell23_1607182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_1607182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607182 prefixEnd_1607182 := by exact prefixLift 1607182
  have htrace : WordTrace (prefixWord ++ tailWord_1607182) baseStart_1607182 baseEnd_1607182 := by
    simpa [prefixWord, tailWord_1607182, baseEnd_1607182] using wordTrace_append hprefix tailTrace_1607182
  have hstable : (prefixWord ++ tailWord_1607182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607182).length < 2 ^ (prefixWord ++ tailWord_1607182).sum := by decide
  have hdescent : baseEnd_1607182 < baseStart_1607182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607192 : List Nat := [2, 1, 2, 3, 5, 1, 1, 2, 1, 2, 3]
def baseStart_1607192 : Nat := 118140960795 + 1607192 * 2 ^ 59
def prefixEnd_1607192 : Nat := 4983230072969 + 3 ^ 40 * 1607192 * 2
def baseEnd_1607192 : Nat := 825262000060981087608665

theorem tailTrace_1607192 : CollatzResearch.WordTrace tailWord_1607192 prefixEnd_1607192 825262000060981087608665 := by
  unfold tailWord_1607192
  simp only [CollatzResearch.WordTrace]
  refine ⟨29309553996712672692859915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39079405328950230257146553 29309553996712672692859915)
  ·
    refine ⟨43964330995069009039289873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29309553996712672692859915 43964330995069009039289873)
    ·
      refine ⟨32973248246301756779467405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43964330995069009039289873 32973248246301756779467405)
      ·
        refine ⟨12364968092363158792300277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32973248246301756779467405 12364968092363158792300277)
        ·
          refine ⟨1159215758659046136778151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12364968092363158792300277 1159215758659046136778151)
          ·
            refine ⟨1738823637988569205167227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159215758659046136778151 1738823637988569205167227)
            ·
              refine ⟨2608235456982853807750841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738823637988569205167227 2608235456982853807750841)
              ·
                refine ⟨1956176592737140355813131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2608235456982853807750841 1956176592737140355813131)
                ·
                  refine ⟨2934264889105710533719697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1956176592737140355813131 2934264889105710533719697)
                  ·
                    refine ⟨2200698666829282900289773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2934264889105710533719697 2200698666829282900289773)
                    ·
                      refine ⟨825262000060981087608665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2200698666829282900289773 825262000060981087608665)
                      ·
                        rfl

theorem cell23_1607192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_1607192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607192 prefixEnd_1607192 := by exact prefixLift 1607192
  have htrace : WordTrace (prefixWord ++ tailWord_1607192) baseStart_1607192 baseEnd_1607192 := by
    simpa [prefixWord, tailWord_1607192, baseEnd_1607192] using wordTrace_append hprefix tailTrace_1607192
  have hstable : (prefixWord ++ tailWord_1607192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607192).length < 2 ^ (prefixWord ++ tailWord_1607192).sum := by decide
  have hdescent : baseEnd_1607192 < baseStart_1607192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607194 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8]
def baseStart_1607194 : Nat := 118140960795 + 1607194 * 2 ^ 59
def prefixEnd_1607194 : Nat := 4983230072969 + 3 ^ 40 * 1607194 * 2
def baseEnd_1607194 : Nat := 825263027022290079783655

theorem tailTrace_1607194 : CollatzResearch.WordTrace tailWord_1607194 prefixEnd_1607194 825263027022290079783655 := by
  unfold tailWord_1607194
  simp only [CollatzResearch.WordTrace]
  refine ⟨14654795234854524931823159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39079453959612066484861757 14654795234854524931823159)
  ·
    refine ⟨21982192852281787397734739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14654795234854524931823159 21982192852281787397734739)
    ·
      refine ⟨32973289278422681096602109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21982192852281787397734739 32973289278422681096602109)
      ·
        refine ⟨12364983479408505411225791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32973289278422681096602109 12364983479408505411225791)
        ·
          refine ⟨18547475219112758116838687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12364983479408505411225791 18547475219112758116838687)
          ·
            refine ⟨27821212828669137175258031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18547475219112758116838687 27821212828669137175258031)
            ·
              refine ⟨41731819243003705762887047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27821212828669137175258031 41731819243003705762887047)
              ·
                refine ⟨62597728864505558644330571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41731819243003705762887047 62597728864505558644330571)
                ·
                  refine ⟨93896593296758337966495857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62597728864505558644330571 93896593296758337966495857)
                  ·
                    refine ⟨70422444972568753474871893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93896593296758337966495857 70422444972568753474871893)
                    ·
                      refine ⟨825263027022290079783655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 70422444972568753474871893 825263027022290079783655)
                      ·
                        rfl

theorem cell23_1607194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_1607194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607194 prefixEnd_1607194 := by exact prefixLift 1607194
  have htrace : WordTrace (prefixWord ++ tailWord_1607194) baseStart_1607194 baseEnd_1607194 := by
    simpa [prefixWord, tailWord_1607194, baseEnd_1607194] using wordTrace_append hprefix tailTrace_1607194
  have hstable : (prefixWord ++ tailWord_1607194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607194).length < 2 ^ (prefixWord ++ tailWord_1607194).sum := by decide
  have hdescent : baseEnd_1607194 < baseStart_1607194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607231 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 3]
def baseStart_1607231 : Nat := 118140960795 + 1607231 * 2 ^ 59
def prefixEnd_1607231 : Nat := 4983230072969 + 3 ^ 40 * 1607231 * 2
def baseEnd_1607231 : Nat := 825282025806506435020985

theorem tailTrace_1607231 : CollatzResearch.WordTrace tailWord_1607231 prefixEnd_1607231 825282025806506435020985 := by
  unfold tailWord_1607231
  simp only [CollatzResearch.WordTrace]
  refine ⟨58620530440284055046389547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39080353626856036697593031 58620530440284055046389547)
  ·
    refine ⟨87930795660426082569584321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58620530440284055046389547 87930795660426082569584321)
    ·
      refine ⟨65948096745319561927188241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87930795660426082569584321 65948096745319561927188241)
      ·
        refine ⟨49461072558989671445391181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65948096745319561927188241 49461072558989671445391181)
        ·
          refine ⟨18547902209621126792021693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49461072558989671445391181 18547902209621126792021693)
          ·
            refine ⟨6955463328607922547008135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18547902209621126792021693 6955463328607922547008135)
            ·
              refine ⟨10433194992911883820512203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6955463328607922547008135 10433194992911883820512203)
              ·
                refine ⟨15649792489367825730768305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10433194992911883820512203 15649792489367825730768305)
                ·
                  refine ⟨11737344367025869298076229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15649792489367825730768305 11737344367025869298076229)
                  ·
                    refine ⟨2200752068817350493389293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11737344367025869298076229 2200752068817350493389293)
                    ·
                      refine ⟨825282025806506435020985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2200752068817350493389293 825282025806506435020985)
                      ·
                        rfl

theorem cell23_1607231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 3].length) (baseStart_1607231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607231 prefixEnd_1607231 := by exact prefixLift 1607231
  have htrace : WordTrace (prefixWord ++ tailWord_1607231) baseStart_1607231 baseEnd_1607231 := by
    simpa [prefixWord, tailWord_1607231, baseEnd_1607231] using wordTrace_append hprefix tailTrace_1607231
  have hstable : (prefixWord ++ tailWord_1607231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607231).length < 2 ^ (prefixWord ++ tailWord_1607231).sum := by decide
  have hdescent : baseEnd_1607231 < baseStart_1607231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607268 : List Nat := [2, 3, 1, 1, 2, 3, 1, 5, 5]
def baseStart_1607268 : Nat := 118140960795 + 1607268 * 2 ^ 59
def prefixEnd_1607268 : Nat := 4983230072969 + 3 ^ 40 * 1607268 * 2
def baseEnd_1607268 : Nat := 91700113843413643362035

theorem tailTrace_1607268 : CollatzResearch.WordTrace tailWord_1607268 prefixEnd_1607268 91700113843413643362035 := by
  unfold tailWord_1607268
  simp only [CollatzResearch.WordTrace]
  refine ⟨29310939970575005182743229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39081253294100006910324305 29310939970575005182743229)
  ·
    refine ⟨10991602488965626943528711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29310939970575005182743229 10991602488965626943528711)
    ·
      refine ⟨16487403733448440415293067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10991602488965626943528711 16487403733448440415293067)
      ·
        refine ⟨24731105600172660622939601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16487403733448440415293067 24731105600172660622939601)
        ·
          refine ⟨18548329200129495467204701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24731105600172660622939601 18548329200129495467204701)
          ·
            refine ⟨6955623450048560800201763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18548329200129495467204701 6955623450048560800201763)
            ·
              refine ⟨10433435175072841200302645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6955623450048560800201763 10433435175072841200302645)
              ·
                refine ⟨978134547663078862528373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10433435175072841200302645 978134547663078862528373)
                ·
                  refine ⟨91700113843413643362035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 978134547663078862528373 91700113843413643362035)
                  ·
                    rfl

theorem cell23_1607268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_1607268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607268 prefixEnd_1607268 := by exact prefixLift 1607268
  have htrace : WordTrace (prefixWord ++ tailWord_1607268) baseStart_1607268 baseEnd_1607268 := by
    simpa [prefixWord, tailWord_1607268, baseEnd_1607268] using wordTrace_append hprefix tailTrace_1607268
  have hstable : (prefixWord ++ tailWord_1607268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607268).length < 2 ^ (prefixWord ++ tailWord_1607268).sum := by decide
  have hdescent : baseEnd_1607268 < baseStart_1607268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607281 : List Nat := [1, 2, 2, 2, 1, 1, 1, 6, 2, 5]
def baseStart_1607281 : Nat := 118140960795 + 1607281 * 2 ^ 59
def prefixEnd_1607281 : Nat := 4983230072969 + 3 ^ 40 * 1607281 * 2
def baseEnd_1607281 : Nat := 275102566613077079798585

theorem tailTrace_1607281 : CollatzResearch.WordTrace tailWord_1607281 prefixEnd_1607281 275102566613077079798585 := by
  unfold tailWord_1607281
  simp only [CollatzResearch.WordTrace]
  refine ⟨58622354090102913585709697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39081569393401942390473131 58622354090102913585709697)
  ·
    refine ⟨43966765567577185189282273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58622354090102913585709697 43966765567577185189282273)
    ·
      refine ⟨32975074175682888891961705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43966765567577185189282273 32975074175682888891961705)
      ·
        refine ⟨24731305631762166668971279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32975074175682888891961705 24731305631762166668971279)
        ·
          refine ⟨37096958447643250003456919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24731305631762166668971279 37096958447643250003456919)
          ·
            refine ⟨55645437671464875005185379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37096958447643250003456919 55645437671464875005185379)
            ·
              refine ⟨83468156507197312507778069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55645437671464875005185379 83468156507197312507778069)
              ·
                refine ⟨3912569836274874023802097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83468156507197312507778069 3912569836274874023802097)
                ·
                  refine ⟨2934427377206155517851573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3912569836274874023802097 2934427377206155517851573)
                  ·
                    refine ⟨275102566613077079798585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2934427377206155517851573 275102566613077079798585)
                    ·
                      rfl

theorem cell23_1607281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_1607281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607281 prefixEnd_1607281 := by exact prefixLift 1607281
  have htrace : WordTrace (prefixWord ++ tailWord_1607281) baseStart_1607281 baseEnd_1607281 := by
    simpa [prefixWord, tailWord_1607281, baseEnd_1607281] using wordTrace_append hprefix tailTrace_1607281
  have hstable : (prefixWord ++ tailWord_1607281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607281).length < 2 ^ (prefixWord ++ tailWord_1607281).sum := by decide
  have hdescent : baseEnd_1607281 < baseStart_1607281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607285 : List Nat := [1, 3, 4, 2, 1, 1, 2, 4, 5]
def baseStart_1607285 : Nat := 118140960795 + 1607285 * 2 ^ 59
def prefixEnd_1607285 : Nat := 4983230072969 + 3 ^ 40 * 1607285 * 2
def baseEnd_1607285 : Nat := 91701083751316580416193

theorem tailTrace_1607285 : CollatzResearch.WordTrace tailWord_1607285 prefixEnd_1607285 91701083751316580416193 := by
  unfold tailWord_1607285
  simp only [CollatzResearch.WordTrace]
  refine ⟨58622499982088422268855309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39081666654725614845903539 58622499982088422268855309)
  ·
    refine ⟨21983437493283158350820741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58622499982088422268855309 21983437493283158350820741)
    ·
      refine ⟨4121894529990592190778889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21983437493283158350820741 4121894529990592190778889)
      ·
        refine ⟨3091420897492944143084167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4121894529990592190778889 3091420897492944143084167)
        ·
          refine ⟨4637131346239416214626251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3091420897492944143084167 4637131346239416214626251)
          ·
            refine ⟨6955697019359124321939377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4637131346239416214626251 6955697019359124321939377)
            ·
              refine ⟨5216772764519343241454533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6955697019359124321939377 5216772764519343241454533)
              ·
                refine ⟨978144893347376857772725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5216772764519343241454533 978144893347376857772725)
                ·
                  refine ⟨91701083751316580416193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 978144893347376857772725 91701083751316580416193)
                  ·
                    rfl

theorem cell23_1607285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 5].length) (baseStart_1607285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607285 prefixEnd_1607285 := by exact prefixLift 1607285
  have htrace : WordTrace (prefixWord ++ tailWord_1607285) baseStart_1607285 baseEnd_1607285 := by
    simpa [prefixWord, tailWord_1607285, baseEnd_1607285] using wordTrace_append hprefix tailTrace_1607285
  have hstable : (prefixWord ++ tailWord_1607285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607285).length < 2 ^ (prefixWord ++ tailWord_1607285).sum := by decide
  have hdescent : baseEnd_1607285 < baseStart_1607285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607301 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 3, 3, 4]
def baseStart_1607301 : Nat := 118140960795 + 1607301 * 2 ^ 59
def prefixEnd_1607301 : Nat := 4983230072969 + 3 ^ 40 * 1607301 * 2
def baseEnd_1607301 : Nat := 825317969452321161145663

theorem tailTrace_1607301 : CollatzResearch.WordTrace tailWord_1607301 prefixEnd_1607301 825317969452321161145663 := by
  unfold tailWord_1607301
  simp only [CollatzResearch.WordTrace]
  refine ⟨58623083550030457001437757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39082055700020304667625171 58623083550030457001437757)
  ·
    refine ⟨21983656331261421375539159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58623083550030457001437757 21983656331261421375539159)
    ·
      refine ⟨32975484496892132063308739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21983656331261421375539159 32975484496892132063308739)
      ·
        refine ⟨49463226745338198094963109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32975484496892132063308739 49463226745338198094963109)
        ·
          refine ⟨9274355014750912142805583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49463226745338198094963109 9274355014750912142805583)
          ·
            refine ⟨13911532522126368214208375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9274355014750912142805583 13911532522126368214208375)
            ·
              refine ⟨20867298783189552321312563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13911532522126368214208375 20867298783189552321312563)
              ·
                refine ⟨31300948174784328481968845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20867298783189552321312563 31300948174784328481968845)
                ·
                  refine ⟨11737855565544123180738317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31300948174784328481968845 11737855565544123180738317)
                  ·
                    refine ⟨4401695837079046192776869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11737855565544123180738317 4401695837079046192776869)
                    ·
                      refine ⟨825317969452321161145663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4401695837079046192776869 825317969452321161145663)
                      ·
                        rfl

theorem cell23_1607301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_1607301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607301 prefixEnd_1607301 := by exact prefixLift 1607301
  have htrace : WordTrace (prefixWord ++ tailWord_1607301) baseStart_1607301 baseEnd_1607301 := by
    simpa [prefixWord, tailWord_1607301, baseEnd_1607301] using wordTrace_append hprefix tailTrace_1607301
  have hstable : (prefixWord ++ tailWord_1607301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607301).length < 2 ^ (prefixWord ++ tailWord_1607301).sum := by decide
  have hdescent : baseEnd_1607301 < baseStart_1607301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607336 : List Nat := [2, 1, 7, 1, 1, 1, 3, 2, 5]
def baseStart_1607336 : Nat := 118140960795 + 1607336 * 2 ^ 59
def prefixEnd_1607336 : Nat := 4983230072969 + 3 ^ 40 * 1607336 * 2
def baseEnd_1607336 : Nat := 91703993475025391578667

theorem tailTrace_1607336 : CollatzResearch.WordTrace tailWord_1607336 prefixEnd_1607336 91703993475025391578667 := by
  unfold tailWord_1607336
  simp only [CollatzResearch.WordTrace]
  refine ⟨29312180052451828989480931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39082906736602438652641241 29312180052451828989480931)
  ·
    refine ⟨43968270078677743484221397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29312180052451828989480931 43968270078677743484221397)
    ·
      refine ⟨1030506329969009612911439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 43968270078677743484221397 1030506329969009612911439)
      ·
        refine ⟨1545759494953514419367159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1030506329969009612911439 1545759494953514419367159)
        ·
          refine ⟨2318639242430271629050739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1545759494953514419367159 2318639242430271629050739)
          ·
            refine ⟨3477958863645407443576109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318639242430271629050739 3477958863645407443576109)
            ·
              refine ⟨1304234573867027791341041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3477958863645407443576109 1304234573867027791341041)
              ·
                refine ⟨978175930400270843505781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1304234573867027791341041 978175930400270843505781)
                ·
                  refine ⟨91703993475025391578667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 978175930400270843505781 91703993475025391578667)
                  ·
                    rfl

theorem cell23_1607336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 5].length) (baseStart_1607336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607336 prefixEnd_1607336 := by exact prefixLift 1607336
  have htrace : WordTrace (prefixWord ++ tailWord_1607336) baseStart_1607336 baseEnd_1607336 := by
    simpa [prefixWord, tailWord_1607336, baseEnd_1607336] using wordTrace_append hprefix tailTrace_1607336
  have hstable : (prefixWord ++ tailWord_1607336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607336).length < 2 ^ (prefixWord ++ tailWord_1607336).sum := by decide
  have hdescent : baseEnd_1607336 < baseStart_1607336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607372 : List Nat := [2, 2, 1, 5, 2, 1, 2, 1, 2, 2, 3]
def baseStart_1607372 : Nat := 118140960795 + 1607372 * 2 ^ 59
def prefixEnd_1607372 : Nat := 4983230072969 + 3 ^ 40 * 1607372 * 2
def baseEnd_1607372 : Nat := 825354426578790383357837

theorem tailTrace_1607372 : CollatzResearch.WordTrace tailWord_1607372 prefixEnd_1607372 825354426578790383357837 := by
  unfold tailWord_1607372
  simp only [CollatzResearch.WordTrace]
  refine ⟨29312836566386618063636185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39083782088515490751514913 29312836566386618063636185)
  ·
    refine ⟨21984627424789963547727139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29312836566386618063636185 21984627424789963547727139)
    ·
      refine ⟨32976941137184945321590709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21984627424789963547727139 32976941137184945321590709)
      ·
        refine ⟨3091588231611088623899129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32976941137184945321590709 3091588231611088623899129)
        ·
          refine ⟨2318691173708316467924347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3091588231611088623899129 2318691173708316467924347)
          ·
            refine ⟨3478036760562474701886521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318691173708316467924347 3478036760562474701886521)
            ·
              refine ⟨2608527570421856026414891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3478036760562474701886521 2608527570421856026414891)
              ·
                refine ⟨3912791355632784039622337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2608527570421856026414891 3912791355632784039622337)
                ·
                  refine ⟨2934593516724588029716753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3912791355632784039622337 2934593516724588029716753)
                  ·
                    refine ⟨2200945137543441022287565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2934593516724588029716753 2200945137543441022287565)
                    ·
                      refine ⟨825354426578790383357837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2200945137543441022287565 825354426578790383357837)
                      ·
                        rfl

theorem cell23_1607372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_1607372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607372 prefixEnd_1607372 := by exact prefixLift 1607372
  have htrace : WordTrace (prefixWord ++ tailWord_1607372) baseStart_1607372 baseEnd_1607372 := by
    simpa [prefixWord, tailWord_1607372, baseEnd_1607372] using wordTrace_append hprefix tailTrace_1607372
  have hstable : (prefixWord ++ tailWord_1607372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607372).length < 2 ^ (prefixWord ++ tailWord_1607372).sum := by decide
  have hdescent : baseEnd_1607372 < baseStart_1607372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607401 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 5, 6]
def baseStart_1607401 : Nat := 118140960795 + 1607401 * 2 ^ 59
def prefixEnd_1607401 : Nat := 4983230072969 + 3 ^ 40 * 1607401 * 2
def baseEnd_1607401 : Nat := 275123105839256923298401

theorem tailTrace_1607401 : CollatzResearch.WordTrace tailWord_1607401 prefixEnd_1607401 275123105839256923298401 := by
  unfold tailWord_1607401
  simp only [CollatzResearch.WordTrace]
  refine ⟨58626730849668174080078057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39084487233112116053385371 58626730849668174080078057)
  ·
    refine ⟨43970048137251130560058543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58626730849668174080078057 43970048137251130560058543)
    ·
      refine ⟨65955072205876695840087815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43970048137251130560058543 65955072205876695840087815)
      ·
        refine ⟨98932608308815043760131723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65955072205876695840087815 98932608308815043760131723)
        ·
          refine ⟨148398912463222565640197585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98932608308815043760131723 148398912463222565640197585)
          ·
            refine ⟨111299184347416924230148189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148398912463222565640197585 111299184347416924230148189)
            ·
              refine ⟨41737194130281346586305571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111299184347416924230148189 41737194130281346586305571)
              ·
                refine ⟨62605791195422019879458357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41737194130281346586305571 62605791195422019879458357)
                ·
                  refine ⟨5869292924570814363699221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62605791195422019879458357 5869292924570814363699221)
                  ·
                    refine ⟨275123105839256923298401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5869292924570814363699221 275123105839256923298401)
                    ·
                      rfl

theorem cell23_1607401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 6].length) (baseStart_1607401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607401 prefixEnd_1607401 := by exact prefixLift 1607401
  have htrace : WordTrace (prefixWord ++ tailWord_1607401) baseStart_1607401 baseEnd_1607401 := by
    simpa [prefixWord, tailWord_1607401, baseEnd_1607401] using wordTrace_append hprefix tailTrace_1607401
  have hstable : (prefixWord ++ tailWord_1607401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607401).length < 2 ^ (prefixWord ++ tailWord_1607401).sum := by decide
  have hdescent : baseEnd_1607401 < baseStart_1607401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607418 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 6, 4]
def baseStart_1607418 : Nat := 118140960795 + 1607418 * 2 ^ 59
def prefixEnd_1607418 : Nat := 4983230072969 + 3 ^ 40 * 1607418 * 2
def baseEnd_1607418 : Nat := 275126015562965734460875

theorem tailTrace_1607418 : CollatzResearch.WordTrace tailWord_1607418 prefixEnd_1607418 275126015562965734460875 := by
  unfold tailWord_1607418
  simp only [CollatzResearch.WordTrace]
  refine ⟨14656837722651646495861727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39084900593737723988964605 14656837722651646495861727)
  ·
    refine ⟨21985256583977469743792591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14656837722651646495861727 21985256583977469743792591)
    ·
      refine ⟨32977884875966204615688887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21985256583977469743792591 32977884875966204615688887)
      ·
        refine ⟨49466827313949306923533331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32977884875966204615688887 49466827313949306923533331)
        ·
          refine ⟨74200240970923960385299997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49466827313949306923533331 74200240970923960385299997)
          ·
            refine ⟨27825090364096485144487499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74200240970923960385299997 27825090364096485144487499)
            ·
              refine ⟨41737635546144727716731249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27825090364096485144487499 41737635546144727716731249)
              ·
                refine ⟨31303226659608545787548437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41737635546144727716731249 31303226659608545787548437)
                ·
                  refine ⟨1467338749669150583791333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31303226659608545787548437 1467338749669150583791333)
                  ·
                    refine ⟨275126015562965734460875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1467338749669150583791333 275126015562965734460875)
                    ·
                      rfl

theorem cell23_1607418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 6, 4].length) (baseStart_1607418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607418 prefixEnd_1607418 := by exact prefixLift 1607418
  have htrace : WordTrace (prefixWord ++ tailWord_1607418) baseStart_1607418 baseEnd_1607418 := by
    simpa [prefixWord, tailWord_1607418, baseEnd_1607418] using wordTrace_append hprefix tailTrace_1607418
  have hstable : (prefixWord ++ tailWord_1607418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607418).length < 2 ^ (prefixWord ++ tailWord_1607418).sum := by decide
  have hdescent : baseEnd_1607418 < baseStart_1607418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607459 : List Nat := [1, 1, 1, 4, 2, 1, 4, 4, 1, 2, 2]
def baseStart_1607459 : Nat := 118140960795 + 1607459 * 2 ^ 59
def prefixEnd_1607459 : Nat := 4983230072969 + 3 ^ 40 * 1607459 * 2
def baseEnd_1607459 : Nat := 825399099395731542969937

theorem tailTrace_1607459 : CollatzResearch.WordTrace tailWord_1607459 prefixEnd_1607459 825399099395731542969937 := by
  unfold tailWord_1607459
  simp only [CollatzResearch.WordTrace]
  refine ⟨58628846283458049985689431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39085897522305366657126287 58628846283458049985689431)
  ·
    refine ⟨87943269425187074978534147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58628846283458049985689431 87943269425187074978534147)
    ·
      refine ⟨131914904137780612467801221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87943269425187074978534147 131914904137780612467801221)
      ·
        refine ⟨24734044525833864837712729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131914904137780612467801221 24734044525833864837712729)
        ·
          refine ⟨18550533394375398628284547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24734044525833864837712729 18550533394375398628284547)
          ·
            refine ⟨27825800091563097942426821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18550533394375398628284547 27825800091563097942426821)
            ·
              refine ⟨5217337517168080864205029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27825800091563097942426821 5217337517168080864205029)
              ·
                refine ⟨978250784469015162038443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5217337517168080864205029 978250784469015162038443)
                ·
                  refine ⟨1467376176703522743057665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 978250784469015162038443 1467376176703522743057665)
                  ·
                    refine ⟨1100532132527642057293249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1467376176703522743057665 1100532132527642057293249)
                    ·
                      refine ⟨825399099395731542969937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1100532132527642057293249 825399099395731542969937)
                      ·
                        rfl

theorem cell23_1607459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 1, 2, 2].length) (baseStart_1607459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607459 prefixEnd_1607459 := by exact prefixLift 1607459
  have htrace : WordTrace (prefixWord ++ tailWord_1607459) baseStart_1607459 baseEnd_1607459 := by
    simpa [prefixWord, tailWord_1607459, baseEnd_1607459] using wordTrace_append hprefix tailTrace_1607459
  have hstable : (prefixWord ++ tailWord_1607459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607459).length < 2 ^ (prefixWord ++ tailWord_1607459).sum := by decide
  have hdescent : baseEnd_1607459 < baseStart_1607459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607538 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 9]
def baseStart_1607538 : Nat := 118140960795 + 1607538 * 2 ^ 59
def prefixEnd_1607538 : Nat := 4983230072969 + 3 ^ 40 * 1607538 * 2
def baseEnd_1607538 : Nat := 91715518263048525986897

theorem tailTrace_1607538 : CollatzResearch.WordTrace tailWord_1607538 prefixEnd_1607538 91715518263048525986897 := by
  unfold tailWord_1607538
  simp only [CollatzResearch.WordTrace]
  refine ⟨14657931912542961619453817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39087818433447897651876845 14657931912542961619453817)
  ·
    refine ⟨10993448934407221214590363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14657931912542961619453817 10993448934407221214590363)
    ·
      refine ⟨16490173401610831821885545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10993448934407221214590363 16490173401610831821885545)
      ·
        refine ⟨12367630051208123866414159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16490173401610831821885545 12367630051208123866414159)
        ·
          refine ⟨18551445076812185799621239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12367630051208123866414159 18551445076812185799621239)
          ·
            refine ⟨27827167615218278699431859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18551445076812185799621239 27827167615218278699431859)
            ·
              refine ⟨41740751422827418049147789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27827167615218278699431859 41740751422827418049147789)
              ·
                refine ⟨15652781783560281768430421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41740751422827418049147789 15652781783560281768430421)
                ·
                  refine ⟨91715518263048525986897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15652781783560281768430421 91715518263048525986897)
                  ·
                    rfl

theorem cell23_1607538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_1607538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607538 prefixEnd_1607538 := by exact prefixLift 1607538
  have htrace : WordTrace (prefixWord ++ tailWord_1607538) baseStart_1607538 baseEnd_1607538 := by
    simpa [prefixWord, tailWord_1607538, baseEnd_1607538] using wordTrace_append hprefix tailTrace_1607538
  have hstable : (prefixWord ++ tailWord_1607538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607538).length < 2 ^ (prefixWord ++ tailWord_1607538).sum := by decide
  have hdescent : baseEnd_1607538 < baseStart_1607538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607553 : List Nat := [1, 2, 4, 4, 1, 1, 3, 1, 1, 3, 2]
def baseStart_1607553 : Nat := 118140960795 + 1607553 * 2 ^ 59
def prefixEnd_1607553 : Nat := 4983230072969 + 3 ^ 40 * 1607553 * 2
def baseEnd_1607553 : Nat := 825447366577254175194505

theorem tailTrace_1607553 : CollatzResearch.WordTrace tailWord_1607553 prefixEnd_1607553 825447366577254175194505 := by
  unfold tailWord_1607553
  simp only [CollatzResearch.WordTrace]
  refine ⟨58632274745117504039611313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39088183163411669359740875 58632274745117504039611313)
  ·
    refine ⟨43974206058838128029708485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58632274745117504039611313 43974206058838128029708485)
    ·
      refine ⟨8245163636032149005570341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43974206058838128029708485 8245163636032149005570341)
      ·
        refine ⟨1545968181756027938544439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8245163636032149005570341 1545968181756027938544439)
        ·
          refine ⟨2318952272634041907816659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1545968181756027938544439 2318952272634041907816659)
          ·
            refine ⟨3478428408951062861724989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318952272634041907816659 3478428408951062861724989)
            ·
              refine ⟨1304410653356648573146871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3478428408951062861724989 1304410653356648573146871)
              ·
                refine ⟨1956615980034972859720307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1304410653356648573146871 1956615980034972859720307)
                ·
                  refine ⟨2934923970052459289580461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1956615980034972859720307 2934923970052459289580461)
                  ·
                    refine ⟨1100596488769672233592673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2934923970052459289580461 1100596488769672233592673)
                    ·
                      refine ⟨825447366577254175194505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1100596488769672233592673 825447366577254175194505)
                      ·
                        rfl

theorem cell23_1607553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_1607553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607553 prefixEnd_1607553 := by exact prefixLift 1607553
  have htrace : WordTrace (prefixWord ++ tailWord_1607553) baseStart_1607553 baseEnd_1607553 := by
    simpa [prefixWord, tailWord_1607553, baseEnd_1607553] using wordTrace_append hprefix tailTrace_1607553
  have hstable : (prefixWord ++ tailWord_1607553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607553).length < 2 ^ (prefixWord ++ tailWord_1607553).sum := by decide
  have hdescent : baseEnd_1607553 < baseStart_1607553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607615 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 5, 4]
def baseStart_1607615 : Nat := 118140960795 + 1607615 * 2 ^ 59
def prefixEnd_1607615 : Nat := 4983230072969 + 3 ^ 40 * 1607615 * 2
def baseEnd_1607615 : Nat := 275159734125944310873073

theorem tailTrace_1607615 : CollatzResearch.WordTrace tailWord_1607615 prefixEnd_1607615 275159734125944310873073 := by
  unfold tailWord_1607615
  simp only [CollatzResearch.WordTrace]
  refine ⟨58634536070892888628368299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39089690713928592418912199 58634536070892888628368299)
  ·
    refine ⟨87951804106339332942552449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58634536070892888628368299 87951804106339332942552449)
    ·
      refine ⟨65963853079754499706914337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87951804106339332942552449 65963853079754499706914337)
      ·
        refine ⟨49472889809815874780185753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65963853079754499706914337 49472889809815874780185753)
        ·
          refine ⟨37104667357361906085139315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49472889809815874780185753 37104667357361906085139315)
          ·
            refine ⟨55657001036042859127708973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37104667357361906085139315 55657001036042859127708973)
            ·
              refine ⟨20871375388516072172890865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55657001036042859127708973 20871375388516072172890865)
              ·
                refine ⟨15653531541387054129668149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20871375388516072172890865 15653531541387054129668149)
                ·
                  refine ⟨1467518582005036324656389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15653531541387054129668149 1467518582005036324656389)
                  ·
                    refine ⟨275159734125944310873073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1467518582005036324656389 275159734125944310873073)
                    ·
                      rfl

theorem cell23_1607615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 4].length) (baseStart_1607615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607615 prefixEnd_1607615 := by exact prefixLift 1607615
  have htrace : WordTrace (prefixWord ++ tailWord_1607615) baseStart_1607615 baseEnd_1607615 := by
    simpa [prefixWord, tailWord_1607615, baseEnd_1607615] using wordTrace_append hprefix tailTrace_1607615
  have hstable : (prefixWord ++ tailWord_1607615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607615).length < 2 ^ (prefixWord ++ tailWord_1607615).sum := by decide
  have hdescent : baseEnd_1607615 < baseStart_1607615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607672 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 5, 1, 3]
def baseStart_1607672 : Nat := 118140960795 + 1607672 * 2 ^ 59
def prefixEnd_1607672 : Nat := 4983230072969 + 3 ^ 40 * 1607672 * 2
def baseEnd_1607672 : Nat := 825508470775139209606457

theorem tailTrace_1607672 : CollatzResearch.WordTrace tailWord_1607672 prefixEnd_1607672 825508470775139209606457 := by
  unfold tailWord_1607672
  simp only [CollatzResearch.WordTrace]
  refine ⟨29318307515843193681596635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39091076687790924908795513 29318307515843193681596635)
  ·
    refine ⟨43977461273764790522394953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29318307515843193681596635 43977461273764790522394953)
    ·
      refine ⟨32983095955323592891796215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43977461273764790522394953 32983095955323592891796215)
      ·
        refine ⟨49474643932985389337694323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32983095955323592891796215 49474643932985389337694323)
        ·
          refine ⟨74211965899478084006541485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49474643932985389337694323 74211965899478084006541485)
          ·
            refine ⟨27829487212304281502453057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74211965899478084006541485 27829487212304281502453057)
            ·
              refine ⟨20872115409228211126839793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27829487212304281502453057 20872115409228211126839793)
              ·
                refine ⟨15654086556921158345129845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20872115409228211126839793 15654086556921158345129845)
                ·
                  refine ⟨1467570614711358594855923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15654086556921158345129845 1467570614711358594855923)
                  ·
                    refine ⟨2201355922067037892283885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1467570614711358594855923 2201355922067037892283885)
                    ·
                      refine ⟨825508470775139209606457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2201355922067037892283885 825508470775139209606457)
                      ·
                        rfl

theorem cell23_1607672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 5, 1, 3].length) (baseStart_1607672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607672 prefixEnd_1607672 := by exact prefixLift 1607672
  have htrace : WordTrace (prefixWord ++ tailWord_1607672) baseStart_1607672 baseEnd_1607672 := by
    simpa [prefixWord, tailWord_1607672, baseEnd_1607672] using wordTrace_append hprefix tailTrace_1607672
  have hstable : (prefixWord ++ tailWord_1607672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607672).length < 2 ^ (prefixWord ++ tailWord_1607672).sum := by decide
  have hdescent : baseEnd_1607672 < baseStart_1607672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607705 : List Nat := [1, 2, 1, 2, 1, 1, 3, 5, 1, 6]
def baseStart_1607705 : Nat := 118140960795 + 1607705 * 2 ^ 59
def prefixEnd_1607705 : Nat := 4983230072969 + 3 ^ 40 * 1607705 * 2
def baseEnd_1607705 : Nat := 275175138545579193497935

theorem tailTrace_1607705 : CollatzResearch.WordTrace tailWord_1607705 prefixEnd_1607705 275175138545579193497935 := by
  unfold tailWord_1607705
  simp only [CollatzResearch.WordTrace]
  refine ⟨58637818640566833999144569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39091879093711222666096379 58637818640566833999144569)
  ·
    refine ⟨43978363980425125499358427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58637818640566833999144569 43978363980425125499358427)
    ·
      refine ⟨65967545970637688249037641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43978363980425125499358427 65967545970637688249037641)
      ·
        refine ⟨49475659477978266186778231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65967545970637688249037641 49475659477978266186778231)
        ·
          refine ⟨74213489216967399280167347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49475659477978266186778231 74213489216967399280167347)
          ·
            refine ⟨111320233825451098920251021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74213489216967399280167347 111320233825451098920251021)
            ·
              refine ⟨41745087684544162095094133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111320233825451098920251021 41745087684544162095094133)
              ·
                refine ⟨3913601970426015196415075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41745087684544162095094133 3913601970426015196415075)
                ·
                  refine ⟨5870402955639022794622613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3913601970426015196415075 5870402955639022794622613)
                  ·
                    refine ⟨275175138545579193497935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5870402955639022794622613 275175138545579193497935)
                    ·
                      rfl

theorem cell23_1607705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 6].length) (baseStart_1607705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607705 prefixEnd_1607705 := by exact prefixLift 1607705
  have htrace : WordTrace (prefixWord ++ tailWord_1607705) baseStart_1607705 baseEnd_1607705 := by
    simpa [prefixWord, tailWord_1607705, baseEnd_1607705] using wordTrace_append hprefix tailTrace_1607705
  have hstable : (prefixWord ++ tailWord_1607705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607705).length < 2 ^ (prefixWord ++ tailWord_1607705).sum := by decide
  have hdescent : baseEnd_1607705 < baseStart_1607705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607709 : List Nat := [1, 4, 2, 2, 2, 1, 3, 2, 1, 5]
def baseStart_1607709 : Nat := 118140960795 + 1607709 * 2 ^ 59
def prefixEnd_1607709 : Nat := 4983230072969 + 3 ^ 40 * 1607709 * 2
def baseEnd_1607709 : Nat := 275175823186451854947929

theorem tailTrace_1607709 : CollatzResearch.WordTrace tailWord_1607709 prefixEnd_1607709 275175823186451854947929 := by
  unfold tailWord_1607709
  simp only [CollatzResearch.WordTrace]
  refine ⟨58637964532552342682290181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39091976355034895121526787 58637964532552342682290181)
  ·
    refine ⟨10994618349853564252929409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58637964532552342682290181 10994618349853564252929409)
    ·
      refine ⟨8245963762390173189697057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10994618349853564252929409 8245963762390173189697057)
      ·
        refine ⟨6184472821792629892272793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8245963762390173189697057 6184472821792629892272793)
        ·
          refine ⟨4638354616344472419204595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6184472821792629892272793 4638354616344472419204595)
          ·
            refine ⟨6957531924516708628806893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4638354616344472419204595 6957531924516708628806893)
            ·
              refine ⟨2609074471693765735802585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6957531924516708628806893 2609074471693765735802585)
              ·
                refine ⟨1956805853770324301851939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2609074471693765735802585 1956805853770324301851939)
                ·
                  refine ⟨2935208780655486452777909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1956805853770324301851939 2935208780655486452777909)
                  ·
                    refine ⟨275175823186451854947929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2935208780655486452777909 275175823186451854947929)
                    ·
                      rfl

theorem cell23_1607709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_1607709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607709 prefixEnd_1607709 := by exact prefixLift 1607709
  have htrace : WordTrace (prefixWord ++ tailWord_1607709) baseStart_1607709 baseEnd_1607709 := by
    simpa [prefixWord, tailWord_1607709, baseEnd_1607709] using wordTrace_append hprefix tailTrace_1607709
  have hstable : (prefixWord ++ tailWord_1607709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607709).length < 2 ^ (prefixWord ++ tailWord_1607709).sum := by decide
  have hdescent : baseEnd_1607709 < baseStart_1607709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607722 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 3, 6]
def baseStart_1607722 : Nat := 118140960795 + 1607722 * 2 ^ 59
def prefixEnd_1607722 : Nat := 4983230072969 + 3 ^ 40 * 1607722 * 2
def baseEnd_1607722 : Nat := 275178048269288004660409

theorem tailTrace_1607722 : CollatzResearch.WordTrace tailWord_1607722 prefixEnd_1607722 275178048269288004660409 := by
  unfold tailWord_1607722
  simp only [CollatzResearch.WordTrace]
  refine ⟨14659609670376311475628355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39092292454336830601675613 14659609670376311475628355)
  ·
    refine ⟨21989414505564467213442533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14659609670376311475628355 21989414505564467213442533)
    ·
      refine ⟨4123015219793337602520475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21989414505564467213442533 4123015219793337602520475)
      ·
        refine ⟨6184522829690006403780713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4123015219793337602520475 6184522829690006403780713)
        ·
          refine ⟨4638392122267504802835535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6184522829690006403780713 4638392122267504802835535)
          ·
            refine ⟨6957588183401257204253303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4638392122267504802835535 6957588183401257204253303)
            ·
              refine ⟨10436382275101885806379955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6957588183401257204253303 10436382275101885806379955)
              ·
                refine ⟨15654573412652828709569933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10436382275101885806379955 15654573412652828709569933)
                ·
                  refine ⟨5870465029744810766088725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15654573412652828709569933 5870465029744810766088725)
                  ·
                    refine ⟨275178048269288004660409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5870465029744810766088725 275178048269288004660409)
                    ·
                      rfl

theorem cell23_1607722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_1607722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607722 prefixEnd_1607722 := by exact prefixLift 1607722
  have htrace : WordTrace (prefixWord ++ tailWord_1607722) baseStart_1607722 baseEnd_1607722 := by
    simpa [prefixWord, tailWord_1607722, baseEnd_1607722] using wordTrace_append hprefix tailTrace_1607722
  have hstable : (prefixWord ++ tailWord_1607722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607722).length < 2 ^ (prefixWord ++ tailWord_1607722).sum := by decide
  have hdescent : baseEnd_1607722 < baseStart_1607722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607726 : List Nat := [4, 1, 3, 1, 1, 3, 3, 1, 1, 5]
def baseStart_1607726 : Nat := 118140960795 + 1607726 * 2 ^ 59
def prefixEnd_1607726 : Nat := 4983230072969 + 3 ^ 40 * 1607726 * 2
def baseEnd_1607726 : Nat := 275178732910160666110403

theorem tailTrace_1607726 : CollatzResearch.WordTrace tailWord_1607726 prefixEnd_1607726 275178732910160666110403 := by
  unfold tailWord_1607726
  simp only [CollatzResearch.WordTrace]
  refine ⟨7329823071686344323207379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39092389715660503057106021 7329823071686344323207379)
  ·
    refine ⟨10994734607529516484811069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7329823071686344323207379 10994734607529516484811069)
    ·
      refine ⟨4123025477823568681804151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10994734607529516484811069 4123025477823568681804151)
      ·
        refine ⟨6184538216735353022706227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4123025477823568681804151 6184538216735353022706227)
        ·
          refine ⟨9276807325103029534059341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6184538216735353022706227 9276807325103029534059341)
          ·
            refine ⟨3478802746913636075272253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9276807325103029534059341 3478802746913636075272253)
            ·
              refine ⟨1304551030092613528227095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3478802746913636075272253 1304551030092613528227095)
              ·
                refine ⟨1956826545138920292340643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1304551030092613528227095 1956826545138920292340643)
                ·
                  refine ⟨2935239817708380438510965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1956826545138920292340643 2935239817708380438510965)
                  ·
                    refine ⟨275178732910160666110403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2935239817708380438510965 275178732910160666110403)
                    ·
                      rfl

theorem cell23_1607726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_1607726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607726 prefixEnd_1607726 := by exact prefixLift 1607726
  have htrace : WordTrace (prefixWord ++ tailWord_1607726) baseStart_1607726 baseEnd_1607726 := by
    simpa [prefixWord, tailWord_1607726, baseEnd_1607726] using wordTrace_append hprefix tailTrace_1607726
  have hstable : (prefixWord ++ tailWord_1607726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607726).length < 2 ^ (prefixWord ++ tailWord_1607726).sum := by decide
  have hdescent : baseEnd_1607726 < baseStart_1607726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607812 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 2, 6]
def baseStart_1607812 : Nat := 118140960795 + 1607812 * 2 ^ 59
def prefixEnd_1607812 : Nat := 4983230072969 + 3 ^ 40 * 1607812 * 2
def baseEnd_1607812 : Nat := 275193452688922887285271

theorem tailTrace_1607812 : CollatzResearch.WordTrace tailWord_1607812 prefixEnd_1607812 275193452688922887285271 := by
  unfold tailWord_1607812
  simp only [CollatzResearch.WordTrace]
  refine ⟨29320860625589595636644845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39094480834119460848859793 29320860625589595636644845)
  ·
    refine ⟨10995322734596098363741817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29320860625589595636644845 10995322734596098363741817)
    ·
      refine ⟨8246492050947073772806363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10995322734596098363741817 8246492050947073772806363)
      ·
        refine ⟨12369738076420610659209545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8246492050947073772806363 12369738076420610659209545)
        ·
          refine ⟨9277303557315457994407159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12369738076420610659209545 9277303557315457994407159)
          ·
            refine ⟨13915955335973186991610739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9277303557315457994407159 13915955335973186991610739)
            ·
              refine ⟨20873933003959780487416109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13915955335973186991610739 20873933003959780487416109)
              ·
                refine ⟨7827724876484917682781041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20873933003959780487416109 7827724876484917682781041)
                ·
                  refine ⟨5870793657363688262085781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7827724876484917682781041 5870793657363688262085781)
                  ·
                    refine ⟨275193452688922887285271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5870793657363688262085781 275193452688922887285271)
                    ·
                      rfl

theorem cell23_1607812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_1607812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607812 prefixEnd_1607812 := by exact prefixLift 1607812
  have htrace : WordTrace (prefixWord ++ tailWord_1607812) baseStart_1607812 baseEnd_1607812 := by
    simpa [prefixWord, tailWord_1607812, baseEnd_1607812] using wordTrace_append hprefix tailTrace_1607812
  have hstable : (prefixWord ++ tailWord_1607812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607812).length < 2 ^ (prefixWord ++ tailWord_1607812).sum := by decide
  have hdescent : baseEnd_1607812 < baseStart_1607812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607813 : List Nat := [1, 3, 1, 1, 5, 2, 3, 1, 2, 1, 3]
def baseStart_1607813 : Nat := 118140960795 + 1607813 * 2 ^ 59
def prefixEnd_1607813 : Nat := 4983230072969 + 3 ^ 40 * 1607813 * 2
def baseEnd_1607813 : Nat := 825580871547423157943309

theorem tailTrace_1607813 : CollatzResearch.WordTrace tailWord_1607813 prefixEnd_1607813 825580871547423157943309 := by
  unfold tailWord_1607813
  simp only [CollatzResearch.WordTrace]
  refine ⟨58641757724175568444076093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39094505149450378962717395 58641757724175568444076093)
  ·
    refine ⟨21990659146565838166528535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58641757724175568444076093 21990659146565838166528535)
    ·
      refine ⟨32985988719848757249792803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21990659146565838166528535 32985988719848757249792803)
      ·
        refine ⟨49478983079773135874689205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32985988719848757249792803 49478983079773135874689205)
        ·
          refine ⟨4638654663728731488252113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49478983079773135874689205 4638654663728731488252113)
          ·
            refine ⟨3478990997796548616189085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4638654663728731488252113 3478990997796548616189085)
            ·
              refine ⟨1304621624173705731070907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3478990997796548616189085 1304621624173705731070907)
              ·
                refine ⟨1956932436260558596606361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1304621624173705731070907 1956932436260558596606361)
                ·
                  refine ⟨1467699327195418947454771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1956932436260558596606361 1467699327195418947454771)
                  ·
                    refine ⟨2201548990793128421182157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1467699327195418947454771 2201548990793128421182157)
                    ·
                      refine ⟨825580871547423157943309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2201548990793128421182157 825580871547423157943309)
                      ·
                        rfl

theorem cell23_1607813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 2, 1, 3].length) (baseStart_1607813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607813 prefixEnd_1607813 := by exact prefixLift 1607813
  have htrace : WordTrace (prefixWord ++ tailWord_1607813) baseStart_1607813 baseEnd_1607813 := by
    simpa [prefixWord, tailWord_1607813, baseEnd_1607813] using wordTrace_append hprefix tailTrace_1607813
  have hstable : (prefixWord ++ tailWord_1607813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607813).length < 2 ^ (prefixWord ++ tailWord_1607813).sum := by decide
  have hdescent : baseEnd_1607813 < baseStart_1607813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607836 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 6, 2, 2]
def baseStart_1607836 : Nat := 118140960795 + 1607836 * 2 ^ 59
def prefixEnd_1607836 : Nat := 4983230072969 + 3 ^ 40 * 1607836 * 2
def baseEnd_1607836 : Nat := 825592681602476567955703

theorem tailTrace_1607836 : CollatzResearch.WordTrace tailWord_1607836 prefixEnd_1607836 825592681602476567955703 := by
  unfold tailWord_1607836
  simp only [CollatzResearch.WordTrace]
  refine ⟨29321298301546121686081681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39095064402061495581442241 29321298301546121686081681)
  ·
    refine ⟨21990973726159591264561261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29321298301546121686081681 21990973726159591264561261)
    ·
      refine ⟨8246615147309846724210473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21990973726159591264561261 8246615147309846724210473)
      ·
        refine ⟨6184961360482385043157855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8246615147309846724210473 6184961360482385043157855)
        ·
          refine ⟨9277442040723577564736783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6184961360482385043157855 9277442040723577564736783)
          ·
            refine ⟨13916163061085366347105175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9277442040723577564736783 13916163061085366347105175)
            ·
              refine ⟨20874244591628049520657763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13916163061085366347105175 20874244591628049520657763)
              ·
                refine ⟨31311366887442074280986645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20874244591628049520657763 31311366887442074280986645)
                ·
                  refine ⟨1467720322848847231921249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31311366887442074280986645 1467720322848847231921249)
                  ·
                    refine ⟨1100790242136635423940937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1467720322848847231921249 1100790242136635423940937)
                    ·
                      refine ⟨825592681602476567955703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1100790242136635423940937 825592681602476567955703)
                      ·
                        rfl

theorem cell23_1607836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_1607836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607836 prefixEnd_1607836 := by exact prefixLift 1607836
  have htrace : WordTrace (prefixWord ++ tailWord_1607836) baseStart_1607836 baseEnd_1607836 := by
    simpa [prefixWord, tailWord_1607836, baseEnd_1607836] using wordTrace_append hprefix tailTrace_1607836
  have hstable : (prefixWord ++ tailWord_1607836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607836).length < 2 ^ (prefixWord ++ tailWord_1607836).sum := by decide
  have hdescent : baseEnd_1607836 < baseStart_1607836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607839 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1607839 : Nat := 118140960795 + 1607839 * 2 ^ 59
def prefixEnd_1607839 : Nat := 4983230072969 + 3 ^ 40 * 1607839 * 2
def baseEnd_1607839 : Nat := 825594222044440056218189

theorem tailTrace_1607839 : CollatzResearch.WordTrace tailWord_1607839 prefixEnd_1607839 825594222044440056218189 := by
  unfold tailWord_1607839
  simp only [CollatzResearch.WordTrace]
  refine ⟨58642706022081374884522571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39095137348054249923015047 58642706022081374884522571)
  ·
    refine ⟨87964059033122062326783857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58642706022081374884522571 87964059033122062326783857)
    ·
      refine ⟨65973044274841546745087893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87964059033122062326783857 65973044274841546745087893)
      ·
        refine ⟨3092486450383197503675995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65973044274841546745087893 3092486450383197503675995)
        ·
          refine ⟨4638729675574796255513993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3092486450383197503675995 4638729675574796255513993)
          ·
            refine ⟨3479047256681097191635495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4638729675574796255513993 3479047256681097191635495)
            ·
              refine ⟨5218570885021645787453243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3479047256681097191635495 5218570885021645787453243)
              ·
                refine ⟨7827856327532468681179865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5218570885021645787453243 7827856327532468681179865)
                ·
                  refine ⟨5870892245649351510884899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7827856327532468681179865 5870892245649351510884899)
                  ·
                    refine ⟨8806338368474027266327349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5870892245649351510884899 8806338368474027266327349)
                    ·
                      refine ⟨825594222044440056218189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8806338368474027266327349 825594222044440056218189)
                      ·
                        rfl

theorem cell23_1607839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1607839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607839 prefixEnd_1607839 := by exact prefixLift 1607839
  have htrace : WordTrace (prefixWord ++ tailWord_1607839) baseStart_1607839 baseEnd_1607839 := by
    simpa [prefixWord, tailWord_1607839, baseEnd_1607839] using wordTrace_append hprefix tailTrace_1607839
  have hstable : (prefixWord ++ tailWord_1607839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607839).length < 2 ^ (prefixWord ++ tailWord_1607839).sum := by decide
  have hdescent : baseEnd_1607839 < baseStart_1607839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607853 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 4, 2, 2]
def baseStart_1607853 : Nat := 118140960795 + 1607853 * 2 ^ 59
def prefixEnd_1607853 : Nat := 4983230072969 + 3 ^ 40 * 1607853 * 2
def baseEnd_1607853 : Nat := 825601410773603001443125

theorem tailTrace_1607853 : CollatzResearch.WordTrace tailWord_1607853 prefixEnd_1607853 825601410773603001443125 := by
  unfold tailWord_1607853
  simp only [CollatzResearch.WordTrace]
  refine ⟨58643216644030655275532213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39095477762687103517021475 58643216644030655275532213)
  ·
    refine ⟨5497801560377873932081145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58643216644030655275532213 5497801560377873932081145)
    ·
      refine ⟨4123351170283405449060859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5497801560377873932081145 4123351170283405449060859)
      ·
        refine ⟨6185026755425108173591289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4123351170283405449060859 6185026755425108173591289)
        ·
          refine ⟨4638770066568831130193467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6185026755425108173591289 4638770066568831130193467)
          ·
            refine ⟨6958155099853246695290201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4638770066568831130193467 6958155099853246695290201)
            ·
              refine ⟨5218616324889935021467651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6958155099853246695290201 5218616324889935021467651)
              ·
                refine ⟨7827924487334902532201477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5218616324889935021467651 7827924487334902532201477)
                ·
                  refine ⟨1467735841375294224787777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7827924487334902532201477 1467735841375294224787777)
                  ·
                    refine ⟨1100801881031470668590833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1467735841375294224787777 1100801881031470668590833)
                    ·
                      refine ⟨825601410773603001443125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1100801881031470668590833 825601410773603001443125)
                      ·
                        rfl

theorem cell23_1607853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_1607853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607853 prefixEnd_1607853 := by exact prefixLift 1607853
  have htrace : WordTrace (prefixWord ++ tailWord_1607853) baseStart_1607853 baseEnd_1607853 := by
    simpa [prefixWord, tailWord_1607853, baseEnd_1607853] using wordTrace_append hprefix tailTrace_1607853
  have hstable : (prefixWord ++ tailWord_1607853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607853).length < 2 ^ (prefixWord ++ tailWord_1607853).sum := by decide
  have hdescent : baseEnd_1607853 < baseStart_1607853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607870 : List Nat := [4, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2]
def baseStart_1607870 : Nat := 118140960795 + 1607870 * 2 ^ 59
def prefixEnd_1607870 : Nat := 4983230072969 + 3 ^ 40 * 1607870 * 2
def baseEnd_1607870 : Nat := 825610139944729434930547

theorem tailTrace_1607870 : CollatzResearch.WordTrace tailWord_1607870 prefixEnd_1607870 825610139944729434930547 := by
  unfold tailWord_1607870
  simp only [CollatzResearch.WordTrace]
  refine ⟨7330479585621133397362633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39095891123312711452600709 7330479585621133397362633)
  ·
    refine ⟨5497859689215850048021975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7330479585621133397362633 5497859689215850048021975)
    ·
      refine ⟨8246789533823775072032963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5497859689215850048021975 8246789533823775072032963)
      ·
        refine ⟨12370184300735662608049445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8246789533823775072032963 12370184300735662608049445)
        ·
          refine ⟨2319409556387936739009271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12370184300735662608049445 2319409556387936739009271)
          ·
            refine ⟨3479114334581905108513907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319409556387936739009271 3479114334581905108513907)
            ·
              refine ⟨5218671501872857662770861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3479114334581905108513907 5218671501872857662770861)
              ·
                refine ⟨1957001813202321623539073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5218671501872857662770861 1957001813202321623539073)
                ·
                  refine ⟨1467751359901741217654305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1957001813202321623539073 1467751359901741217654305)
                  ·
                    refine ⟨1100813519926305913240729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1467751359901741217654305 1100813519926305913240729)
                    ·
                      refine ⟨825610139944729434930547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1100813519926305913240729 825610139944729434930547)
                      ·
                        rfl

theorem cell23_1607870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_1607870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607870 prefixEnd_1607870 := by exact prefixLift 1607870
  have htrace : WordTrace (prefixWord ++ tailWord_1607870) baseStart_1607870 baseEnd_1607870 := by
    simpa [prefixWord, tailWord_1607870, baseEnd_1607870] using wordTrace_append hprefix tailTrace_1607870
  have hstable : (prefixWord ++ tailWord_1607870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607870).length < 2 ^ (prefixWord ++ tailWord_1607870).sum := by decide
  have hdescent : baseEnd_1607870 < baseStart_1607870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607882 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_1607882 : Nat := 118140960795 + 1607882 * 2 ^ 59
def prefixEnd_1607882 : Nat := 4983230072969 + 3 ^ 40 * 1607882 * 2
def baseEnd_1607882 : Nat := 825616301712583387980491

theorem tailTrace_1607882 : CollatzResearch.WordTrace tailWord_1607882 prefixEnd_1607882 825616301712583387980491 := by
  unfold tailWord_1607882
  simp only [CollatzResearch.WordTrace]
  refine ⟨14661068590231398307084475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39096182907283728818891933 14661068590231398307084475)
  ·
    refine ⟨21991602885347097460626713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14661068590231398307084475 21991602885347097460626713)
    ·
      refine ⟨16493702164010323095470035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21991602885347097460626713 16493702164010323095470035)
      ·
        refine ⟨24740553246015484643205053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16493702164010323095470035 24740553246015484643205053)
        ·
          refine ⟨9277707467255806741201895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24740553246015484643205053 9277707467255806741201895)
          ·
            refine ⟨13916561200883710111802843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9277707467255806741201895 13916561200883710111802843)
            ·
              refine ⟨20874841801325565167704265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13916561200883710111802843 20874841801325565167704265)
              ·
                refine ⟨15656131350994173875778199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20874841801325565167704265 15656131350994173875778199)
                ·
                  refine ⟨23484197026491260813667299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15656131350994173875778199 23484197026491260813667299)
                  ·
                    refine ⟨35226295539736891220500949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23484197026491260813667299 35226295539736891220500949)
                    ·
                      refine ⟨825616301712583387980491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35226295539736891220500949 825616301712583387980491)
                      ·
                        rfl

theorem cell23_1607882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_1607882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607882 prefixEnd_1607882 := by exact prefixLift 1607882
  have htrace : WordTrace (prefixWord ++ tailWord_1607882) baseStart_1607882 baseEnd_1607882 := by
    simpa [prefixWord, tailWord_1607882, baseEnd_1607882] using wordTrace_append hprefix tailTrace_1607882
  have hstable : (prefixWord ++ tailWord_1607882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607882).length < 2 ^ (prefixWord ++ tailWord_1607882).sum := by decide
  have hdescent : baseEnd_1607882 < baseStart_1607882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607926 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2]
def baseStart_1607926 : Nat := 118140960795 + 1607926 * 2 ^ 59
def prefixEnd_1607926 : Nat := 4983230072969 + 3 ^ 40 * 1607926 * 2
def baseEnd_1607926 : Nat := 825638894861381215830289

theorem tailTrace_1607926 : CollatzResearch.WordTrace tailWord_1607926 prefixEnd_1607926 825638894861381215830289 := by
  unfold tailWord_1607926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3665367448297886796433727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39097252781844125828626421 3665367448297886796433727)
  ·
    refine ⟨5498051172446830194650591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3665367448297886796433727 5498051172446830194650591)
    ·
      refine ⟨8247076758670245291975887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5498051172446830194650591 8247076758670245291975887)
      ·
        refine ⟨12370615138005367937963831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8247076758670245291975887 12370615138005367937963831)
        ·
          refine ⟨18555922707008051906945747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12370615138005367937963831 18555922707008051906945747)
          ·
            refine ⟨27833884060512077860418621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18555922707008051906945747 27833884060512077860418621)
            ·
              refine ⟨10437706522692029197656983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27833884060512077860418621 10437706522692029197656983)
              ·
                refine ⟨15656559784038043796485475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10437706522692029197656983 15656559784038043796485475)
                ·
                  refine ⟨23484839676057065694728213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15656559784038043796485475 23484839676057065694728213)
                  ·
                    refine ⟨1100851859815174954440385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23484839676057065694728213 1100851859815174954440385)
                    ·
                      refine ⟨825638894861381215830289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1100851859815174954440385 825638894861381215830289)
                      ·
                        rfl

theorem cell23_1607926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_1607926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607926 prefixEnd_1607926 := by exact prefixLift 1607926
  have htrace : WordTrace (prefixWord ++ tailWord_1607926) baseStart_1607926 baseEnd_1607926 := by
    simpa [prefixWord, tailWord_1607926, baseEnd_1607926] using wordTrace_append hprefix tailTrace_1607926
  have hstable : (prefixWord ++ tailWord_1607926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607926).length < 2 ^ (prefixWord ++ tailWord_1607926).sum := by decide
  have hdescent : baseEnd_1607926 < baseStart_1607926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607946 : List Nat := [3, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3]
def baseStart_1607946 : Nat := 118140960795 + 1607946 * 2 ^ 59
def prefixEnd_1607946 : Nat := 4983230072969 + 3 ^ 40 * 1607946 * 2
def baseEnd_1607946 : Nat := 825649164474471137580197

theorem tailTrace_1607946 : CollatzResearch.WordTrace tailWord_1607946 prefixEnd_1607946 825649164474471137580197 := by
  unfold tailWord_1607946
  simp only [CollatzResearch.WordTrace]
  refine ⟨14661652158173433039666923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39097739088462488105778461 14661652158173433039666923)
  ·
    refine ⟨21992478237260149559500385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14661652158173433039666923 21992478237260149559500385)
    ·
      refine ⟨16494358677945112169625289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21992478237260149559500385 16494358677945112169625289)
      ·
        refine ⟨12370769008458834127218967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16494358677945112169625289 12370769008458834127218967)
        ·
          refine ⟨18556153512688251190828451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12370769008458834127218967 18556153512688251190828451)
          ·
            refine ⟨27834230269032376786242677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18556153512688251190828451 27834230269032376786242677)
            ·
              refine ⟨2609459087721785323710251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27834230269032376786242677 2609459087721785323710251)
              ·
                refine ⟨3914188631582677985565377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2609459087721785323710251 3914188631582677985565377)
                ·
                  refine ⟨2935641473687008489174033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3914188631582677985565377 2935641473687008489174033)
                  ·
                    refine ⟨2201731105265256366880525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2935641473687008489174033 2201731105265256366880525)
                    ·
                      refine ⟨825649164474471137580197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2201731105265256366880525 825649164474471137580197)
                      ·
                        rfl

theorem cell23_1607946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_1607946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607946 prefixEnd_1607946 := by exact prefixLift 1607946
  have htrace : WordTrace (prefixWord ++ tailWord_1607946) baseStart_1607946 baseEnd_1607946 := by
    simpa [prefixWord, tailWord_1607946, baseEnd_1607946] using wordTrace_append hprefix tailTrace_1607946
  have hstable : (prefixWord ++ tailWord_1607946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607946).length < 2 ^ (prefixWord ++ tailWord_1607946).sum := by decide
  have hdescent : baseEnd_1607946 < baseStart_1607946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607953 : List Nat := [1, 2, 2, 1, 1, 6, 2, 3, 1, 4]
def baseStart_1607953 : Nat := 118140960795 + 1607953 * 2 ^ 59
def prefixEnd_1607953 : Nat := 4983230072969 + 3 ^ 40 * 1607953 * 2
def baseEnd_1607953 : Nat := 275217586279684203397555

theorem tailTrace_1607953 : CollatzResearch.WordTrace tailWord_1607953 prefixEnd_1607953 275217586279684203397555 := by
  unfold tailWord_1607953
  simp only [CollatzResearch.WordTrace]
  refine ⟨58646863943668372354172513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39097909295778914902781675 58646863943668372354172513)
  ·
    refine ⟨43985147957751279265629385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58646863943668372354172513 43985147957751279265629385)
    ·
      refine ⟨32988860968313459449222039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43985147957751279265629385 32988860968313459449222039)
      ·
        refine ⟨49483291452470189173833059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32988860968313459449222039 49483291452470189173833059)
        ·
          refine ⟨74224937178705283760749589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49483291452470189173833059 74224937178705283760749589)
          ·
            refine ⟨3479293930251810176285137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74224937178705283760749589 3479293930251810176285137)
            ·
              refine ⟨2609470447688857632213853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3479293930251810176285137 2609470447688857632213853)
              ·
                refine ⟨978551417883321612080195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2609470447688857632213853 978551417883321612080195)
                ·
                  refine ⟨1467827126824982418120293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 978551417883321612080195 1467827126824982418120293)
                  ·
                    refine ⟨275217586279684203397555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1467827126824982418120293 275217586279684203397555)
                    ·
                      rfl

theorem cell23_1607953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 1, 4].length) (baseStart_1607953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607953 prefixEnd_1607953 := by exact prefixLift 1607953
  have htrace : WordTrace (prefixWord ++ tailWord_1607953) baseStart_1607953 baseEnd_1607953 := by
    simpa [prefixWord, tailWord_1607953, baseEnd_1607953] using wordTrace_append hprefix tailTrace_1607953
  have hstable : (prefixWord ++ tailWord_1607953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607953).length < 2 ^ (prefixWord ++ tailWord_1607953).sum := by decide
  have hdescent : baseEnd_1607953 < baseStart_1607953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607993 : List Nat := [1, 2, 1, 6, 1, 1, 2, 2, 3, 1, 3]
def baseStart_1607993 : Nat := 118140960795 + 1607993 * 2 ^ 59
def prefixEnd_1607993 : Nat := 4983230072969 + 3 ^ 40 * 1607993 * 2
def baseEnd_1607993 : Nat := 825673298065232453692481

theorem tailTrace_1607993 : CollatzResearch.WordTrace tailWord_1607993 prefixEnd_1607993 825673298065232453692481 := by
  unfold tailWord_1607993
  simp only [CollatzResearch.WordTrace]
  refine ⟨58648322863523459185628633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39098881909015639457085755 58648322863523459185628633)
  ·
    refine ⟨43986242147642594389221475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58648322863523459185628633 43986242147642594389221475)
    ·
      refine ⟨65979363221463891583832213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43986242147642594389221475 65979363221463891583832213)
      ·
        refine ⟨3092782651006119917992135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65979363221463891583832213 3092782651006119917992135)
        ·
          refine ⟨4639173976509179876988203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3092782651006119917992135 4639173976509179876988203)
          ·
            refine ⟨6958760964763769815482305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4639173976509179876988203 6958760964763769815482305)
            ·
              refine ⟨5219070723572827361611729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6958760964763769815482305 5219070723572827361611729)
              ·
                refine ⟨3914303042679620521208797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5219070723572827361611729 3914303042679620521208797)
                ·
                  refine ⟨1467863641004857695453299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3914303042679620521208797 1467863641004857695453299)
                  ·
                    refine ⟨2201795461507286543179949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1467863641004857695453299 2201795461507286543179949)
                    ·
                      refine ⟨825673298065232453692481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2201795461507286543179949 825673298065232453692481)
                      ·
                        rfl

theorem cell23_1607993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_1607993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607993 prefixEnd_1607993 := by exact prefixLift 1607993
  have htrace : WordTrace (prefixWord ++ tailWord_1607993) baseStart_1607993 baseEnd_1607993 := by
    simpa [prefixWord, tailWord_1607993, baseEnd_1607993] using wordTrace_append hprefix tailTrace_1607993
  have hstable : (prefixWord ++ tailWord_1607993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607993).length < 2 ^ (prefixWord ++ tailWord_1607993).sum := by decide
  have hdescent : baseEnd_1607993 < baseStart_1607993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1607996 : List Nat := [2, 2, 2, 2, 1, 2, 4, 2, 1, 5]
def baseStart_1607996 : Nat := 118140960795 + 1607996 * 2 ^ 59
def prefixEnd_1607996 : Nat := 4983230072969 + 3 ^ 40 * 1607996 * 2
def baseEnd_1607996 : Nat := 275224946169065313984989

theorem tailTrace_1607996 : CollatzResearch.WordTrace tailWord_1607996 prefixEnd_1607996 275224946169065313984989 := by
  unfold tailWord_1607996
  simp only [CollatzResearch.WordTrace]
  refine ⟨29324216141256295348993921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39098954855008393798658561 29324216141256295348993921)
  ·
    refine ⟨21993162105942221511745441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29324216141256295348993921 21993162105942221511745441)
    ·
      refine ⟨16494871579456666133809081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21993162105942221511745441 16494871579456666133809081)
      ·
        refine ⟨12371153684592499600356811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16494871579456666133809081 12371153684592499600356811)
        ·
          refine ⟨18556730526888749400535217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12371153684592499600356811 18556730526888749400535217)
          ·
            refine ⟨13917547895166562050401413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18556730526888749400535217 13917547895166562050401413)
            ·
              refine ⟨2609540230343730384450265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13917547895166562050401413 2609540230343730384450265)
              ·
                refine ⟨1957155172757797788337699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2609540230343730384450265 1957155172757797788337699)
                ·
                  refine ⟨2935732759136696682506549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1957155172757797788337699 2935732759136696682506549)
                  ·
                    refine ⟨275224946169065313984989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2935732759136696682506549 275224946169065313984989)
                    ·
                      rfl

theorem cell23_1607996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_1607996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1607996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1607996 prefixEnd_1607996 := by exact prefixLift 1607996
  have htrace : WordTrace (prefixWord ++ tailWord_1607996) baseStart_1607996 baseEnd_1607996 := by
    simpa [prefixWord, tailWord_1607996, baseEnd_1607996] using wordTrace_append hprefix tailTrace_1607996
  have hstable : (prefixWord ++ tailWord_1607996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1607996).length < 2 ^ (prefixWord ++ tailWord_1607996).sum := by decide
  have hdescent : baseEnd_1607996 < baseStart_1607996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1607996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608004 : List Nat := [2, 3, 4, 1, 3, 1, 1, 3, 1, 4]
def baseStart_1608004 : Nat := 118140960795 + 1608004 * 2 ^ 59
def prefixEnd_1608004 : Nat := 4983230072969 + 3 ^ 40 * 1608004 * 2
def baseEnd_1608004 : Nat := 275226315450810636884977

theorem tailTrace_1608004 : CollatzResearch.WordTrace tailWord_1608004 prefixEnd_1608004 275226315450810636884977 := by
  unfold tailWord_1608004
  simp only [CollatzResearch.WordTrace]
  refine ⟨29324362033241804032139533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39099149377655738709519377 29324362033241804032139533)
  ·
    refine ⟨10996635762465676512052325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29324362033241804032139533 10996635762465676512052325)
    ·
      refine ⟨2061869205462314346009811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10996635762465676512052325 2061869205462314346009811)
      ·
        refine ⟨3092803808193471519014717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2061869205462314346009811 3092803808193471519014717)
        ·
          refine ⟨1159801428072551819630519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3092803808193471519014717 1159801428072551819630519)
          ·
            refine ⟨1739702142108827729445779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159801428072551819630519 1739702142108827729445779)
            ·
              refine ⟨2609553213163241594168669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1739702142108827729445779 2609553213163241594168669)
              ·
                refine ⟨978582454936215597813251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2609553213163241594168669 978582454936215597813251)
                ·
                  refine ⟨1467873682404323396719877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 978582454936215597813251 1467873682404323396719877)
                  ·
                    refine ⟨275226315450810636884977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1467873682404323396719877 275226315450810636884977)
                    ·
                      rfl

theorem cell23_1608004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_1608004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608004 prefixEnd_1608004 := by exact prefixLift 1608004
  have htrace : WordTrace (prefixWord ++ tailWord_1608004) baseStart_1608004 baseEnd_1608004 := by
    simpa [prefixWord, tailWord_1608004, baseEnd_1608004] using wordTrace_append hprefix tailTrace_1608004
  have hstable : (prefixWord ++ tailWord_1608004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608004).length < 2 ^ (prefixWord ++ tailWord_1608004).sum := by decide
  have hdescent : baseEnd_1608004 < baseStart_1608004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608016 : List Nat := [2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 4]
def baseStart_1608016 : Nat := 118140960795 + 1608016 * 2 ^ 59
def prefixEnd_1608016 : Nat := 4983230072969 + 3 ^ 40 * 1608016 * 2
def baseEnd_1608016 : Nat := 825685108120285863704875

theorem tailTrace_1608016 : CollatzResearch.WordTrace tailWord_1608016 prefixEnd_1608016 825685108120285863704875 := by
  unfold tailWord_1608016
  simp only [CollatzResearch.WordTrace]
  refine ⟨29324580871220067056857951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39099441161626756075810601 29324580871220067056857951)
  ·
    refine ⟨43986871306830100585286927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29324580871220067056857951 43986871306830100585286927)
    ·
      refine ⟨65980306960245150877930391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43986871306830100585286927 65980306960245150877930391)
      ·
        refine ⟨98970460440367726316895587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65980306960245150877930391 98970460440367726316895587)
        ·
          refine ⟨148455690660551589475343381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98970460440367726316895587 148455690660551589475343381)
          ·
            refine ⟨6958860499713355756656721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 148455690660551589475343381 6958860499713355756656721)
            ·
              refine ⟨5219145374785016817492541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6958860499713355756656721 5219145374785016817492541)
              ·
                refine ⟨1957179515544381306559703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5219145374785016817492541 1957179515544381306559703)
                ·
                  refine ⟨2935769273316571959839555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1957179515544381306559703 2935769273316571959839555)
                  ·
                    refine ⟨4403653909974857939759333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2935769273316571959839555 4403653909974857939759333)
                    ·
                      refine ⟨825685108120285863704875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4403653909974857939759333 825685108120285863704875)
                      ·
                        rfl

theorem cell23_1608016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 4].length) (baseStart_1608016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608016 prefixEnd_1608016 := by exact prefixLift 1608016
  have htrace : WordTrace (prefixWord ++ tailWord_1608016) baseStart_1608016 baseEnd_1608016 := by
    simpa [prefixWord, tailWord_1608016, baseEnd_1608016] using wordTrace_append hprefix tailTrace_1608016
  have hstable : (prefixWord ++ tailWord_1608016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608016).length < 2 ^ (prefixWord ++ tailWord_1608016).sum := by decide
  have hdescent : baseEnd_1608016 < baseStart_1608016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608026 : List Nat := [3, 1, 1, 2, 1, 2, 1, 6, 2, 4]
def baseStart_1608026 : Nat := 118140960795 + 1608026 * 2 ^ 59
def prefixEnd_1608026 : Nat := 4983230072969 + 3 ^ 40 * 1608026 * 2
def baseEnd_1608026 : Nat := 275230080975610274859943

theorem tailTrace_1608026 : CollatzResearch.WordTrace tailWord_1608026 prefixEnd_1608026 275230080975610274859943 := by
  unfold tailWord_1608026
  simp only [CollatzResearch.WordTrace]
  refine ⟨14662381618100976455394983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39099684314935937214386621 14662381618100976455394983)
  ·
    refine ⟨21993572427151464683092475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14662381618100976455394983 21993572427151464683092475)
    ·
      refine ⟨32990358640727197024638713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21993572427151464683092475 32990358640727197024638713)
      ·
        refine ⟨24742768980545397768479035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32990358640727197024638713 24742768980545397768479035)
        ·
          refine ⟨37114153470818096652718553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24742768980545397768479035 37114153470818096652718553)
          ·
            refine ⟨27835615103113572489538915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37114153470818096652718553 27835615103113572489538915)
            ·
              refine ⟨41753422654670358734308373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27835615103113572489538915 41753422654670358734308373)
              ·
                refine ⟨1957191686937673065670705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41753422654670358734308373 1957191686937673065670705)
                ·
                  refine ⟨1467893765203254799253029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1957191686937673065670705 1467893765203254799253029)
                  ·
                    refine ⟨275230080975610274859943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1467893765203254799253029 275230080975610274859943)
                    ·
                      rfl

theorem cell23_1608026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 2, 4].length) (baseStart_1608026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608026 prefixEnd_1608026 := by exact prefixLift 1608026
  have htrace : WordTrace (prefixWord ++ tailWord_1608026) baseStart_1608026 baseEnd_1608026 := by
    simpa [prefixWord, tailWord_1608026, baseEnd_1608026] using wordTrace_append hprefix tailTrace_1608026
  have hstable : (prefixWord ++ tailWord_1608026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608026).length < 2 ^ (prefixWord ++ tailWord_1608026).sum := by decide
  have hdescent : baseEnd_1608026 < baseStart_1608026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608036 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 3, 2, 3]
def baseStart_1608036 : Nat := 118140960795 + 1608036 * 2 ^ 59
def prefixEnd_1608036 : Nat := 4983230072969 + 3 ^ 40 * 1608036 * 2
def baseEnd_1608036 : Nat := 825695377733375785454783

theorem tailTrace_1608036 : CollatzResearch.WordTrace tailWord_1608036 prefixEnd_1608036 825695377733375785454783 := by
  unfold tailWord_1608036
  simp only [CollatzResearch.WordTrace]
  refine ⟨29324945601183838764721981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39099927468245118352962641 29324945601183838764721981)
  ·
    refine ⟨10996854600443939536770743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29324945601183838764721981 10996854600443939536770743)
    ·
      refine ⟨16495281900665909305156115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10996854600443939536770743 16495281900665909305156115)
      ·
        refine ⟨24742922850998863957734173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16495281900665909305156115 24742922850998863957734173)
        ·
          refine ⟨9278596069124573984150315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24742922850998863957734173 9278596069124573984150315)
          ·
            refine ⟨13917894103686860976225473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9278596069124573984150315 13917894103686860976225473)
            ·
              refine ⟨10438420577765145732169105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13917894103686860976225473 10438420577765145732169105)
              ·
                refine ⟨7828815433323859299126829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10438420577765145732169105 7828815433323859299126829)
                ·
                  refine ⟨2935805787496447237172561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7828815433323859299126829 2935805787496447237172561)
                  ·
                    refine ⟨2201854340622335427879421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2935805787496447237172561 2201854340622335427879421)
                    ·
                      refine ⟨825695377733375785454783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2201854340622335427879421 825695377733375785454783)
                      ·
                        rfl

theorem cell23_1608036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_1608036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608036 prefixEnd_1608036 := by exact prefixLift 1608036
  have htrace : WordTrace (prefixWord ++ tailWord_1608036) baseStart_1608036 baseEnd_1608036 := by
    simpa [prefixWord, tailWord_1608036, baseEnd_1608036] using wordTrace_append hprefix tailTrace_1608036
  have hstable : (prefixWord ++ tailWord_1608036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608036).length < 2 ^ (prefixWord ++ tailWord_1608036).sum := by decide
  have hdescent : baseEnd_1608036 < baseStart_1608036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608039 : List Nat := [1, 1, 5, 1, 3, 1, 1, 10]
def baseStart_1608039 : Nat := 118140960795 + 1608039 * 2 ^ 59
def prefixEnd_1608039 : Nat := 4983230072969 + 3 ^ 40 * 1608039 * 2
def baseEnd_1608039 : Nat := 30581367339827380508047

theorem tailTrace_1608039 : CollatzResearch.WordTrace tailWord_1608039 prefixEnd_1608039 30581367339827380508047 := by
  unfold tailWord_1608039
  simp only [CollatzResearch.WordTrace]
  refine ⟨58650000621356809041803171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39100000414237872694535447 58650000621356809041803171)
  ·
    refine ⟨87975000932035213562704757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58650000621356809041803171 87975000932035213562704757)
    ·
      refine ⟨8247656337378301271503571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87975000932035213562704757 8247656337378301271503571)
      ·
        refine ⟨12371484506067451907255357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8247656337378301271503571 12371484506067451907255357)
        ·
          refine ⟨4639306689775294465220759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12371484506067451907255357 4639306689775294465220759)
          ·
            refine ⟨6958960034662941697831139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4639306689775294465220759 6958960034662941697831139)
            ·
              refine ⟨10438440051994412546746709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6958960034662941697831139 10438440051994412546746709)
              ·
                refine ⟨30581367339827380508047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10438440051994412546746709 30581367339827380508047)
                ·
                  rfl

theorem cell23_1608039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 10].length) (baseStart_1608039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608039 prefixEnd_1608039 := by exact prefixLift 1608039
  have htrace : WordTrace (prefixWord ++ tailWord_1608039) baseStart_1608039 baseEnd_1608039 := by
    simpa [prefixWord, tailWord_1608039, baseEnd_1608039] using wordTrace_append hprefix tailTrace_1608039
  have hstable : (prefixWord ++ tailWord_1608039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608039).length < 2 ^ (prefixWord ++ tailWord_1608039).sum := by decide
  have hdescent : baseEnd_1608039 < baseStart_1608039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608053 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_1608053 : Nat := 118140960795 + 1608053 * 2 ^ 59
def prefixEnd_1608053 : Nat := 4983230072969 + 3 ^ 40 * 1608053 * 2
def baseEnd_1608053 : Nat := 825704106904502218942205

theorem tailTrace_1608053 : CollatzResearch.WordTrace tailWord_1608053 prefixEnd_1608053 825704106904502218942205 := by
  unfold tailWord_1608053
  simp only [CollatzResearch.WordTrace]
  refine ⟨58650511243306089432812813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39100340828870726288541875 58650511243306089432812813)
  ·
    refine ⟨21993941716239783537304805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58650511243306089432812813 21993941716239783537304805)
    ·
      refine ⟨4123864071794959413244651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21993941716239783537304805 4123864071794959413244651)
      ·
        refine ⟨6185796107692439119866977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4123864071794959413244651 6185796107692439119866977)
        ·
          refine ⟨4639347080769329339900233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6185796107692439119866977 4639347080769329339900233)
          ·
            refine ⟨3479510310576997004925175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4639347080769329339900233 3479510310576997004925175)
            ·
              refine ⟨5219265465865495507387763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3479510310576997004925175 5219265465865495507387763)
              ·
                refine ⟨7828898198798243261081645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5219265465865495507387763 7828898198798243261081645)
                ·
                  refine ⟨2935836824549341222905617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7828898198798243261081645 2935836824549341222905617)
                  ·
                    refine ⟨2201877618412005917179213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2935836824549341222905617 2201877618412005917179213)
                    ·
                      refine ⟨825704106904502218942205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2201877618412005917179213 825704106904502218942205)
                      ·
                        rfl

theorem cell23_1608053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_1608053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608053 prefixEnd_1608053 := by exact prefixLift 1608053
  have htrace : WordTrace (prefixWord ++ tailWord_1608053) baseStart_1608053 baseEnd_1608053 := by
    simpa [prefixWord, tailWord_1608053, baseEnd_1608053] using wordTrace_append hprefix tailTrace_1608053
  have hstable : (prefixWord ++ tailWord_1608053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608053).length < 2 ^ (prefixWord ++ tailWord_1608053).sum := by decide
  have hdescent : baseEnd_1608053 < baseStart_1608053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608084 : List Nat := [2, 4, 2, 1, 3, 1, 1, 4, 1, 2, 2]
def baseStart_1608084 : Nat := 118140960795 + 1608084 * 2 ^ 59
def prefixEnd_1608084 : Nat := 4983230072969 + 3 ^ 40 * 1608084 * 2
def baseEnd_1608084 : Nat := 825720024804791597654563

theorem tailTrace_1608084 : CollatzResearch.WordTrace tailWord_1608084 prefixEnd_1608084 825720024804791597654563 := by
  unfold tailWord_1608084
  simp only [CollatzResearch.WordTrace]
  refine ⟨29325820953096890863595653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39101094604129187818127537 29325820953096890863595653)
  ·
    refine ⟨5498591428705667036924185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29325820953096890863595653 5498591428705667036924185)
    ·
      refine ⟨4123943571529250277693139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5498591428705667036924185 4123943571529250277693139)
      ·
        refine ⟨6185915357293875416539709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4123943571529250277693139 6185915357293875416539709)
        ·
          refine ⟨2319718258985203281202391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6185915357293875416539709 2319718258985203281202391)
          ·
            refine ⟨3479577388477804921803587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319718258985203281202391 3479577388477804921803587)
            ·
              refine ⟨5219366082716707382705381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3479577388477804921803587 5219366082716707382705381)
              ·
                refine ⟨978631140509382634257259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5219366082716707382705381 978631140509382634257259)
                ·
                  refine ⟨1467946710764073951385889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 978631140509382634257259 1467946710764073951385889)
                  ·
                    refine ⟨1100960033073055463539417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1467946710764073951385889 1100960033073055463539417)
                    ·
                      refine ⟨825720024804791597654563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1100960033073055463539417 825720024804791597654563)
                      ·
                        rfl

theorem cell23_1608084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_1608084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608084 prefixEnd_1608084 := by exact prefixLift 1608084
  have htrace : WordTrace (prefixWord ++ tailWord_1608084) baseStart_1608084 baseEnd_1608084 := by
    simpa [prefixWord, tailWord_1608084, baseEnd_1608084] using wordTrace_append hprefix tailTrace_1608084
  have hstable : (prefixWord ++ tailWord_1608084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608084).length < 2 ^ (prefixWord ++ tailWord_1608084).sum := by decide
  have hdescent : baseEnd_1608084 < baseStart_1608084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608089 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 1, 5, 4]
def baseStart_1608089 : Nat := 118140960795 + 1608089 * 2 ^ 59
def prefixEnd_1608089 : Nat := 4983230072969 + 3 ^ 40 * 1608089 * 2
def baseEnd_1608089 : Nat := 825722592208064078092039

theorem tailTrace_1608089 : CollatzResearch.WordTrace tailWord_1608089 prefixEnd_1608089 825722592208064078092039 := by
  unfold tailWord_1608089
  simp only [CollatzResearch.WordTrace]
  refine ⟨58651824271175667581123321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39101216180783778387415547 58651824271175667581123321)
  ·
    refine ⟨43988868203381750685842491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58651824271175667581123321 43988868203381750685842491)
    ·
      refine ⟨65983302305072626028763737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43988868203381750685842491 65983302305072626028763737)
      ·
        refine ⟨49487476728804469521572803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65983302305072626028763737 49487476728804469521572803)
        ·
          refine ⟨74231215093206704282359205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49487476728804469521572803 74231215093206704282359205)
          ·
            refine ⟨13918352829976257052942351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74231215093206704282359205 13918352829976257052942351)
            ·
              refine ⟨20877529244964385579413527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13918352829976257052942351 20877529244964385579413527)
              ·
                refine ⟨31316293867446578369120291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20877529244964385579413527 31316293867446578369120291)
                ·
                  refine ⟨46974440801169867553680437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31316293867446578369120291 46974440801169867553680437)
                  ·
                    refine ⟨4403853825109675083157541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46974440801169867553680437 4403853825109675083157541)
                    ·
                      refine ⟨825722592208064078092039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4403853825109675083157541 825722592208064078092039)
                      ·
                        rfl

theorem cell23_1608089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_1608089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608089 prefixEnd_1608089 := by exact prefixLift 1608089
  have htrace : WordTrace (prefixWord ++ tailWord_1608089) baseStart_1608089 baseEnd_1608089 := by
    simpa [prefixWord, tailWord_1608089, baseEnd_1608089] using wordTrace_append hprefix tailTrace_1608089
  have hstable : (prefixWord ++ tailWord_1608089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608089).length < 2 ^ (prefixWord ++ tailWord_1608089).sum := by decide
  have hdescent : baseEnd_1608089 < baseStart_1608089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608099 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 1, 8]
def baseStart_1608099 : Nat := 118140960795 + 1608099 * 2 ^ 59
def prefixEnd_1608099 : Nat := 4983230072969 + 3 ^ 40 * 1608099 * 2
def baseEnd_1608099 : Nat := 275242575671536346322331

theorem tailTrace_1608099 : CollatzResearch.WordTrace tailWord_1608099 prefixEnd_1608099 275242575671536346322331 := by
  unfold tailWord_1608099
  simp only [CollatzResearch.WordTrace]
  refine ⟨58652189001139439288987351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39101459334092959525991567 58652189001139439288987351)
  ·
    refine ⟨87978283501709158933481027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58652189001139439288987351 87978283501709158933481027)
    ·
      refine ⟨131967425252563738400221541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87978283501709158933481027 131967425252563738400221541)
      ·
        refine ⟨24743892234855700950041539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131967425252563738400221541 24743892234855700950041539)
        ·
          refine ⟨37115838352283551425062309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24743892234855700950041539 37115838352283551425062309)
          ·
            refine ⟨6959219691053165892199183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37115838352283551425062309 6959219691053165892199183)
            ·
              refine ⟨10438829536579748838298775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6959219691053165892199183 10438829536579748838298775)
              ·
                refine ⟨15658244304869623257448163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10438829536579748838298775 15658244304869623257448163)
                ·
                  refine ⟨23487366457304434886172245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15658244304869623257448163 23487366457304434886172245)
                  ·
                    refine ⟨275242575671536346322331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23487366457304434886172245 275242575671536346322331)
                    ·
                      rfl

theorem cell23_1608099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 8].length) (baseStart_1608099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608099 prefixEnd_1608099 := by exact prefixLift 1608099
  have htrace : WordTrace (prefixWord ++ tailWord_1608099) baseStart_1608099 baseEnd_1608099 := by
    simpa [prefixWord, tailWord_1608099, baseEnd_1608099] using wordTrace_append hprefix tailTrace_1608099
  have hstable : (prefixWord ++ tailWord_1608099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608099).length < 2 ^ (prefixWord ++ tailWord_1608099).sum := by decide
  have hdescent : baseEnd_1608099 < baseStart_1608099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608126 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_1608126 : Nat := 118140960795 + 1608126 * 2 ^ 59
def prefixEnd_1608126 : Nat := 4983230072969 + 3 ^ 40 * 1608126 * 2
def baseEnd_1608126 : Nat := 825741590992280433329369

theorem tailTrace_1608126 : CollatzResearch.WordTrace tailWord_1608126 prefixEnd_1608126 825741590992280433329369 := by
  unfold tailWord_1608126
  simp only [CollatzResearch.WordTrace]
  refine ⟨7331646721505202862527529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39102115848027748600146821 7331646721505202862527529)
  ·
    refine ⟨5498735041128902146895647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7331646721505202862527529 5498735041128902146895647)
    ·
      refine ⟨8248102561693353220343471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5498735041128902146895647 8248102561693353220343471)
      ·
        refine ⟨12372153842540029830515207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8248102561693353220343471 12372153842540029830515207)
        ·
          refine ⟨18558230763810044745772811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12372153842540029830515207 18558230763810044745772811)
          ·
            refine ⟨27837346145715067118659217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18558230763810044745772811 27837346145715067118659217)
            ·
              refine ⟨20878009609286300338994413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27837346145715067118659217 20878009609286300338994413)
              ·
                refine ⟨7829253603482362627122905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20878009609286300338994413 7829253603482362627122905)
                ·
                  refine ⟨5871940202611771970342179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7829253603482362627122905 5871940202611771970342179)
                  ·
                    refine ⟨8807910303917657955513269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5871940202611771970342179 8807910303917657955513269)
                    ·
                      refine ⟨825741590992280433329369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8807910303917657955513269 825741590992280433329369)
                      ·
                        rfl

theorem cell23_1608126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_1608126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608126 prefixEnd_1608126 := by exact prefixLift 1608126
  have htrace : WordTrace (prefixWord ++ tailWord_1608126) baseStart_1608126 baseEnd_1608126 := by
    simpa [prefixWord, tailWord_1608126, baseEnd_1608126] using wordTrace_append hprefix tailTrace_1608126
  have hstable : (prefixWord ++ tailWord_1608126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608126).length < 2 ^ (prefixWord ++ tailWord_1608126).sum := by decide
  have hdescent : baseEnd_1608126 < baseStart_1608126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608136 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 2, 2, 4]
def baseStart_1608136 : Nat := 118140960795 + 1608136 * 2 ^ 59
def prefixEnd_1608136 : Nat := 4983230072969 + 3 ^ 40 * 1608136 * 2
def baseEnd_1608136 : Nat := 825746725798825394204323

theorem tailTrace_1608136 : CollatzResearch.WordTrace tailWord_1608136 prefixEnd_1608136 825746725798825394204323 := by
  unfold tailWord_1608136
  simp only [CollatzResearch.WordTrace]
  refine ⟨29326769251002697304042131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39102359001336929738722841 29326769251002697304042131)
  ·
    refine ⟨43990153876504045956063197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29326769251002697304042131 43990153876504045956063197)
    ·
      refine ⟨16496307703689017233523699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43990153876504045956063197 16496307703689017233523699)
      ·
        refine ⟨24744461555533525850285549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16496307703689017233523699 24744461555533525850285549)
        ·
          refine ⟨9279173083325072193857081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24744461555533525850285549 9279173083325072193857081)
          ·
            refine ⟨6959379812493804145392811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9279173083325072193857081 6959379812493804145392811)
            ·
              refine ⟨10439069718740706218089217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6959379812493804145392811 10439069718740706218089217)
              ·
                refine ⟨7829302289055529663566913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10439069718740706218089217 7829302289055529663566913)
                ·
                  refine ⟨5871976716791647247675185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7829302289055529663566913 5871976716791647247675185)
                  ·
                    refine ⟨4403982537593735435756389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5871976716791647247675185 4403982537593735435756389)
                    ·
                      refine ⟨825746725798825394204323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4403982537593735435756389 825746725798825394204323)
                      ·
                        rfl

theorem cell23_1608136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_1608136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608136 prefixEnd_1608136 := by exact prefixLift 1608136
  have htrace : WordTrace (prefixWord ++ tailWord_1608136) baseStart_1608136 baseEnd_1608136 := by
    simpa [prefixWord, tailWord_1608136, baseEnd_1608136] using wordTrace_append hprefix tailTrace_1608136
  have hstable : (prefixWord ++ tailWord_1608136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608136).length < 2 ^ (prefixWord ++ tailWord_1608136).sum := by decide
  have hdescent : baseEnd_1608136 < baseStart_1608136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608169 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 3, 1, 7]
def baseStart_1608169 : Nat := 118140960795 + 1608169 * 2 ^ 59
def prefixEnd_1608169 : Nat := 4983230072969 + 3 ^ 40 * 1608169 * 2
def baseEnd_1608169 : Nat := 825763670660423765091671

theorem tailTrace_1608169 : CollatzResearch.WordTrace tailWord_1608169 prefixEnd_1608169 825763670660423765091671 := by
  unfold tailWord_1608169
  simp only [CollatzResearch.WordTrace]
  refine ⟨58654742110885841244035561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39103161407257227496023707 58654742110885841244035561)
  ·
    refine ⟨43991056583164380933026671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58654742110885841244035561 43991056583164380933026671)
    ·
      refine ⟨65986584874746571399540007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43991056583164380933026671 65986584874746571399540007)
      ·
        refine ⟨98979877312119857099310011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65986584874746571399540007 98979877312119857099310011)
        ·
          refine ⟨148469815968179785648965017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98979877312119857099310011 148469815968179785648965017)
          ·
            refine ⟨111352361976134839236723763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148469815968179785648965017 111352361976134839236723763)
            ·
              refine ⟨167028542964202258855085645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111352361976134839236723763 167028542964202258855085645)
              ·
                refine ⟨62635703611575847070657117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167028542964202258855085645 62635703611575847070657117)
                ·
                  refine ⟨23488388854340942651496419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62635703611575847070657117 23488388854340942651496419)
                  ·
                    refine ⟨35232583281511413977244629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23488388854340942651496419 35232583281511413977244629)
                    ·
                      refine ⟨825763670660423765091671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35232583281511413977244629 825763670660423765091671)
                      ·
                        rfl

theorem cell23_1608169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_1608169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608169 prefixEnd_1608169 := by exact prefixLift 1608169
  have htrace : WordTrace (prefixWord ++ tailWord_1608169) baseStart_1608169 baseEnd_1608169 := by
    simpa [prefixWord, tailWord_1608169, baseEnd_1608169] using wordTrace_append hprefix tailTrace_1608169
  have hstable : (prefixWord ++ tailWord_1608169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608169).length < 2 ^ (prefixWord ++ tailWord_1608169).sum := by decide
  have hdescent : baseEnd_1608169 < baseStart_1608169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608176 : List Nat := [2, 1, 1, 1, 3, 3, 2, 3, 2, 5]
def baseStart_1608176 : Nat := 118140960795 + 1608176 * 2 ^ 59
def prefixEnd_1608176 : Nat := 4983230072969 + 3 ^ 40 * 1608176 * 2
def baseEnd_1608176 : Nat := 275255755008335079234713

theorem tailTrace_1608176 : CollatzResearch.WordTrace tailWord_1608176 prefixEnd_1608176 275255755008335079234713 := by
  unfold tailWord_1608176
  simp only [CollatzResearch.WordTrace]
  refine ⟨29327498710930240719770191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39103331614573654293026921 29327498710930240719770191)
  ·
    refine ⟨43991248066395361079655287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29327498710930240719770191 43991248066395361079655287)
    ·
      refine ⟨65986872099593041619482931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43991248066395361079655287 65986872099593041619482931)
      ·
        refine ⟨98980308149389562429224397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65986872099593041619482931 98980308149389562429224397)
        ·
          refine ⟨37117615556021085910959149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98980308149389562429224397 37117615556021085910959149)
          ·
            refine ⟨13919105833507907216609681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37117615556021085910959149 13919105833507907216609681)
            ·
              refine ⟨10439329375130930412457261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13919105833507907216609681 10439329375130930412457261)
              ·
                refine ⟨3914748515674098904671473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10439329375130930412457261 3914748515674098904671473)
                ·
                  refine ⟨2936061386755574178503605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3914748515674098904671473 2936061386755574178503605)
                  ·
                    refine ⟨275255755008335079234713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2936061386755574178503605 275255755008335079234713)
                    ·
                      rfl

theorem cell23_1608176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 2, 5].length) (baseStart_1608176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608176 prefixEnd_1608176 := by exact prefixLift 1608176
  have htrace : WordTrace (prefixWord ++ tailWord_1608176) baseStart_1608176 baseEnd_1608176 := by
    simpa [prefixWord, tailWord_1608176, baseEnd_1608176] using wordTrace_append hprefix tailTrace_1608176
  have hstable : (prefixWord ++ tailWord_1608176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608176).length < 2 ^ (prefixWord ++ tailWord_1608176).sum := by decide
  have hdescent : baseEnd_1608176 < baseStart_1608176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608193 : List Nat := [1, 2, 4, 1, 3, 2, 1, 2, 2, 5]
def baseStart_1608193 : Nat := 118140960795 + 1608193 * 2 ^ 59
def prefixEnd_1608193 : Nat := 4983230072969 + 3 ^ 40 * 1608193 * 2
def baseEnd_1608193 : Nat := 275258664732043890397187

theorem tailTrace_1608193 : CollatzResearch.WordTrace tailWord_1608193 prefixEnd_1608193 275258664732043890397187 := by
  unfold tailWord_1608193
  simp only [CollatzResearch.WordTrace]
  refine ⟨58655617462798893342909233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39103744975199262228606155 58655617462798893342909233)
  ·
    refine ⟨43991713097099170007181925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58655617462798893342909233 43991713097099170007181925)
    ·
      refine ⟨8248446205706094376346611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43991713097099170007181925 8248446205706094376346611)
      ·
        refine ⟨12372669308559141564519917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8248446205706094376346611 12372669308559141564519917)
        ·
          refine ⟨4639750990709678086694969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12372669308559141564519917 4639750990709678086694969)
          ·
            refine ⟨3479813243032258565021227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4639750990709678086694969 3479813243032258565021227)
            ·
              refine ⟨5219719864548387847531841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3479813243032258565021227 5219719864548387847531841)
              ·
                refine ⟨3914789898411290885648881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5219719864548387847531841 3914789898411290885648881)
                ·
                  refine ⟨2936092423808468164236661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3914789898411290885648881 2936092423808468164236661)
                  ·
                    refine ⟨275258664732043890397187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2936092423808468164236661 275258664732043890397187)
                    ·
                      rfl

theorem cell23_1608193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_1608193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608193 prefixEnd_1608193 := by exact prefixLift 1608193
  have htrace : WordTrace (prefixWord ++ tailWord_1608193) baseStart_1608193 baseEnd_1608193 := by
    simpa [prefixWord, tailWord_1608193, baseEnd_1608193] using wordTrace_append hprefix tailTrace_1608193
  have hstable : (prefixWord ++ tailWord_1608193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608193).length < 2 ^ (prefixWord ++ tailWord_1608193).sum := by decide
  have hdescent : baseEnd_1608193 < baseStart_1608193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608213 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 1, 6, 2]
def baseStart_1608213 : Nat := 118140960795 + 1608213 * 2 ^ 59
def prefixEnd_1608213 : Nat := 4983230072969 + 3 ^ 40 * 1608213 * 2
def baseEnd_1608213 : Nat := 825786263809221592941469

theorem tailTrace_1608213 : CollatzResearch.WordTrace tailWord_1608213 prefixEnd_1608213 825786263809221592941469 := by
  unfold tailWord_1608213
  simp only [CollatzResearch.WordTrace]
  refine ⟨58656346922726436758637293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39104231281817624505758195 58656346922726436758637293)
  ·
    refine ⟨21996130096022413784488985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58656346922726436758637293 21996130096022413784488985)
    ·
      refine ⟨16497097572016810338366739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21996130096022413784488985 16497097572016810338366739)
      ·
        refine ⟨24745646358025215507550109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16497097572016810338366739 24745646358025215507550109)
        ·
          refine ⟨9279617384259455815331291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24745646358025215507550109 9279617384259455815331291)
          ·
            refine ⟨13919426076389183722996937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9279617384259455815331291 13919426076389183722996937)
            ·
              refine ⟨10439569557291887792247703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13919426076389183722996937 10439569557291887792247703)
              ·
                refine ⟨15659354335937831688371555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10439569557291887792247703 15659354335937831688371555)
                ·
                  refine ⟨23489031503906747532557333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15659354335937831688371555 23489031503906747532557333)
                  ·
                    refine ⟨1101048351745628790588625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23489031503906747532557333 1101048351745628790588625)
                    ·
                      refine ⟨825786263809221592941469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1101048351745628790588625 825786263809221592941469)
                      ·
                        rfl

theorem cell23_1608213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_1608213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608213 prefixEnd_1608213 := by exact prefixLift 1608213
  have htrace : WordTrace (prefixWord ++ tailWord_1608213) baseStart_1608213 baseEnd_1608213 := by
    simpa [prefixWord, tailWord_1608213, baseEnd_1608213] using wordTrace_append hprefix tailTrace_1608213
  have hstable : (prefixWord ++ tailWord_1608213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608213).length < 2 ^ (prefixWord ++ tailWord_1608213).sum := by decide
  have hdescent : baseEnd_1608213 < baseStart_1608213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608226 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_1608226 : Nat := 118140960795 + 1608226 * 2 ^ 59
def prefixEnd_1608226 : Nat := 4983230072969 + 3 ^ 40 * 1608226 * 2
def baseEnd_1608226 : Nat := 825792939057730042078909

theorem tailTrace_1608226 : CollatzResearch.WordTrace tailWord_1608226 prefixEnd_1608226 825792939057730042078909 := by
  unfold tailWord_1608226
  simp only [CollatzResearch.WordTrace]
  refine ⟨14664205267919834994715133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39104547381119559985907021 14664205267919834994715133)
  ·
    refine ⟨5499076975469938123018175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14664205267919834994715133 5499076975469938123018175)
    ·
      refine ⟨8248615463204907184527263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5499076975469938123018175 8248615463204907184527263)
      ·
        refine ⟨12372923194807360776790895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8248615463204907184527263 12372923194807360776790895)
        ·
          refine ⟨18559384792211041165186343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12372923194807360776790895 18559384792211041165186343)
          ·
            refine ⟨27839077188316561747779515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18559384792211041165186343 27839077188316561747779515)
            ·
              refine ⟨41758615782474842621669273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27839077188316561747779515 41758615782474842621669273)
              ·
                refine ⟨31318961836856131966251955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41758615782474842621669273 31318961836856131966251955)
                ·
                  refine ⟨46978442755284197949377933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31318961836856131966251955 46978442755284197949377933)
                  ·
                    refine ⟨17616916033231574231016725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46978442755284197949377933 17616916033231574231016725)
                    ·
                      refine ⟨825792939057730042078909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17616916033231574231016725 825792939057730042078909)
                      ·
                        rfl

theorem cell23_1608226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_1608226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608226 prefixEnd_1608226 := by exact prefixLift 1608226
  have htrace : WordTrace (prefixWord ++ tailWord_1608226) baseStart_1608226 baseEnd_1608226 := by
    simpa [prefixWord, tailWord_1608226, baseEnd_1608226] using wordTrace_append hprefix tailTrace_1608226
  have hstable : (prefixWord ++ tailWord_1608226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608226).length < 2 ^ (prefixWord ++ tailWord_1608226).sum := by decide
  have hdescent : baseEnd_1608226 < baseStart_1608226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608253 : List Nat := [1, 4, 1, 3, 2, 1, 1, 4, 6]
def baseStart_1608253 : Nat := 118140960795 + 1608253 * 2 ^ 59
def prefixEnd_1608253 : Nat := 4983230072969 + 3 ^ 40 * 1608253 * 2
def baseEnd_1608253 : Nat := 91756311448377937382365

theorem tailTrace_1608253 : CollatzResearch.WordTrace tailWord_1608253 prefixEnd_1608253 91756311448377937382365 := by
  unfold tailWord_1608253
  simp only [CollatzResearch.WordTrace]
  refine ⟨58657805842581523590093413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39105203895054349060062275 58657805842581523590093413)
  ·
    refine ⟨10998338595484035673142515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58657805842581523590093413 10998338595484035673142515)
    ·
      refine ⟨16497507893226053509713773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10998338595484035673142515 16497507893226053509713773)
      ·
        refine ⟨6186565459959770066142665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16497507893226053509713773 6186565459959770066142665)
        ·
          refine ⟨4639924094969827549606999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6186565459959770066142665 4639924094969827549606999)
          ·
            refine ⟨6959886142454741324410499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4639924094969827549606999 6959886142454741324410499)
            ·
              refine ⟨10439829213682111986615749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6959886142454741324410499 10439829213682111986615749)
              ·
                refine ⟨1957467977565395997490453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10439829213682111986615749 1957467977565395997490453)
                ·
                  refine ⟨91756311448377937382365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1957467977565395997490453 91756311448377937382365)
                  ·
                    rfl

theorem cell23_1608253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_1608253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608253 prefixEnd_1608253 := by exact prefixLift 1608253
  have htrace : WordTrace (prefixWord ++ tailWord_1608253) baseStart_1608253 baseEnd_1608253 := by
    simpa [prefixWord, tailWord_1608253, baseEnd_1608253] using wordTrace_append hprefix tailTrace_1608253
  have hstable : (prefixWord ++ tailWord_1608253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608253).length < 2 ^ (prefixWord ++ tailWord_1608253).sum := by decide
  have hdescent : baseEnd_1608253 < baseStart_1608253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608257 : List Nat := [1, 2, 5, 1, 1, 3, 1, 4, 1, 4]
def baseStart_1608257 : Nat := 118140960795 + 1608257 * 2 ^ 59
def prefixEnd_1608257 : Nat := 4983230072969 + 3 ^ 40 * 1608257 * 2
def baseEnd_1608257 : Nat := 275269618986006473597089

theorem tailTrace_1608257 : CollatzResearch.WordTrace tailWord_1608257 prefixEnd_1608257 275269618986006473597089 := by
  unfold tailWord_1608257
  simp only [CollatzResearch.WordTrace]
  refine ⟨58657951734567032273239025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39105301156378021515492683 58657951734567032273239025)
  ·
    refine ⟨43993463800925274204929269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58657951734567032273239025 43993463800925274204929269)
    ·
      refine ⟨4124387231336744456712119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43993463800925274204929269 4124387231336744456712119)
      ·
        refine ⟨6186580847005116685068179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4124387231336744456712119 6186580847005116685068179)
        ·
          refine ⟨9279871270507675027602269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6186580847005116685068179 9279871270507675027602269)
          ·
            refine ⟨3479951726440378135350851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9279871270507675027602269 3479951726440378135350851)
            ·
              refine ⟨5219927589660567203026277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3479951726440378135350851 5219927589660567203026277)
              ·
                refine ⟨978736423061356350567427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5219927589660567203026277 978736423061356350567427)
                ·
                  refine ⟨1468104634592034525851141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 978736423061356350567427 1468104634592034525851141)
                  ·
                    refine ⟨275269618986006473597089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1468104634592034525851141 275269618986006473597089)
                    ·
                      rfl

theorem cell23_1608257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_1608257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608257 prefixEnd_1608257 := by exact prefixLift 1608257
  have htrace : WordTrace (prefixWord ++ tailWord_1608257) baseStart_1608257 baseEnd_1608257 := by
    simpa [prefixWord, tailWord_1608257, baseEnd_1608257] using wordTrace_append hprefix tailTrace_1608257
  have hstable : (prefixWord ++ tailWord_1608257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608257).length < 2 ^ (prefixWord ++ tailWord_1608257).sum := by decide
  have hdescent : baseEnd_1608257 < baseStart_1608257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608284 : List Nat := [2, 2, 4, 1, 4, 1, 1, 1, 2, 2, 3]
def baseStart_1608284 : Nat := 118140960795 + 1608284 * 2 ^ 59
def prefixEnd_1608284 : Nat := 4983230072969 + 3 ^ 40 * 1608284 * 2
def baseEnd_1608284 : Nat := 825822720935690815153643

theorem tailTrace_1608284 : CollatzResearch.WordTrace tailWord_1608284 prefixEnd_1608284 825822720935690815153643 := by
  unfold tailWord_1608284
  simp only [CollatzResearch.WordTrace]
  refine ⟨29329468252734607942235953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39105957670312810589647937 29329468252734607942235953)
  ·
    refine ⟨21997101189550955956676965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29329468252734607942235953 21997101189550955956676965)
    ·
      refine ⟨4124456473040804241876931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21997101189550955956676965 4124456473040804241876931)
      ·
        refine ⟨6186684709561206362815397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4124456473040804241876931 6186684709561206362815397)
        ·
          refine ⟨1160003383042726193027887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6186684709561206362815397 1160003383042726193027887)
          ·
            refine ⟨1740005074564089289541831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160003383042726193027887 1740005074564089289541831)
            ·
              refine ⟨2610007611846133934312747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1740005074564089289541831 2610007611846133934312747)
              ·
                refine ⟨3915011417769200901469121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2610007611846133934312747 3915011417769200901469121)
                ·
                  refine ⟨2936258563326900676101841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3915011417769200901469121 2936258563326900676101841)
                  ·
                    refine ⟨2202193922495175507076381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2936258563326900676101841 2202193922495175507076381)
                    ·
                      refine ⟨825822720935690815153643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2202193922495175507076381 825822720935690815153643)
                      ·
                        rfl

theorem cell23_1608284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_1608284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608284 prefixEnd_1608284 := by exact prefixLift 1608284
  have htrace : WordTrace (prefixWord ++ tailWord_1608284) baseStart_1608284 baseEnd_1608284 := by
    simpa [prefixWord, tailWord_1608284, baseEnd_1608284] using wordTrace_append hprefix tailTrace_1608284
  have hstable : (prefixWord ++ tailWord_1608284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608284).length < 2 ^ (prefixWord ++ tailWord_1608284).sum := by decide
  have hdescent : baseEnd_1608284 < baseStart_1608284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608300 : List Nat := [2, 2, 1, 1, 3, 1, 6, 1, 1, 5]
def baseStart_1608300 : Nat := 118140960795 + 1608300 * 2 ^ 59
def prefixEnd_1608300 : Nat := 4983230072969 + 3 ^ 40 * 1608300 * 2
def baseEnd_1608300 : Nat := 275276978875387584184523

theorem tailTrace_1608300 : CollatzResearch.WordTrace tailWord_1608300 prefixEnd_1608300 275276978875387584184523 := by
  unfold tailWord_1608300
  simp only [CollatzResearch.WordTrace]
  refine ⟨29329760036705625308527177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39106346715607500411369569 29329760036705625308527177)
  ·
    refine ⟨21997320027529218981395383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29329760036705625308527177 21997320027529218981395383)
    ·
      refine ⟨32995980041293828472093075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21997320027529218981395383 32995980041293828472093075)
      ·
        refine ⟨49493970061940742708139613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32995980041293828472093075 49493970061940742708139613)
        ·
          refine ⟨18560238773227778515552355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49493970061940742708139613 18560238773227778515552355)
          ·
            refine ⟨27840358159841667773328533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18560238773227778515552355 27840358159841667773328533)
            ·
              refine ⟨1305016788742578176874775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27840358159841667773328533 1305016788742578176874775)
              ·
                refine ⟨1957525183113867265312163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1305016788742578176874775 1957525183113867265312163)
                ·
                  refine ⟨2936287774670800897968245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1957525183113867265312163 2936287774670800897968245)
                  ·
                    refine ⟨275276978875387584184523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2936287774670800897968245 275276978875387584184523)
                    ·
                      rfl

theorem cell23_1608300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 5].length) (baseStart_1608300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608300 prefixEnd_1608300 := by exact prefixLift 1608300
  have htrace : WordTrace (prefixWord ++ tailWord_1608300) baseStart_1608300 baseEnd_1608300 := by
    simpa [prefixWord, tailWord_1608300, baseEnd_1608300] using wordTrace_append hprefix tailTrace_1608300
  have hstable : (prefixWord ++ tailWord_1608300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608300).length < 2 ^ (prefixWord ++ tailWord_1608300).sum := by decide
  have hdescent : baseEnd_1608300 < baseStart_1608300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608323 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 3]
def baseStart_1608323 : Nat := 118140960795 + 1608323 * 2 ^ 59
def prefixEnd_1608323 : Nat := 4983230072969 + 3 ^ 40 * 1608323 * 2
def baseEnd_1608323 : Nat := 825842746681216162565963

theorem tailTrace_1608323 : CollatzResearch.WordTrace tailWord_1608323 prefixEnd_1608323 825842746681216162565963 := by
  unfold tailWord_1608323
  simp only [CollatzResearch.WordTrace]
  refine ⟨58660358952327925545141623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39106905968218617030094415 58660358952327925545141623)
  ·
    refine ⟨87990538428491888317712435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58660358952327925545141623 87990538428491888317712435)
    ·
      refine ⟨131985807642737832476568653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87990538428491888317712435 131985807642737832476568653)
      ·
        refine ⟨49494677866026687178713245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131985807642737832476568653 49494677866026687178713245)
        ·
          refine ⟨18560504199760007692017467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49494677866026687178713245 18560504199760007692017467)
          ·
            refine ⟨27840756299640011538026201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18560504199760007692017467 27840756299640011538026201)
            ·
              refine ⟨20880567224730008653519651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27840756299640011538026201 20880567224730008653519651)
              ·
                refine ⟨31320850837095012980279477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20880567224730008653519651 31320850837095012980279477)
                ·
                  refine ⟨2936329765977657466901201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31320850837095012980279477 2936329765977657466901201)
                  ·
                    refine ⟨2202247324483243100175901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2936329765977657466901201 2202247324483243100175901)
                    ·
                      refine ⟨825842746681216162565963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2202247324483243100175901 825842746681216162565963)
                      ·
                        rfl

theorem cell23_1608323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 3].length) (baseStart_1608323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608323 prefixEnd_1608323 := by exact prefixLift 1608323
  have htrace : WordTrace (prefixWord ++ tailWord_1608323) baseStart_1608323 baseEnd_1608323 := by
    simpa [prefixWord, tailWord_1608323, baseEnd_1608323] using wordTrace_append hprefix tailTrace_1608323
  have hstable : (prefixWord ++ tailWord_1608323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608323).length < 2 ^ (prefixWord ++ tailWord_1608323).sum := by decide
  have hdescent : baseEnd_1608323 < baseStart_1608323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608350 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_1608350 : Nat := 118140960795 + 1608350 * 2 ^ 59
def prefixEnd_1608350 : Nat := 4983230072969 + 3 ^ 40 * 1608350 * 2
def baseEnd_1608350 : Nat := 825856610658887556928339

theorem tailTrace_1608350 : CollatzResearch.WordTrace tailWord_1608350 prefixEnd_1608350 825856610658887556928339 := by
  unfold tailWord_1608350
  simp only [CollatzResearch.WordTrace]
  refine ⟨7332667965403763644546813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39107562482153406104249669 7332667965403763644546813)
  ·
    refine ⟨2749750487026411366705055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7332667965403763644546813 2749750487026411366705055)
    ·
      refine ⟨4124625730539617050057583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2749750487026411366705055 4124625730539617050057583)
      ·
        refine ⟨6186938595809425575086375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4124625730539617050057583 6186938595809425575086375)
        ·
          refine ⟨9280407893714138362629563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6186938595809425575086375 9280407893714138362629563)
          ·
            refine ⟨13920611840571207543944345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9280407893714138362629563 13920611840571207543944345)
            ·
              refine ⟨10440458880428405657958259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13920611840571207543944345 10440458880428405657958259)
              ·
                refine ⟨15660688320642608486937389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10440458880428405657958259 15660688320642608486937389)
                ·
                  refine ⟨5872758120240978182601521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15660688320642608486937389 5872758120240978182601521)
                  ·
                    refine ⟨4404568590180733636951141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5872758120240978182601521 4404568590180733636951141)
                    ·
                      refine ⟨825856610658887556928339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4404568590180733636951141 825856610658887556928339)
                      ·
                        rfl

theorem cell23_1608350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_1608350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608350 prefixEnd_1608350 := by exact prefixLift 1608350
  have htrace : WordTrace (prefixWord ++ tailWord_1608350) baseStart_1608350 baseEnd_1608350 := by
    simpa [prefixWord, tailWord_1608350, baseEnd_1608350] using wordTrace_append hprefix tailTrace_1608350
  have hstable : (prefixWord ++ tailWord_1608350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608350).length < 2 ^ (prefixWord ++ tailWord_1608350).sum := by decide
  have hdescent : baseEnd_1608350 < baseStart_1608350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608371 : List Nat := [1, 1, 1, 2, 3, 5, 3, 2, 1, 2, 2]
def baseStart_1608371 : Nat := 118140960795 + 1608371 * 2 ^ 59
def prefixEnd_1608371 : Nat := 4983230072969 + 3 ^ 40 * 1608371 * 2
def baseEnd_1608371 : Nat := 825867393752631974765743

theorem tailTrace_1608371 : CollatzResearch.WordTrace tailWord_1608371 prefixEnd_1608371 825867393752631974765743 := by
  unfold tailWord_1608371
  simp only [CollatzResearch.WordTrace]
  refine ⟨58662109656154029742888967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39108073104102686495259311 58662109656154029742888967)
  ·
    refine ⟨87993164484231044614333451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58662109656154029742888967 87993164484231044614333451)
    ·
      refine ⟨131989746726346566921500177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87993164484231044614333451 131989746726346566921500177)
      ·
        refine ⟨98992310044759925191125133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131989746726346566921500177 98992310044759925191125133)
        ·
          refine ⟨37122116266784971946671925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98992310044759925191125133 37122116266784971946671925)
          ·
            refine ⟨3480198400011091120000493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37122116266784971946671925 3480198400011091120000493)
            ·
              refine ⟨1305074400004159170000185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3480198400011091120000493 1305074400004159170000185)
              ·
                refine ⟨978805800003119377500139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1305074400004159170000185 978805800003119377500139)
                ·
                  refine ⟨1468208700004679066250209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 978805800003119377500139 1468208700004679066250209)
                  ·
                    refine ⟨1101156525003509299687657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1468208700004679066250209 1101156525003509299687657)
                    ·
                      refine ⟨825867393752631974765743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1101156525003509299687657 825867393752631974765743)
                      ·
                        rfl

theorem cell23_1608371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 1, 2, 2].length) (baseStart_1608371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608371 prefixEnd_1608371 := by exact prefixLift 1608371
  have htrace : WordTrace (prefixWord ++ tailWord_1608371) baseStart_1608371 baseEnd_1608371 := by
    simpa [prefixWord, tailWord_1608371, baseEnd_1608371] using wordTrace_append hprefix tailTrace_1608371
  have hstable : (prefixWord ++ tailWord_1608371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608371).length < 2 ^ (prefixWord ++ tailWord_1608371).sum := by decide
  have hdescent : baseEnd_1608371 < baseStart_1608371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608430 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 2, 4, 3]
def baseStart_1608430 : Nat := 118140960795 + 1608430 * 2 ^ 59
def prefixEnd_1608430 : Nat := 4983230072969 + 3 ^ 40 * 1608430 * 2
def baseEnd_1608430 : Nat := 825897689111247243927971

theorem tailTrace_1608430 : CollatzResearch.WordTrace tailWord_1608430 prefixEnd_1608430 825897689111247243927971 := by
  unfold tailWord_1608430
  simp only [CollatzResearch.WordTrace]
  refine ⟨7333032695367535352410843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39109507708626855212857829 7333032695367535352410843)
  ·
    refine ⟨10999549043051303028616265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7333032695367535352410843 10999549043051303028616265)
    ·
      refine ⟨8249661782288477271462199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10999549043051303028616265 8249661782288477271462199)
      ·
        refine ⟨12374492673432715907193299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8249661782288477271462199 12374492673432715907193299)
        ·
          refine ⟨18561739010149073860789949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12374492673432715907193299 18561739010149073860789949)
          ·
            refine ⟨6960652128805902697796231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18561739010149073860789949 6960652128805902697796231)
            ·
              refine ⟨10440978193208854046694347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6960652128805902697796231 10440978193208854046694347)
              ·
                refine ⟨15661467289813281070041521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10440978193208854046694347 15661467289813281070041521)
                ·
                  refine ⟨11746100467359960802531141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15661467289813281070041521 11746100467359960802531141)
                  ·
                    refine ⟨2202393837629992650474589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11746100467359960802531141 2202393837629992650474589)
                    ·
                      refine ⟨825897689111247243927971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2202393837629992650474589 825897689111247243927971)
                      ·
                        rfl

theorem cell23_1608430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_1608430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608430 prefixEnd_1608430 := by exact prefixLift 1608430
  have htrace : WordTrace (prefixWord ++ tailWord_1608430) baseStart_1608430 baseEnd_1608430 := by
    simpa [prefixWord, tailWord_1608430, baseEnd_1608430] using wordTrace_append hprefix tailTrace_1608430
  have hstable : (prefixWord ++ tailWord_1608430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608430).length < 2 ^ (prefixWord ++ tailWord_1608430).sum := by decide
  have hdescent : baseEnd_1608430 < baseStart_1608430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608433 : List Nat := [1, 2, 2, 2, 2, 2, 2, 3, 7]
def baseStart_1608433 : Nat := 118140960795 + 1608433 * 2 ^ 59
def prefixEnd_1608433 : Nat := 4983230072969 + 3 ^ 40 * 1608433 * 2
def baseEnd_1608433 : Nat := 91766581061467859132273

theorem tailTrace_1608433 : CollatzResearch.WordTrace tailWord_1608433 prefixEnd_1608433 91766581061467859132273 := by
  unfold tailWord_1608433
  simp only [CollatzResearch.WordTrace]
  refine ⟨58664370981929414331645953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39109580654619609554430635 58664370981929414331645953)
  ·
    refine ⟨43998278236447060748734465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58664370981929414331645953 43998278236447060748734465)
    ·
      refine ⟨32998708677335295561550849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43998278236447060748734465 32998708677335295561550849)
      ·
        refine ⟨24749031508001471671163137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32998708677335295561550849 24749031508001471671163137)
        ·
          refine ⟨18561773631001103753372353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24749031508001471671163137 18561773631001103753372353)
          ·
            refine ⟨13921330223250827815029265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18561773631001103753372353 13921330223250827815029265)
            ·
              refine ⟨10440997667438120861271949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13921330223250827815029265 10440997667438120861271949)
              ·
                refine ⟨3915374125289295322976981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10440997667438120861271949 3915374125289295322976981)
                ·
                  refine ⟨91766581061467859132273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3915374125289295322976981 91766581061467859132273)
                  ·
                    rfl

theorem cell23_1608433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 7].length) (baseStart_1608433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608433 prefixEnd_1608433 := by exact prefixLift 1608433
  have htrace : WordTrace (prefixWord ++ tailWord_1608433) baseStart_1608433 baseEnd_1608433 := by
    simpa [prefixWord, tailWord_1608433, baseEnd_1608433] using wordTrace_append hprefix tailTrace_1608433
  have hstable : (prefixWord ++ tailWord_1608433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608433).length < 2 ^ (prefixWord ++ tailWord_1608433).sum := by decide
  have hdescent : baseEnd_1608433 < baseStart_1608433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608444 : List Nat := [2, 2, 2, 1, 3, 2, 2, 3, 2, 2, 2]
def baseStart_1608444 : Nat := 118140960795 + 1608444 * 2 ^ 59
def prefixEnd_1608444 : Nat := 4983230072969 + 3 ^ 40 * 1608444 * 2
def baseEnd_1608444 : Nat := 825904877840410189152907

theorem tailTrace_1608444 : CollatzResearch.WordTrace tailWord_1608444 prefixEnd_1608444 825904877840410189152907 := by
  unfold tailWord_1608444
  simp only [CollatzResearch.WordTrace]
  refine ⟨29332386092444781605148193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39109848123259708806864257 29332386092444781605148193)
  ·
    refine ⟨21999289569333586203861145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29332386092444781605148193 21999289569333586203861145)
    ·
      refine ⟨16499467177000189652895859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21999289569333586203861145 16499467177000189652895859)
      ·
        refine ⟨24749200765500284479343789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16499467177000189652895859 24749200765500284479343789)
        ·
          refine ⟨9280950287062606679753921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24749200765500284479343789 9280950287062606679753921)
          ·
            refine ⟨6960712715296955009815441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9280950287062606679753921 6960712715296955009815441)
            ·
              refine ⟨5220534536472716257361581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6960712715296955009815441 5220534536472716257361581)
              ·
                refine ⟨1957700451177268596510593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5220534536472716257361581 1957700451177268596510593)
                ·
                  refine ⟨1468275338382951447382945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1957700451177268596510593 1468275338382951447382945)
                  ·
                    refine ⟨1101206503787213585537209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1468275338382951447382945 1101206503787213585537209)
                    ·
                      refine ⟨825904877840410189152907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1101206503787213585537209 825904877840410189152907)
                      ·
                        rfl

theorem cell23_1608444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_1608444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608444 prefixEnd_1608444 := by exact prefixLift 1608444
  have htrace : WordTrace (prefixWord ++ tailWord_1608444) baseStart_1608444 baseEnd_1608444 := by
    simpa [prefixWord, tailWord_1608444, baseEnd_1608444] using wordTrace_append hprefix tailTrace_1608444
  have hstable : (prefixWord ++ tailWord_1608444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608444).length < 2 ^ (prefixWord ++ tailWord_1608444).sum := by decide
  have hdescent : baseEnd_1608444 < baseStart_1608444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608450 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 9]
def baseStart_1608450 : Nat := 118140960795 + 1608450 * 2 ^ 59
def prefixEnd_1608450 : Nat := 4983230072969 + 3 ^ 40 * 1608450 * 2
def baseEnd_1608450 : Nat := 91767550969370796186431

theorem tailTrace_1608450 : CollatzResearch.WordTrace tailWord_1608450 prefixEnd_1608450 91767550969370796186431 := by
  unfold tailWord_1608450
  simp only [CollatzResearch.WordTrace]
  refine ⟨14666247755716956558753701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39109994015245217490009869 14666247755716956558753701)
  ·
    refine ⟨2749921454196929354766319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14666247755716956558753701 2749921454196929354766319)
    ·
      refine ⟨4124882181295394032149479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2749921454196929354766319 4124882181295394032149479)
      ·
        refine ⟨6187323271943091048224219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4124882181295394032149479 6187323271943091048224219)
        ·
          refine ⟨9280984907914636572336329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6187323271943091048224219 9280984907914636572336329)
          ·
            refine ⟨6960738680935977429252247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9280984907914636572336329 6960738680935977429252247)
            ·
              refine ⟨10441108021403966143878371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6960738680935977429252247 10441108021403966143878371)
              ·
                refine ⟨15661662032105949215817557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10441108021403966143878371 15661662032105949215817557)
                ·
                  refine ⟨91767550969370796186431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15661662032105949215817557 91767550969370796186431)
                  ·
                    rfl

theorem cell23_1608450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_1608450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608450 prefixEnd_1608450 := by exact prefixLift 1608450
  have htrace : WordTrace (prefixWord ++ tailWord_1608450) baseStart_1608450 baseEnd_1608450 := by
    simpa [prefixWord, tailWord_1608450, baseEnd_1608450] using wordTrace_append hprefix tailTrace_1608450
  have hstable : (prefixWord ++ tailWord_1608450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608450).length < 2 ^ (prefixWord ++ tailWord_1608450).sum := by decide
  have hdescent : baseEnd_1608450 < baseStart_1608450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608463 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 1, 7]
def baseStart_1608463 : Nat := 118140960795 + 1608463 * 2 ^ 59
def prefixEnd_1608463 : Nat := 4983230072969 + 3 ^ 40 * 1608463 * 2
def baseEnd_1608463 : Nat := 275304877990948538271773

theorem tailTrace_1608463 : CollatzResearch.WordTrace tailWord_1608463 prefixEnd_1608463 275304877990948538271773 := by
  unfold tailWord_1608463
  simp only [CollatzResearch.WordTrace]
  refine ⟨58665465171820729455238043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39110310114547152970158695 58665465171820729455238043)
  ·
    refine ⟨87998197757731094182857065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58665465171820729455238043 87998197757731094182857065)
    ·
      refine ⟨65998648318298320637142799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87998197757731094182857065 65998648318298320637142799)
      ·
        refine ⟨98997972477447480955714199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65998648318298320637142799 98997972477447480955714199)
        ·
          refine ⟨148496958716171221433571299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98997972477447480955714199 148496958716171221433571299)
          ·
            refine ⟨222745438074256832150356949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148496958716171221433571299 222745438074256832150356949)
            ·
              refine ⟨5220596204865394503523991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 222745438074256832150356949 5220596204865394503523991)
              ·
                refine ⟨7830894307298091755285987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5220596204865394503523991 7830894307298091755285987)
                ·
                  refine ⟨11746341460947137632928981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7830894307298091755285987 11746341460947137632928981)
                  ·
                    refine ⟨275304877990948538271773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11746341460947137632928981 275304877990948538271773)
                    ·
                      rfl

theorem cell23_1608463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 7].length) (baseStart_1608463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608463 prefixEnd_1608463 := by exact prefixLift 1608463
  have htrace : WordTrace (prefixWord ++ tailWord_1608463) baseStart_1608463 baseEnd_1608463 := by
    simpa [prefixWord, tailWord_1608463, baseEnd_1608463] using wordTrace_append hprefix tailTrace_1608463
  have hstable : (prefixWord ++ tailWord_1608463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608463).length < 2 ^ (prefixWord ++ tailWord_1608463).sum := by decide
  have hdescent : baseEnd_1608463 < baseStart_1608463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608473 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 1, 2, 5]
def baseStart_1608473 : Nat := 118140960795 + 1608473 * 2 ^ 59
def prefixEnd_1608473 : Nat := 4983230072969 + 3 ^ 40 * 1608473 * 2
def baseEnd_1608473 : Nat := 825919768779390575690273

theorem tailTrace_1608473 : CollatzResearch.WordTrace tailWord_1608473 prefixEnd_1608473 825919768779390575690273 := by
  unfold tailWord_1608473
  simp only [CollatzResearch.WordTrace]
  refine ⟨58665829901784501163102073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39110553267856334108734715 58665829901784501163102073)
  ·
    refine ⟨43999372426338375872326555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58665829901784501163102073 43999372426338375872326555)
    ·
      refine ⟨65999058639507563808489833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43999372426338375872326555 65999058639507563808489833)
      ·
        refine ⟨49499293979630672856367375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65999058639507563808489833 49499293979630672856367375)
        ·
          refine ⟨74248940969446009284551063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49499293979630672856367375 74248940969446009284551063)
          ·
            refine ⟨111373411454169013926826595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74248940969446009284551063 111373411454169013926826595)
            ·
              refine ⟨167060117181253520890239893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111373411454169013926826595 167060117181253520890239893)
              ·
                refine ⟨7830942992871258791729995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 167060117181253520890239893 7830942992871258791729995)
                ·
                  refine ⟨11746414489306888187594993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7830942992871258791729995 11746414489306888187594993)
                  ·
                    refine ⟨8809810866980166140696245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11746414489306888187594993 8809810866980166140696245)
                    ·
                      refine ⟨825919768779390575690273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8809810866980166140696245 825919768779390575690273)
                      ·
                        rfl

theorem cell23_1608473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_1608473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608473 prefixEnd_1608473 := by exact prefixLift 1608473
  have htrace : WordTrace (prefixWord ++ tailWord_1608473) baseStart_1608473 baseEnd_1608473 := by
    simpa [prefixWord, tailWord_1608473, baseEnd_1608473] using wordTrace_append hprefix tailTrace_1608473
  have hstable : (prefixWord ++ tailWord_1608473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608473).length < 2 ^ (prefixWord ++ tailWord_1608473).sum := by decide
  have hdescent : baseEnd_1608473 < baseStart_1608473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608518 : List Nat := [6, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_1608518 : Nat := 118140960795 + 1608518 * 2 ^ 59
def prefixEnd_1608518 : Nat := 4983230072969 + 3 ^ 40 * 1608518 * 2
def baseEnd_1608518 : Nat := 91771430600982544403063

theorem tailTrace_1608518 : CollatzResearch.WordTrace tailWord_1608518 prefixEnd_1608518 91771430600982544403063 := by
  unfold tailWord_1608518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1833358474581921057765319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39111647457747649232326805 1833358474581921057765319)
  ·
    refine ⟨2750037711872881586647979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1833358474581921057765319 2750037711872881586647979)
    ·
      refine ⟨4125056567809322379971969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2750037711872881586647979 4125056567809322379971969)
      ·
        refine ⟨3093792425856991784978977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4125056567809322379971969 3093792425856991784978977)
        ·
          refine ⟨2320344319392743838734233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3093792425856991784978977 2320344319392743838734233)
          ·
            refine ⟨1740258239544557879050675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2320344319392743838734233 1740258239544557879050675)
            ·
              refine ⟨2610387359316836818576013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1740258239544557879050675 2610387359316836818576013)
              ·
                refine ⟨978895259743813806966005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2610387359316836818576013 978895259743813806966005)
                ·
                  refine ⟨91771430600982544403063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 978895259743813806966005 91771430600982544403063)
                  ·
                    rfl

theorem cell23_1608518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_1608518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608518 prefixEnd_1608518 := by exact prefixLift 1608518
  have htrace : WordTrace (prefixWord ++ tailWord_1608518) baseStart_1608518 baseEnd_1608518 := by
    simpa [prefixWord, tailWord_1608518, baseEnd_1608518] using wordTrace_append hprefix tailTrace_1608518
  have hstable : (prefixWord ++ tailWord_1608518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608518).length < 2 ^ (prefixWord ++ tailWord_1608518).sum := by decide
  have hdescent : baseEnd_1608518 < baseStart_1608518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608520 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 1, 4, 3]
def baseStart_1608520 : Nat := 118140960795 + 1608520 * 2 ^ 59
def prefixEnd_1608520 : Nat := 4983230072969 + 3 ^ 40 * 1608520 * 2
def baseEnd_1608520 : Nat := 825943902370151891802557

theorem tailTrace_1608520 : CollatzResearch.WordTrace tailWord_1608520 prefixEnd_1608520 825943902370151891802557 := by
  unfold tailWord_1608520
  simp only [CollatzResearch.WordTrace]
  refine ⟨29333772066307114095031507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39111696088409485460042009 29333772066307114095031507)
  ·
    refine ⟨44000658099460671142547261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29333772066307114095031507 44000658099460671142547261)
    ·
      refine ⟨16500246787297751678455223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44000658099460671142547261 16500246787297751678455223)
      ·
        refine ⟨24750370180946627517682835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16500246787297751678455223 24750370180946627517682835)
        ·
          refine ⟨37125555271419941276524253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24750370180946627517682835 37125555271419941276524253)
          ·
            refine ⟨13922083226782477978696595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37125555271419941276524253 13922083226782477978696595)
            ·
              refine ⟨20883124840173716968044893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13922083226782477978696595 20883124840173716968044893)
              ·
                refine ⟨7831171815065143863016835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20883124840173716968044893 7831171815065143863016835)
                ·
                  refine ⟨11746757722597715794525253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7831171815065143863016835 11746757722597715794525253)
                  ·
                    refine ⟨2202517072987071711473485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11746757722597715794525253 2202517072987071711473485)
                    ·
                      refine ⟨825943902370151891802557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2202517072987071711473485 825943902370151891802557)
                      ·
                        rfl

theorem cell23_1608520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_1608520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608520 prefixEnd_1608520 := by exact prefixLift 1608520
  have htrace : WordTrace (prefixWord ++ tailWord_1608520) baseStart_1608520 baseEnd_1608520 := by
    simpa [prefixWord, tailWord_1608520, baseEnd_1608520] using wordTrace_append hprefix tailTrace_1608520
  have hstable : (prefixWord ++ tailWord_1608520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608520).length < 2 ^ (prefixWord ++ tailWord_1608520).sum := by decide
  have hdescent : baseEnd_1608520 < baseStart_1608520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608537 : List Nat := [1, 2, 1, 2, 2, 5, 1, 2, 2, 2, 3]
def baseStart_1608537 : Nat := 118140960795 + 1608537 * 2 ^ 59
def prefixEnd_1608537 : Nat := 4983230072969 + 3 ^ 40 * 1608537 * 2
def baseEnd_1608537 : Nat := 825952631541278325289979

theorem tailTrace_1608537 : CollatzResearch.WordTrace tailWord_1608537 prefixEnd_1608537 825952631541278325289979 := by
  unfold tailWord_1608537
  simp only [CollatzResearch.WordTrace]
  refine ⟨58668164173552640093431865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39112109449035093395621243 58668164173552640093431865)
  ·
    refine ⟨44001123130164480070073899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58668164173552640093431865 44001123130164480070073899)
    ·
      refine ⟨66001684695246720105110849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44001123130164480070073899 66001684695246720105110849)
      ·
        refine ⟨49501263521435040078833137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66001684695246720105110849 49501263521435040078833137)
        ·
          refine ⟨37125947641076280059124853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49501263521435040078833137 37125947641076280059124853)
          ·
            refine ⟨3480557591350901255542955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37125947641076280059124853 3480557591350901255542955)
            ·
              refine ⟨5220836387026351883314433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3480557591350901255542955 5220836387026351883314433)
              ·
                refine ⟨3915627290269763912485825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5220836387026351883314433 3915627290269763912485825)
                ·
                  refine ⟨2936720467702322934364369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3915627290269763912485825 2936720467702322934364369)
                  ·
                    refine ⟨2202540350776742200773277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2936720467702322934364369 2202540350776742200773277)
                    ·
                      refine ⟨825952631541278325289979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2202540350776742200773277 825952631541278325289979)
                      ·
                        rfl

theorem cell23_1608537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 2, 3].length) (baseStart_1608537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608537 prefixEnd_1608537 := by exact prefixLift 1608537
  have htrace : WordTrace (prefixWord ++ tailWord_1608537) baseStart_1608537 baseEnd_1608537 := by
    simpa [prefixWord, tailWord_1608537, baseEnd_1608537] using wordTrace_append hprefix tailTrace_1608537
  have hstable : (prefixWord ++ tailWord_1608537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608537).length < 2 ^ (prefixWord ++ tailWord_1608537).sum := by decide
  have hdescent : baseEnd_1608537 < baseStart_1608537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608553 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 1, 11]
def baseStart_1608553 : Nat := 118140960795 + 1608553 * 2 ^ 59
def prefixEnd_1608553 : Nat := 4983230072969 + 3 ^ 40 * 1608553 * 2
def baseEnd_1608553 : Nat := 275320282410583420896635

theorem tailTrace_1608553 : CollatzResearch.WordTrace tailWord_1608553 prefixEnd_1608553 275320282410583420896635 := by
  unfold tailWord_1608553
  simp only [CollatzResearch.WordTrace]
  refine ⟨58668747741494674826014313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39112498494329783217342875 58668747741494674826014313)
  ·
    refine ⟨44001560806121006119510735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58668747741494674826014313 44001560806121006119510735)
    ·
      refine ⟨66002341209181509179266103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44001560806121006119510735 66002341209181509179266103)
      ·
        refine ⟨99003511813772263768899155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66002341209181509179266103 99003511813772263768899155)
        ·
          refine ⟨148505267720658395653348733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99003511813772263768899155 148505267720658395653348733)
          ·
            refine ⟨55689475395246898370005775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148505267720658395653348733 55689475395246898370005775)
            ·
              refine ⟨83534213092870347555008663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55689475395246898370005775 83534213092870347555008663)
              ·
                refine ⟨125301319639305521332512995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83534213092870347555008663 125301319639305521332512995)
                ·
                  refine ⟨187951979458958281998769493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125301319639305521332512995 187951979458958281998769493)
                  ·
                    refine ⟨275320282410583420896635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 187951979458958281998769493 275320282410583420896635)
                    ·
                      rfl

theorem cell23_1608553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 11].length) (baseStart_1608553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608553 prefixEnd_1608553 := by exact prefixLift 1608553
  have htrace : WordTrace (prefixWord ++ tailWord_1608553) baseStart_1608553 baseEnd_1608553 := by
    simpa [prefixWord, tailWord_1608553, baseEnd_1608553] using wordTrace_append hprefix tailTrace_1608553
  have hstable : (prefixWord ++ tailWord_1608553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608553).length < 2 ^ (prefixWord ++ tailWord_1608553).sum := by decide
  have hdescent : baseEnd_1608553 < baseStart_1608553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608567 : List Nat := [1, 1, 3, 1, 1, 2, 1, 6, 3, 1, 3]
def baseStart_1608567 : Nat := 118140960795 + 1608567 * 2 ^ 59
def prefixEnd_1608567 : Nat := 4983230072969 + 3 ^ 40 * 1608567 * 2
def baseEnd_1608567 : Nat := 825968035960913207914841

theorem tailTrace_1608567 : CollatzResearch.WordTrace tailWord_1608567 prefixEnd_1608567 825968035960913207914841 := by
  unfold tailWord_1608567
  simp only [CollatzResearch.WordTrace]
  refine ⟨58669258363443955217023955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39112838908962636811349303 58669258363443955217023955)
  ·
    refine ⟨88003887545165932825535933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58669258363443955217023955 88003887545165932825535933)
    ·
      refine ⟨33001457829437224809575975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88003887545165932825535933 33001457829437224809575975)
      ·
        refine ⟨49502186744155837214363963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33001457829437224809575975 49502186744155837214363963)
        ·
          refine ⟨74253280116233755821545945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49502186744155837214363963 74253280116233755821545945)
          ·
            refine ⟨55689960087175316866159459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74253280116233755821545945 55689960087175316866159459)
            ·
              refine ⟨83534940130762975299239189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55689960087175316866159459 83534940130762975299239189)
              ·
                refine ⟨3915700318629514467151837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83534940130762975299239189 3915700318629514467151837)
                ·
                  refine ⟨1468387619486067925181939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3915700318629514467151837 1468387619486067925181939)
                  ·
                    refine ⟨2202581429229101887772909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1468387619486067925181939 2202581429229101887772909)
                    ·
                      refine ⟨825968035960913207914841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2202581429229101887772909 825968035960913207914841)
                      ·
                        rfl

theorem cell23_1608567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 1, 3].length) (baseStart_1608567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608567 prefixEnd_1608567 := by exact prefixLift 1608567
  have htrace : WordTrace (prefixWord ++ tailWord_1608567) baseStart_1608567 baseEnd_1608567 := by
    simpa [prefixWord, tailWord_1608567, baseEnd_1608567] using wordTrace_append hprefix tailTrace_1608567
  have hstable : (prefixWord ++ tailWord_1608567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608567).length < 2 ^ (prefixWord ++ tailWord_1608567).sum := by decide
  have hdescent : baseEnd_1608567 < baseStart_1608567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608607 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 4]
def baseStart_1608607 : Nat := 118140960795 + 1608607 * 2 ^ 59
def prefixEnd_1608607 : Nat := 4983230072969 + 3 ^ 40 * 1608607 * 2
def baseEnd_1608607 : Nat := 825988575187093051414657

theorem tailTrace_1608607 : CollatzResearch.WordTrace tailWord_1608607 prefixEnd_1608607 825988575187093051414657 := by
  unfold tailWord_1608607
  simp only [CollatzResearch.WordTrace]
  refine ⟨58670717283299042048480075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39113811522199361365653383 58670717283299042048480075)
  ·
    refine ⟨88006075924948563072720113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58670717283299042048480075 88006075924948563072720113)
    ·
      refine ⟨66004556943711422304540085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88006075924948563072720113 66004556943711422304540085)
      ·
        refine ⟨6187927213472945841050633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66004556943711422304540085 6187927213472945841050633)
        ·
          refine ⟨4640945410104709380787975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6187927213472945841050633 4640945410104709380787975)
          ·
            refine ⟨6961418115157064071181963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4640945410104709380787975 6961418115157064071181963)
            ·
              refine ⟨10442127172735596106772945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6961418115157064071181963 10442127172735596106772945)
              ·
                refine ⟨7831595379551697080079709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10442127172735596106772945 7831595379551697080079709)
                ·
                  refine ⟨2936848267331886405029891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7831595379551697080079709 2936848267331886405029891)
                  ·
                    refine ⟨4405272400997829607544837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2936848267331886405029891 4405272400997829607544837)
                    ·
                      refine ⟨825988575187093051414657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4405272400997829607544837 825988575187093051414657)
                      ·
                        rfl

theorem cell23_1608607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_1608607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608607 prefixEnd_1608607 := by exact prefixLift 1608607
  have htrace : WordTrace (prefixWord ++ tailWord_1608607) baseStart_1608607 baseEnd_1608607 := by
    simpa [prefixWord, tailWord_1608607, baseEnd_1608607] using wordTrace_append hprefix tailTrace_1608607
  have hstable : (prefixWord ++ tailWord_1608607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608607).length < 2 ^ (prefixWord ++ tailWord_1608607).sum := by decide
  have hdescent : baseEnd_1608607 < baseStart_1608607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608617 : List Nat := [1, 2, 1, 1, 1, 1, 5, 5, 2, 4]
def baseStart_1608617 : Nat := 118140960795 + 1608617 * 2 ^ 59
def prefixEnd_1608617 : Nat := 4983230072969 + 3 ^ 40 * 1608617 * 2
def baseEnd_1608617 : Nat := 275331236664546004096537

theorem tailTrace_1608617 : CollatzResearch.WordTrace tailWord_1608617 prefixEnd_1608617 275331236664546004096537 := by
  unfold tailWord_1608617
  simp only [CollatzResearch.WordTrace]
  refine ⟨58671082013262813756344105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39114054675508542504229403 58671082013262813756344105)
  ·
    refine ⟨44003311509947110317258079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58671082013262813756344105 44003311509947110317258079)
    ·
      refine ⟨66004967264920665475887119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44003311509947110317258079 66004967264920665475887119)
      ·
        refine ⟨99007450897380998213830679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66004967264920665475887119 99007450897380998213830679)
        ·
          refine ⟨148511176346071497320746019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99007450897380998213830679 148511176346071497320746019)
          ·
            refine ⟨222766764519107245981119029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148511176346071497320746019 222766764519107245981119029)
            ·
              refine ⟨20884384173666304310729909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 222766764519107245981119029 20884384173666304310729909)
              ·
                refine ⟨1957911016281216029130929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20884384173666304310729909 1957911016281216029130929)
                ·
                  refine ⟨1468433262210912021848197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1957911016281216029130929 1468433262210912021848197)
                  ·
                    refine ⟨275331236664546004096537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1468433262210912021848197 275331236664546004096537)
                    ·
                      rfl

theorem cell23_1608617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 4].length) (baseStart_1608617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608617 prefixEnd_1608617 := by exact prefixLift 1608617
  have htrace : WordTrace (prefixWord ++ tailWord_1608617) baseStart_1608617 baseEnd_1608617 := by
    simpa [prefixWord, tailWord_1608617, baseEnd_1608617] using wordTrace_append hprefix tailTrace_1608617
  have hstable : (prefixWord ++ tailWord_1608617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608617).length < 2 ^ (prefixWord ++ tailWord_1608617).sum := by decide
  have hdescent : baseEnd_1608617 < baseStart_1608617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608620 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 4]
def baseStart_1608620 : Nat := 118140960795 + 1608620 * 2 ^ 59
def prefixEnd_1608620 : Nat := 4983230072969 + 3 ^ 40 * 1608620 * 2
def baseEnd_1608620 : Nat := 825995250435601500552097

theorem tailTrace_1608620 : CollatzResearch.WordTrace tailWord_1608620 prefixEnd_1608620 825995250435601500552097 := by
  unfold tailWord_1608620
  simp only [CollatzResearch.WordTrace]
  refine ⟨29335595716125972634351657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39114127621501296845802209 29335595716125972634351657)
  ·
    refine ⟨22001696787094479475763743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29335595716125972634351657 22001696787094479475763743)
    ·
      refine ⟨33002545180641719213645615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22001696787094479475763743 33002545180641719213645615)
      ·
        refine ⟨49503817770962578820468423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33002545180641719213645615 49503817770962578820468423)
        ·
          refine ⟨74255726656443868230702635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49503817770962578820468423 74255726656443868230702635)
          ·
            refine ⟨111383589984665802346053953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74255726656443868230702635 111383589984665802346053953)
            ·
              refine ⟨83537692488499351759540465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111383589984665802346053953 83537692488499351759540465)
              ·
                refine ⟨62653269366374513819655349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83537692488499351759540465 62653269366374513819655349)
                ·
                  refine ⟨5873744003097610670592689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62653269366374513819655349 5873744003097610670592689)
                  ·
                    refine ⟨4405308002323208002944517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5873744003097610670592689 4405308002323208002944517)
                    ·
                      refine ⟨825995250435601500552097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4405308002323208002944517 825995250435601500552097)
                      ·
                        rfl

theorem cell23_1608620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_1608620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608620 prefixEnd_1608620 := by exact prefixLift 1608620
  have htrace : WordTrace (prefixWord ++ tailWord_1608620) baseStart_1608620 baseEnd_1608620 := by
    simpa [prefixWord, tailWord_1608620, baseEnd_1608620] using wordTrace_append hprefix tailTrace_1608620
  have hstable : (prefixWord ++ tailWord_1608620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608620).length < 2 ^ (prefixWord ++ tailWord_1608620).sum := by decide
  have hdescent : baseEnd_1608620 < baseStart_1608620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608628 : List Nat := [2, 5, 2, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_1608628 : Nat := 118140960795 + 1608628 * 2 ^ 59
def prefixEnd_1608628 : Nat := 4983230072969 + 3 ^ 40 * 1608628 * 2
def baseEnd_1608628 : Nat := 825999358280837469252061

theorem tailTrace_1608628 : CollatzResearch.WordTrace tailWord_1608628 prefixEnd_1608628 825999358280837469252061 := by
  unfold tailWord_1608628
  simp only [CollatzResearch.WordTrace]
  refine ⟨29335741608111481317497269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39114322144148641756663025 29335741608111481317497269)
  ·
    refine ⟨2750225775760451373515369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29335741608111481317497269 2750225775760451373515369)
    ·
      refine ⟨2062669331820338530136527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2750225775760451373515369 2062669331820338530136527)
      ·
        refine ⟨3094003997730507795204791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2062669331820338530136527 3094003997730507795204791)
        ·
          refine ⟨4641005996595761692807187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3094003997730507795204791 4641005996595761692807187)
          ·
            refine ⟨6961508994893642539210781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4641005996595761692807187 6961508994893642539210781)
            ·
              refine ⟨2610565873085115952204043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6961508994893642539210781 2610565873085115952204043)
              ·
                refine ⟨3915848809627673928306065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2610565873085115952204043 3915848809627673928306065)
                ·
                  refine ⟨2936886607220755446229549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3915848809627673928306065 2936886607220755446229549)
                  ·
                    refine ⟨1101332477707783292336081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2936886607220755446229549 1101332477707783292336081)
                    ·
                      refine ⟨825999358280837469252061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1101332477707783292336081 825999358280837469252061)
                      ·
                        rfl

theorem cell23_1608628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_1608628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608628 prefixEnd_1608628 := by exact prefixLift 1608628
  have htrace : WordTrace (prefixWord ++ tailWord_1608628) baseStart_1608628 baseEnd_1608628 := by
    simpa [prefixWord, tailWord_1608628, baseEnd_1608628] using wordTrace_append hprefix tailTrace_1608628
  have hstable : (prefixWord ++ tailWord_1608628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608628).length < 2 ^ (prefixWord ++ tailWord_1608628).sum := by decide
  have hdescent : baseEnd_1608628 < baseStart_1608628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608650 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_1608650 : Nat := 118140960795 + 1608650 * 2 ^ 59
def prefixEnd_1608650 : Nat := 4983230072969 + 3 ^ 40 * 1608650 * 2
def baseEnd_1608650 : Nat := 826010654855236383176959

theorem tailTrace_1608650 : CollatzResearch.WordTrace tailWord_1608650 prefixEnd_1608650 826010654855236383176959 := by
  unfold tailWord_1608650
  simp only [CollatzResearch.WordTrace]
  refine ⟨14668071405535815098073851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39114857081428840261530269 14668071405535815098073851)
  ·
    refine ⟨22002107108303722647110777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14668071405535815098073851 22002107108303722647110777)
    ·
      refine ⟨16501580331227791985333083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22002107108303722647110777 16501580331227791985333083)
      ·
        refine ⟨24752370496841687977999625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16501580331227791985333083 24752370496841687977999625)
        ·
          refine ⟨18564277872631265983499719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24752370496841687977999625 18564277872631265983499719)
          ·
            refine ⟨27846416808946898975249579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18564277872631265983499719 27846416808946898975249579)
            ·
              refine ⟨41769625213420348462874369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27846416808946898975249579 41769625213420348462874369)
              ·
                refine ⟨31327218910065261347155777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41769625213420348462874369 31327218910065261347155777)
                ·
                  refine ⟨23495414182548946010366833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31327218910065261347155777 23495414182548946010366833)
                  ·
                    refine ⟨17621560636911709507775125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23495414182548946010366833 17621560636911709507775125)
                    ·
                      refine ⟨826010654855236383176959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17621560636911709507775125 826010654855236383176959)
                      ·
                        rfl

theorem cell23_1608650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_1608650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608650 prefixEnd_1608650 := by exact prefixLift 1608650
  have htrace : WordTrace (prefixWord ++ tailWord_1608650) baseStart_1608650 baseEnd_1608650 := by
    simpa [prefixWord, tailWord_1608650, baseEnd_1608650] using wordTrace_append hprefix tailTrace_1608650
  have hstable : (prefixWord ++ tailWord_1608650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608650).length < 2 ^ (prefixWord ++ tailWord_1608650).sum := by decide
  have hdescent : baseEnd_1608650 < baseStart_1608650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608658 : List Nat := [3, 2, 2, 3, 1, 2, 2, 1, 3, 2, 2]
def baseStart_1608658 : Nat := 118140960795 + 1608658 * 2 ^ 59
def prefixEnd_1608658 : Nat := 4983230072969 + 3 ^ 40 * 1608658 * 2
def baseEnd_1608658 : Nat := 826014762700472351876923

theorem tailTrace_1608658 : CollatzResearch.WordTrace tailWord_1608658 prefixEnd_1608658 826014762700472351876923 := by
  unfold tailWord_1608658
  simp only [CollatzResearch.WordTrace]
  refine ⟨14668144351528569439646657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39115051604076185172391085 14668144351528569439646657)
  ·
    refine ⟨11001108263646427079734993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14668144351528569439646657 11001108263646427079734993)
    ·
      refine ⟨8250831197734820309801245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11001108263646427079734993 8250831197734820309801245)
      ·
        refine ⟨3094061699150557616175467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8250831197734820309801245 3094061699150557616175467)
        ·
          refine ⟨4641092548725836424263201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3094061699150557616175467 4641092548725836424263201)
          ·
            refine ⟨3480819411544377318197401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4641092548725836424263201 3480819411544377318197401)
            ·
              refine ⟨2610614558658282988648051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3480819411544377318197401 2610614558658282988648051)
              ·
                refine ⟨3915921837987424482972077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2610614558658282988648051 3915921837987424482972077)
                ·
                  refine ⟨1468470689245284181114529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3915921837987424482972077 1468470689245284181114529)
                  ·
                    refine ⟨1101353016933963135835897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1468470689245284181114529 1101353016933963135835897)
                    ·
                      refine ⟨826014762700472351876923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1101353016933963135835897 826014762700472351876923)
                      ·
                        rfl

theorem cell23_1608658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_1608658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608658 prefixEnd_1608658 := by exact prefixLift 1608658
  have htrace : WordTrace (prefixWord ++ tailWord_1608658) baseStart_1608658 baseEnd_1608658 := by
    simpa [prefixWord, tailWord_1608658, baseEnd_1608658] using wordTrace_append hprefix tailTrace_1608658
  have hstable : (prefixWord ++ tailWord_1608658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608658).length < 2 ^ (prefixWord ++ tailWord_1608658).sum := by decide
  have hdescent : baseEnd_1608658 < baseStart_1608658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608671 : List Nat := [1, 1, 2, 3, 6, 1, 1, 1, 1, 2, 4]
def baseStart_1608671 : Nat := 118140960795 + 1608671 * 2 ^ 59
def prefixEnd_1608671 : Nat := 4983230072969 + 3 ^ 40 * 1608671 * 2
def baseEnd_1608671 : Nat := 826021437948980801014363

theorem tailTrace_1608671 : CollatzResearch.WordTrace tailWord_1608671 prefixEnd_1608671 826021437948980801014363 := by
  unfold tailWord_1608671
  simp only [CollatzResearch.WordTrace]
  refine ⟨58673051555067180978809867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39115367703378120652539911 58673051555067180978809867)
  ·
    refine ⟨88009577332600771468214801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58673051555067180978809867 88009577332600771468214801)
    ·
      refine ⟨66007182999450578601161101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88009577332600771468214801 66007182999450578601161101)
      ·
        refine ⟨24752693624793966975435413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66007182999450578601161101 24752693624793966975435413)
        ·
          refine ⟨1160282513662217201973535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24752693624793966975435413 1160282513662217201973535)
          ·
            refine ⟨1740423770493325802960303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160282513662217201973535 1740423770493325802960303)
            ·
              refine ⟨2610635655739988704440455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1740423770493325802960303 2610635655739988704440455)
              ·
                refine ⟨3915953483609983056660683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2610635655739988704440455 3915953483609983056660683)
                ·
                  refine ⟨5873930225414974584991025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3915953483609983056660683 5873930225414974584991025)
                  ·
                    refine ⟨4405447669061230938743269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5873930225414974584991025 4405447669061230938743269)
                    ·
                      refine ⟨826021437948980801014363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4405447669061230938743269 826021437948980801014363)
                      ·
                        rfl

theorem cell23_1608671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_1608671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608671 prefixEnd_1608671 := by exact prefixLift 1608671
  have htrace : WordTrace (prefixWord ++ tailWord_1608671) baseStart_1608671 baseEnd_1608671 := by
    simpa [prefixWord, tailWord_1608671, baseEnd_1608671] using wordTrace_append hprefix tailTrace_1608671
  have hstable : (prefixWord ++ tailWord_1608671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608671).length < 2 ^ (prefixWord ++ tailWord_1608671).sum := by decide
  have hdescent : baseEnd_1608671 < baseStart_1608671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608754 : List Nat := [3, 2, 1, 1, 2, 2, 2, 5, 5]
def baseStart_1608754 : Nat := 118140960795 + 1608754 * 2 ^ 59
def prefixEnd_1608754 : Nat := 4983230072969 + 3 ^ 40 * 1608754 * 2
def baseEnd_1608754 : Nat := 91784895204811552919609

theorem tailTrace_1608754 : CollatzResearch.WordTrace tailWord_1608754 prefixEnd_1608754 91784895204811552919609 := by
  unfold tailWord_1608754
  simp only [CollatzResearch.WordTrace]
  refine ⟨14669019703441621538520329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39117385875844324102720877 14669019703441621538520329)
  ·
    refine ⟨11001764777581216153890247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14669019703441621538520329 11001764777581216153890247)
    ·
      refine ⟨16502647166371824230835371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11001764777581216153890247 16502647166371824230835371)
      ·
        refine ⟨24753970749557736346253057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16502647166371824230835371 24753970749557736346253057)
        ·
          refine ⟨18565478062168302259689793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24753970749557736346253057 18565478062168302259689793)
          ·
            refine ⟨13924108546626226694767345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18565478062168302259689793 13924108546626226694767345)
            ·
              refine ⟨10443081409969670021075509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13924108546626226694767345 10443081409969670021075509)
              ·
                refine ⟨979038882184656564475829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10443081409969670021075509 979038882184656564475829)
                ·
                  refine ⟨91784895204811552919609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 979038882184656564475829 91784895204811552919609)
                  ·
                    rfl

theorem cell23_1608754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_1608754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608754 prefixEnd_1608754 := by exact prefixLift 1608754
  have htrace : WordTrace (prefixWord ++ tailWord_1608754) baseStart_1608754 baseEnd_1608754 := by
    simpa [prefixWord, tailWord_1608754, baseEnd_1608754] using wordTrace_append hprefix tailTrace_1608754
  have hstable : (prefixWord ++ tailWord_1608754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608754).length < 2 ^ (prefixWord ++ tailWord_1608754).sum := by decide
  have hdescent : baseEnd_1608754 < baseStart_1608754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608781 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_1608781 : Nat := 118140960795 + 1608781 * 2 ^ 59
def prefixEnd_1608781 : Nat := 4983230072969 + 3 ^ 40 * 1608781 * 2
def baseEnd_1608781 : Nat := 826077920820975370638857

theorem tailTrace_1608781 : CollatzResearch.WordTrace tailWord_1608781 prefixEnd_1608781 826077920820975370638857 := by
  unfold tailWord_1608781
  simp only [CollatzResearch.WordTrace]
  refine ⟨58677063584668669765314197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39118042389779113176876131 58677063584668669765314197)
  ·
    refine ⟨2750487355531343895249103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58677063584668669765314197 2750487355531343895249103)
    ·
      refine ⟨4125731033297015842873655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2750487355531343895249103 4125731033297015842873655)
      ·
        refine ⟨6188596549945523764310483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4125731033297015842873655 6188596549945523764310483)
        ·
          refine ⟨9282894824918285646465725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6188596549945523764310483 9282894824918285646465725)
          ·
            refine ⟨3481085559344357117424647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9282894824918285646465725 3481085559344357117424647)
            ·
              refine ⟨5221628339016535676136971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3481085559344357117424647 5221628339016535676136971)
              ·
                refine ⟨7832442508524803514205457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5221628339016535676136971 7832442508524803514205457)
                ·
                  refine ⟨5874331881393602635654093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7832442508524803514205457 5874331881393602635654093)
                  ·
                    refine ⟨2202874455522600988370285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5874331881393602635654093 2202874455522600988370285)
                    ·
                      refine ⟨826077920820975370638857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2202874455522600988370285 826077920820975370638857)
                      ·
                        rfl

theorem cell23_1608781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_1608781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608781 prefixEnd_1608781 := by exact prefixLift 1608781
  have htrace : WordTrace (prefixWord ++ tailWord_1608781) baseStart_1608781 baseEnd_1608781 := by
    simpa [prefixWord, tailWord_1608781, baseEnd_1608781] using wordTrace_append hprefix tailTrace_1608781
  have hstable : (prefixWord ++ tailWord_1608781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608781).length < 2 ^ (prefixWord ++ tailWord_1608781).sum := by decide
  have hdescent : baseEnd_1608781 < baseStart_1608781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608787 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 4]
def baseStart_1608787 : Nat := 118140960795 + 1608787 * 2 ^ 59
def prefixEnd_1608787 : Nat := 4983230072969 + 3 ^ 40 * 1608787 * 2
def baseEnd_1608787 : Nat := 826081001704902347163829

theorem tailTrace_1608787 : CollatzResearch.WordTrace tailWord_1608787 prefixEnd_1608787 826081001704902347163829 := by
  unfold tailWord_1608787
  simp only [CollatzResearch.WordTrace]
  refine ⟨58677282422646932790032615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39118188281764621860021743 58677282422646932790032615)
  ·
    refine ⟨88015923633970399185048923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58677282422646932790032615 88015923633970399185048923)
    ·
      refine ⟨132023885450955598777573385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88015923633970399185048923 132023885450955598777573385)
      ·
        refine ⟨99017914088216699083180039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132023885450955598777573385 99017914088216699083180039)
        ·
          refine ⟨148526871132325048624770059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99017914088216699083180039 148526871132325048624770059)
          ·
            refine ⟨222790306698487572937155089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148526871132325048624770059 222790306698487572937155089)
            ·
              refine ⟨167092730023865679702866317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222790306698487572937155089 167092730023865679702866317)
              ·
                refine ⟨62659773758949629888574869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167092730023865679702866317 62659773758949629888574869)
                ·
                  refine ⟨2937176894950763901026947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62659773758949629888574869 2937176894950763901026947)
                  ·
                    refine ⟨4405765342426145851540421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2937176894950763901026947 4405765342426145851540421)
                    ·
                      refine ⟨826081001704902347163829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4405765342426145851540421 826081001704902347163829)
                      ·
                        rfl

theorem cell23_1608787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 4].length) (baseStart_1608787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608787 prefixEnd_1608787 := by exact prefixLift 1608787
  have htrace : WordTrace (prefixWord ++ tailWord_1608787) baseStart_1608787 baseEnd_1608787 := by
    simpa [prefixWord, tailWord_1608787, baseEnd_1608787] using wordTrace_append hprefix tailTrace_1608787
  have hstable : (prefixWord ++ tailWord_1608787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608787).length < 2 ^ (prefixWord ++ tailWord_1608787).sum := by decide
  have hdescent : baseEnd_1608787 < baseStart_1608787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608804 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 3, 6, 2]
def baseStart_1608804 : Nat := 118140960795 + 1608804 * 2 ^ 59
def prefixEnd_1608804 : Nat := 4983230072969 + 3 ^ 40 * 1608804 * 2
def baseEnd_1608804 : Nat := 826089730876028780651251

theorem tailTrace_1608804 : CollatzResearch.WordTrace tailWord_1608804 prefixEnd_1608804 826089730876028780651251 := by
  unfold tailWord_1608804
  simp only [CollatzResearch.WordTrace]
  refine ⟨29338951231792672346700733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39118601642390229795600977 29338951231792672346700733)
  ·
    refine ⟨11002106711922252130012775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29338951231792672346700733 11002106711922252130012775)
    ·
      refine ⟨16503160067883378195019163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11002106711922252130012775 16503160067883378195019163)
      ·
        refine ⟨24754740101825067292528745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16503160067883378195019163 24754740101825067292528745)
        ·
          refine ⟨18566055076368800469396559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24754740101825067292528745 18566055076368800469396559)
          ·
            refine ⟨27849082614553200704094839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18566055076368800469396559 27849082614553200704094839)
            ·
              refine ⟨41773623921829801056142259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27849082614553200704094839 41773623921829801056142259)
              ·
                refine ⟨62660435882744701584213389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41773623921829801056142259 62660435882744701584213389)
                ·
                  refine ⟨23497663456029263094080021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62660435882744701584213389 23497663456029263094080021)
                  ·
                    refine ⟨1101452974501371707535001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23497663456029263094080021 1101452974501371707535001)
                    ·
                      refine ⟨826089730876028780651251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1101452974501371707535001 826089730876028780651251)
                      ·
                        rfl

theorem cell23_1608804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_1608804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608804 prefixEnd_1608804 := by exact prefixLift 1608804
  have htrace : WordTrace (prefixWord ++ tailWord_1608804) baseStart_1608804 baseEnd_1608804 := by
    simpa [prefixWord, tailWord_1608804, baseEnd_1608804] using wordTrace_append hprefix tailTrace_1608804
  have hstable : (prefixWord ++ tailWord_1608804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608804).length < 2 ^ (prefixWord ++ tailWord_1608804).sum := by decide
  have hdescent : baseEnd_1608804 < baseStart_1608804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608824 : List Nat := [2, 1, 2, 1, 1, 1, 4, 4, 2, 2, 3]
def baseStart_1608824 : Nat := 118140960795 + 1608824 * 2 ^ 59
def prefixEnd_1608824 : Nat := 4983230072969 + 3 ^ 40 * 1608824 * 2
def baseEnd_1608824 : Nat := 826100000489118702401159

theorem tailTrace_1608824 : CollatzResearch.WordTrace tailWord_1608824 prefixEnd_1608824 826100000489118702401159 := by
  unfold tailWord_1608824
  simp only [CollatzResearch.WordTrace]
  refine ⟨29339315961756444054564763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39119087949008592072753017 29339315961756444054564763)
  ·
    refine ⟨44008973942634666081847145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29339315961756444054564763 44008973942634666081847145)
    ·
      refine ⟨33006730456975999561385359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44008973942634666081847145 33006730456975999561385359)
      ·
        refine ⟨49510095685463999342078039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33006730456975999561385359 49510095685463999342078039)
        ·
          refine ⟨74265143528195999013117059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49510095685463999342078039 74265143528195999013117059)
          ·
            refine ⟨111397715292293998519675589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74265143528195999013117059 111397715292293998519675589)
            ·
              refine ⟨20887071617305124722439173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111397715292293998519675589 20887071617305124722439173)
              ·
                refine ⟨3916325928244710885457345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20887071617305124722439173 3916325928244710885457345)
                ·
                  refine ⟨2937244446183533164093009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3916325928244710885457345 2937244446183533164093009)
                  ·
                    refine ⟨2202933334637649873069757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2937244446183533164093009 2202933334637649873069757)
                    ·
                      refine ⟨826100000489118702401159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2202933334637649873069757 826100000489118702401159)
                      ·
                        rfl

theorem cell23_1608824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 2, 2, 3].length) (baseStart_1608824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608824 prefixEnd_1608824 := by exact prefixLift 1608824
  have htrace : WordTrace (prefixWord ++ tailWord_1608824) baseStart_1608824 baseEnd_1608824 := by
    simpa [prefixWord, tailWord_1608824, baseEnd_1608824] using wordTrace_append hprefix tailTrace_1608824
  have hstable : (prefixWord ++ tailWord_1608824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608824).length < 2 ^ (prefixWord ++ tailWord_1608824).sum := by decide
  have hdescent : baseEnd_1608824 < baseStart_1608824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608925 : List Nat := [1, 4, 3, 2, 2, 1, 3, 1, 1, 5]
def baseStart_1608925 : Nat := 118140960795 + 1608925 * 2 ^ 59
def prefixEnd_1608925 : Nat := 4983230072969 + 3 ^ 40 * 1608925 * 2
def baseEnd_1608925 : Nat := 275383954011740935746065

theorem tailTrace_1608925 : CollatzResearch.WordTrace tailWord_1608925 prefixEnd_1608925 275383954011740935746065 := by
  unfold tailWord_1608925
  simp only [CollatzResearch.WordTrace]
  refine ⟨58682315696146982358556229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39121543797431321572370819 58682315696146982358556229)
  ·
    refine ⟨11002934193027559192229293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58682315696146982358556229 11002934193027559192229293)
    ·
      refine ⟨4126100322385334697085985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11002934193027559192229293 4126100322385334697085985)
      ·
        refine ⟨3094575241789001022814489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4126100322385334697085985 3094575241789001022814489)
        ·
          refine ⟨2320931431341750767110867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3094575241789001022814489 2320931431341750767110867)
          ·
            refine ⟨3481397147012626150666301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320931431341750767110867 3481397147012626150666301)
            ·
              refine ⟨1305523930129734806499863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3481397147012626150666301 1305523930129734806499863)
              ·
                refine ⟨1958285895194602209749795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1305523930129734806499863 1958285895194602209749795)
                ·
                  refine ⟨2937428842791903314624693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1958285895194602209749795 2937428842791903314624693)
                  ·
                    refine ⟨275383954011740935746065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2937428842791903314624693 275383954011740935746065)
                    ·
                      rfl

theorem cell23_1608925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_1608925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608925 prefixEnd_1608925 := by exact prefixLift 1608925
  have htrace : WordTrace (prefixWord ++ tailWord_1608925) baseStart_1608925 baseEnd_1608925 := by
    simpa [prefixWord, tailWord_1608925, baseEnd_1608925] using wordTrace_append hprefix tailTrace_1608925
  have hstable : (prefixWord ++ tailWord_1608925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608925).length < 2 ^ (prefixWord ++ tailWord_1608925).sum := by decide
  have hdescent : baseEnd_1608925 < baseStart_1608925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608928 : List Nat := [2, 1, 1, 3, 1, 5, 3, 1, 1, 1, 4]
def baseStart_1608928 : Nat := 118140960795 + 1608928 * 2 ^ 59
def prefixEnd_1608928 : Nat := 4983230072969 + 3 ^ 40 * 1608928 * 2
def baseEnd_1608928 : Nat := 826153402477186295500681

theorem tailTrace_1608928 : CollatzResearch.WordTrace tailWord_1608928 prefixEnd_1608928 826153402477186295500681 := by
  unfold tailWord_1608928
  simp only [CollatzResearch.WordTrace]
  refine ⟨29341212557568056935457719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39121616743424075913943625 29341212557568056935457719)
  ·
    refine ⟨44011818836352085403186579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29341212557568056935457719 44011818836352085403186579)
    ·
      refine ⟨66017728254528128104779869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44011818836352085403186579 66017728254528128104779869)
      ·
        refine ⟨24756648095448048039292451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66017728254528128104779869 24756648095448048039292451)
        ·
          refine ⟨37134972143172072058938677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24756648095448048039292451 37134972143172072058938677)
          ·
            refine ⟨3481403638422381755525501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37134972143172072058938677 3481403638422381755525501)
            ·
              refine ⟨1305526364408393158322063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3481403638422381755525501 1305526364408393158322063)
              ·
                refine ⟨1958289546612589737483095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1305526364408393158322063 1958289546612589737483095)
                ·
                  refine ⟨2937434319918884606224643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1958289546612589737483095 2937434319918884606224643)
                  ·
                    refine ⟨4406151479878326909336965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2937434319918884606224643 4406151479878326909336965)
                    ·
                      refine ⟨826153402477186295500681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4406151479878326909336965 826153402477186295500681)
                      ·
                        rfl

theorem cell23_1608928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_1608928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608928 prefixEnd_1608928 := by exact prefixLift 1608928
  have htrace : WordTrace (prefixWord ++ tailWord_1608928) baseStart_1608928 baseEnd_1608928 := by
    simpa [prefixWord, tailWord_1608928, baseEnd_1608928] using wordTrace_append hprefix tailTrace_1608928
  have hstable : (prefixWord ++ tailWord_1608928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608928).length < 2 ^ (prefixWord ++ tailWord_1608928).sum := by decide
  have hdescent : baseEnd_1608928 < baseStart_1608928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608938 : List Nat := [3, 1, 3, 1, 1, 4, 2, 2, 2, 4]
def baseStart_1608938 : Nat := 118140960795 + 1608938 * 2 ^ 59
def prefixEnd_1608938 : Nat := 4983230072969 + 3 ^ 40 * 1608938 * 2
def baseEnd_1608938 : Nat := 275386179094577085458545

theorem tailTrace_1608938 : CollatzResearch.WordTrace tailWord_1608938 prefixEnd_1608938 275386179094577085458545 := by
  unfold tailWord_1608938
  simp only [CollatzResearch.WordTrace]
  refine ⟨14670697461274971394694867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39121859896733257052519645 14670697461274971394694867)
  ·
    refine ⟨22006046191912457092042301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14670697461274971394694867 22006046191912457092042301)
    ·
      refine ⟨8252267321967171409515863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22006046191912457092042301 8252267321967171409515863)
      ·
        refine ⟨12378400982950757114273795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8252267321967171409515863 12378400982950757114273795)
        ·
          refine ⟨18567601474426135671410693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12378400982950757114273795 18567601474426135671410693)
          ·
            refine ⟨3481425276454900438389505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18567601474426135671410693 3481425276454900438389505)
            ·
              refine ⟨2611068957341175328792129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3481425276454900438389505 2611068957341175328792129)
              ·
                refine ⟨1958301718005881496594097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2611068957341175328792129 1958301718005881496594097)
                ·
                  refine ⟨1468726288504411122445573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1958301718005881496594097 1468726288504411122445573)
                  ·
                    refine ⟨275386179094577085458545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1468726288504411122445573 275386179094577085458545)
                    ·
                      rfl

theorem cell23_1608938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_1608938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608938 prefixEnd_1608938 := by exact prefixLift 1608938
  have htrace : WordTrace (prefixWord ++ tailWord_1608938) baseStart_1608938 baseEnd_1608938 := by
    simpa [prefixWord, tailWord_1608938, baseEnd_1608938] using wordTrace_append hprefix tailTrace_1608938
  have hstable : (prefixWord ++ tailWord_1608938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608938).length < 2 ^ (prefixWord ++ tailWord_1608938).sum := by decide
  have hdescent : baseEnd_1608938 < baseStart_1608938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608958 : List Nat := [4, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_1608958 : Nat := 118140960795 + 1608958 * 2 ^ 59
def prefixEnd_1608958 : Nat := 4983230072969 + 3 ^ 40 * 1608958 * 2
def baseEnd_1608958 : Nat := 826168806896821178125543

theorem tailTrace_1608958 : CollatzResearch.WordTrace tailWord_1608958 prefixEnd_1608958 826168806896821178125543 := by
  unfold tailWord_1608958
  simp only [CollatzResearch.WordTrace]
  refine ⟨7335439913128428624313441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39122346203351619329671685 7335439913128428624313441)
  ·
    refine ⟨5501579934846321468235081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7335439913128428624313441 5501579934846321468235081)
    ·
      refine ⟨4126184951134741101176311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5501579934846321468235081 4126184951134741101176311)
      ·
        refine ⟨6189277426702111651764467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4126184951134741101176311 6189277426702111651764467)
        ·
          refine ⟨9283916140053167477646701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6189277426702111651764467 9283916140053167477646701)
          ·
            refine ⟨3481468552519937804117513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9283916140053167477646701 3481468552519937804117513)
            ·
              refine ⟨2611101414389953353088135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3481468552519937804117513 2611101414389953353088135)
              ·
                refine ⟨3916652121584930029632203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2611101414389953353088135 3916652121584930029632203)
                ·
                  refine ⟨5874978182377395044448305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3916652121584930029632203 5874978182377395044448305)
                  ·
                    refine ⟨4406233636783046283336229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5874978182377395044448305 4406233636783046283336229)
                    ·
                      refine ⟨826168806896821178125543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4406233636783046283336229 826168806896821178125543)
                      ·
                        rfl

theorem cell23_1608958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_1608958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608958 prefixEnd_1608958 := by exact prefixLift 1608958
  have htrace : WordTrace (prefixWord ++ tailWord_1608958) baseStart_1608958 baseEnd_1608958 := by
    simpa [prefixWord, tailWord_1608958, baseEnd_1608958] using wordTrace_append hprefix tailTrace_1608958
  have hstable : (prefixWord ++ tailWord_1608958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608958).length < 2 ^ (prefixWord ++ tailWord_1608958).sum := by decide
  have hdescent : baseEnd_1608958 < baseStart_1608958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608961 : List Nat := [1, 2, 4, 1, 1, 3, 1, 3, 1, 3, 3]
def baseStart_1608961 : Nat := 118140960795 + 1608961 * 2 ^ 59
def prefixEnd_1608961 : Nat := 4983230072969 + 3 ^ 40 * 1608961 * 2
def baseEnd_1608961 : Nat := 826170347338784666388029

theorem tailTrace_1608961 : CollatzResearch.WordTrace tailWord_1608961 prefixEnd_1608961 826170347338784666388029 := by
  unfold tailWord_1608961
  simp only [CollatzResearch.WordTrace]
  refine ⟨58683628724016560506866737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39122419149344373671244491 58683628724016560506866737)
  ·
    refine ⟨44012721543012420380150053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58683628724016560506866737 44012721543012420380150053)
    ·
      refine ⟨8252385289314828821278135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44012721543012420380150053 8252385289314828821278135)
      ·
        refine ⟨12378577933972243231917203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8252385289314828821278135 12378577933972243231917203)
        ·
          refine ⟨18567866900958364847875805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12378577933972243231917203 18567866900958364847875805)
          ·
            refine ⟨6962950087859386817953427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18567866900958364847875805 6962950087859386817953427)
            ·
              refine ⟨10444425131789080226930141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6962950087859386817953427 10444425131789080226930141)
              ·
                refine ⟨3916659424420905085098803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10444425131789080226930141 3916659424420905085098803)
                ·
                  refine ⟨5874989136631357627648205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3916659424420905085098803 5874989136631357627648205)
                  ·
                    refine ⟨2203120926236759110368077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5874989136631357627648205 2203120926236759110368077)
                    ·
                      refine ⟨826170347338784666388029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2203120926236759110368077 826170347338784666388029)
                      ·
                        rfl

theorem cell23_1608961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_1608961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608961 prefixEnd_1608961 := by exact prefixLift 1608961
  have htrace : WordTrace (prefixWord ++ tailWord_1608961) baseStart_1608961 baseEnd_1608961 := by
    simpa [prefixWord, tailWord_1608961, baseEnd_1608961] using wordTrace_append hprefix tailTrace_1608961
  have hstable : (prefixWord ++ tailWord_1608961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608961).length < 2 ^ (prefixWord ++ tailWord_1608961).sum := by decide
  have hdescent : baseEnd_1608961 < baseStart_1608961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1608962 : List Nat := [3, 4, 1, 1, 3, 1, 1, 2, 3, 2, 2]
def baseStart_1608962 : Nat := 118140960795 + 1608962 * 2 ^ 59
def prefixEnd_1608962 : Nat := 4983230072969 + 3 ^ 40 * 1608962 * 2
def baseEnd_1608962 : Nat := 826170860819439162475525

theorem tailTrace_1608962 : CollatzResearch.WordTrace tailWord_1608962 prefixEnd_1608962 826170860819439162475525 := by
  unfold tailWord_1608962
  simp only [CollatzResearch.WordTrace]
  refine ⟨14670916299253234419413285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39122443464675291785102093 14670916299253234419413285)
  ·
    refine ⟨2750796806109981453639991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14670916299253234419413285 2750796806109981453639991)
    ·
      refine ⟨4126195209164972180459987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2750796806109981453639991 4126195209164972180459987)
      ·
        refine ⟨6189292813747458270689981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4126195209164972180459987 6189292813747458270689981)
        ·
          refine ⟨2320984805155296851508743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6189292813747458270689981 2320984805155296851508743)
          ·
            refine ⟨3481477207732945277263115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320984805155296851508743 3481477207732945277263115)
            ·
              refine ⟨5222215811599417915894673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3481477207732945277263115 5222215811599417915894673)
              ·
                refine ⟨3916661858699563436921005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5222215811599417915894673 3916661858699563436921005)
                ·
                  refine ⟨1468748197012336288845377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3916661858699563436921005 1468748197012336288845377)
                  ·
                    refine ⟨1101561147759252216634033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1468748197012336288845377 1101561147759252216634033)
                    ·
                      refine ⟨826170860819439162475525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1101561147759252216634033 826170860819439162475525)
                      ·
                        rfl

theorem cell23_1608962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_1608962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608962 prefixEnd_1608962 := by exact prefixLift 1608962
  have htrace : WordTrace (prefixWord ++ tailWord_1608962) baseStart_1608962 baseEnd_1608962 := by
    simpa [prefixWord, tailWord_1608962, baseEnd_1608962] using wordTrace_append hprefix tailTrace_1608962
  have hstable : (prefixWord ++ tailWord_1608962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608962).length < 2 ^ (prefixWord ++ tailWord_1608962).sum := by decide
  have hdescent : baseEnd_1608962 < baseStart_1608962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
