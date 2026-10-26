import V185TrunkScan23Chunk1267

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7512097 : List Nat := [1, 2, 3, 2, 5, 1, 1, 1, 2, 5]
def baseStart_7512097 : Nat := 118140960795 + 7512097 * 2 ^ 59
def prefixEnd_7512097 : Nat := 4983230072969 + 3 ^ 40 * 7512097 * 2
def baseEnd_7512097 : Nat := 1285772161399400206546667

theorem tailTrace_7512097 : CollatzResearch.WordTrace tailWord_7512097 prefixEnd_7512097 1285772161399400206546667 := by
  unfold tailWord_7512097
  simp only [CollatzResearch.WordTrace]
  refine ⟨273988686665963007870726545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182659124443975338580484363 273988686665963007870726545)
  ·
    refine ⟨205491514999472255903044909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273988686665963007870726545 205491514999472255903044909)
    ·
      refine ⟨77059318124802095963641841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205491514999472255903044909 77059318124802095963641841)
      ·
        refine ⟨57794488593601571972731381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77059318124802095963641841 57794488593601571972731381)
        ·
          refine ⟨5418233305650147372443567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57794488593601571972731381 5418233305650147372443567)
          ·
            refine ⟨8127349958475221058665351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5418233305650147372443567 8127349958475221058665351)
            ·
              refine ⟨12191024937712831587998027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8127349958475221058665351 12191024937712831587998027)
              ·
                refine ⟨18286537406569247381997041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12191024937712831587998027 18286537406569247381997041)
                ·
                  refine ⟨13714903054926935536497781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18286537406569247381997041 13714903054926935536497781)
                  ·
                    refine ⟨1285772161399400206546667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13714903054926935536497781 1285772161399400206546667)
                    ·
                      rfl

theorem cell23_7512097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_7512097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512097 prefixEnd_7512097 := by exact prefixLift 7512097
  have htrace : WordTrace (prefixWord ++ tailWord_7512097) baseStart_7512097 baseEnd_7512097 := by
    simpa [prefixWord, tailWord_7512097, baseEnd_7512097] using wordTrace_append hprefix tailTrace_7512097
  have hstable : (prefixWord ++ tailWord_7512097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512097).length < 2 ^ (prefixWord ++ tailWord_7512097).sum := by decide
  have hdescent : baseEnd_7512097 < baseStart_7512097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512100 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 1, 3, 4]
def baseStart_7512100 : Nat := 118140960795 + 7512100 * 2 ^ 59
def prefixEnd_7512100 : Nat := 4983230072969 + 3 ^ 40 * 7512100 * 2
def baseEnd_7512100 : Nat := 3857318024640164107902487

theorem tailTrace_7512100 : CollatzResearch.WordTrace tailWord_7512100 prefixEnd_7512100 3857318024640164107902487 := by
  unfold tailWord_7512100
  simp only [CollatzResearch.WordTrace]
  refine ⟨136994398042476069691542877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182659197389968092922057169 136994398042476069691542877)
  ·
    refine ⟨51372899265928526134328579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136994398042476069691542877 51372899265928526134328579)
    ·
      refine ⟨77059348898892789201492869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51372899265928526134328579 77059348898892789201492869)
      ·
        refine ⟨14448627918542397975279913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77059348898892789201492869 14448627918542397975279913)
        ·
          refine ⟨10836470938906798481459935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14448627918542397975279913 10836470938906798481459935)
          ·
            refine ⟨16254706408360197722189903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10836470938906798481459935 16254706408360197722189903)
            ·
              refine ⟨24382059612540296583284855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16254706408360197722189903 24382059612540296583284855)
              ·
                refine ⟨36573089418810444874927283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24382059612540296583284855 36573089418810444874927283)
                ·
                  refine ⟨54859634128215667312390925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36573089418810444874927283 54859634128215667312390925)
                  ·
                    refine ⟨20572362798080875242146597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54859634128215667312390925 20572362798080875242146597)
                    ·
                      refine ⟨3857318024640164107902487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20572362798080875242146597 3857318024640164107902487)
                      ·
                        rfl

theorem cell23_7512100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_7512100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512100 prefixEnd_7512100 := by exact prefixLift 7512100
  have htrace : WordTrace (prefixWord ++ tailWord_7512100) baseStart_7512100 baseEnd_7512100 := by
    simpa [prefixWord, tailWord_7512100, baseEnd_7512100] using wordTrace_append hprefix tailTrace_7512100
  have hstable : (prefixWord ++ tailWord_7512100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512100).length < 2 ^ (prefixWord ++ tailWord_7512100).sum := by decide
  have hdescent : baseEnd_7512100 < baseStart_7512100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512136 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 2, 9]
def baseStart_7512136 : Nat := 118140960795 + 7512136 * 2 ^ 59
def prefixEnd_7512136 : Nat := 4983230072969 + 3 ^ 40 * 7512136 * 2
def baseEnd_7512136 : Nat := 1285778836647908655684107

theorem tailTrace_7512136 : CollatzResearch.WordTrace tailWord_7512136 prefixEnd_7512136 1285778836647908655684107 := by
  unfold tailWord_7512136
  simp only [CollatzResearch.WordTrace]
  refine ⟨136995054556410858765698131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182660072741881145020930841 136995054556410858765698131)
  ·
    refine ⟨205492581834616288148547197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136995054556410858765698131 205492581834616288148547197)
    ·
      refine ⟨77059718187981108055705199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205492581834616288148547197 77059718187981108055705199)
      ·
        refine ⟨115589577281971662083557799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77059718187981108055705199 115589577281971662083557799)
        ·
          refine ⟨173384365922957493125336699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115589577281971662083557799 173384365922957493125336699)
          ·
            refine ⟨260076548884436239688005049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173384365922957493125336699 260076548884436239688005049)
            ·
              refine ⟨195057411663327179766003787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260076548884436239688005049 195057411663327179766003787)
              ·
                refine ⟨292586117494990769649005681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195057411663327179766003787 292586117494990769649005681)
                ·
                  refine ⟨219439588121243077236754261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292586117494990769649005681 219439588121243077236754261)
                  ·
                    refine ⟨1285778836647908655684107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 219439588121243077236754261 1285778836647908655684107)
                    ·
                      rfl

theorem cell23_7512136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_7512136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512136 prefixEnd_7512136 := by exact prefixLift 7512136
  have htrace : WordTrace (prefixWord ++ tailWord_7512136) baseStart_7512136 baseEnd_7512136 := by
    simpa [prefixWord, tailWord_7512136, baseEnd_7512136] using wordTrace_append hprefix tailTrace_7512136
  have hstable : (prefixWord ++ tailWord_7512136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512136).length < 2 ^ (prefixWord ++ tailWord_7512136).sum := by decide
  have hdescent : baseEnd_7512136 < baseStart_7512136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512160 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 1, 5, 2]
def baseStart_7512160 : Nat := 118140960795 + 7512160 * 2 ^ 59
def prefixEnd_7512160 : Nat := 4983230072969 + 3 ^ 40 * 7512160 * 2
def baseEnd_7512160 : Nat := 3857348833479433873152211

theorem tailTrace_7512160 : CollatzResearch.WordTrace tailWord_7512160 prefixEnd_7512160 3857348833479433873152211 := by
  unfold tailWord_7512160
  simp only [CollatzResearch.WordTrace]
  refine ⟨136995492232367384815134967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182660656309823179753513289 136995492232367384815134967)
  ·
    refine ⟨205493238348551077222702451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136995492232367384815134967 205493238348551077222702451)
    ·
      refine ⟨308239857522826615834053677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205493238348551077222702451 308239857522826615834053677)
      ·
        refine ⟨115589946571059980937770129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308239857522826615834053677 115589946571059980937770129)
        ·
          refine ⟨86692459928294985703327597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115589946571059980937770129 86692459928294985703327597)
          ·
            refine ⟨32509672473110619638747849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86692459928294985703327597 32509672473110619638747849)
            ·
              refine ⟨24382254354832964729060887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32509672473110619638747849 24382254354832964729060887)
              ·
                refine ⟨36573381532249447093591331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24382254354832964729060887 36573381532249447093591331)
                ·
                  refine ⟨54860072298374170640386997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36573381532249447093591331 54860072298374170640386997)
                  ·
                    refine ⟨5143131777972578497536281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54860072298374170640386997 5143131777972578497536281)
                    ·
                      refine ⟨3857348833479433873152211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5143131777972578497536281 3857348833479433873152211)
                      ·
                        rfl

theorem cell23_7512160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_7512160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512160 prefixEnd_7512160 := by exact prefixLift 7512160
  have htrace : WordTrace (prefixWord ++ tailWord_7512160) baseStart_7512160 baseEnd_7512160 := by
    simpa [prefixWord, tailWord_7512160, baseEnd_7512160] using wordTrace_append hprefix tailTrace_7512160
  have hstable : (prefixWord ++ tailWord_7512160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512160).length < 2 ^ (prefixWord ++ tailWord_7512160).sum := by decide
  have hdescent : baseEnd_7512160 < baseStart_7512160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512220 : List Nat := [2, 2, 3, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_7512220 : Nat := 118140960795 + 7512220 * 2 ^ 59
def prefixEnd_7512220 : Nat := 4983230072969 + 3 ^ 40 * 7512220 * 2
def baseEnd_7512220 : Nat := 3857379642318703638401935

theorem tailTrace_7512220 : CollatzResearch.WordTrace tailWord_7512220 prefixEnd_7512220 3857379642318703638401935 := by
  unfold tailWord_7512220
  simp only [CollatzResearch.WordTrace]
  refine ⟨136996586422258699938727057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182662115229678266584969409 136996586422258699938727057)
  ·
    refine ⟨102747439816694024954045293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136996586422258699938727057 102747439816694024954045293)
    ·
      refine ⟨38530289931260259357766985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102747439816694024954045293 38530289931260259357766985)
      ·
        refine ⟨28897717448445194518325239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38530289931260259357766985 28897717448445194518325239)
        ·
          refine ⟨43346576172667791777487859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28897717448445194518325239 43346576172667791777487859)
          ·
            refine ⟨65019864259001687666231789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43346576172667791777487859 65019864259001687666231789)
            ·
              refine ⟨24382449097125632874836921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65019864259001687666231789 24382449097125632874836921)
              ·
                refine ⟨18286836822844224656127691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24382449097125632874836921 18286836822844224656127691)
                ·
                  refine ⟨27430255234266336984191537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18286836822844224656127691 27430255234266336984191537)
                  ·
                    refine ⟨20572691425699752738143653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27430255234266336984191537 20572691425699752738143653)
                    ·
                      refine ⟨3857379642318703638401935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20572691425699752738143653 3857379642318703638401935)
                      ·
                        rfl

theorem cell23_7512220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_7512220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512220 prefixEnd_7512220 := by exact prefixLift 7512220
  have htrace : WordTrace (prefixWord ++ tailWord_7512220) baseStart_7512220 baseEnd_7512220 := by
    simpa [prefixWord, tailWord_7512220, baseEnd_7512220] using wordTrace_append hprefix tailTrace_7512220
  have hstable : (prefixWord ++ tailWord_7512220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512220).length < 2 ^ (prefixWord ++ tailWord_7512220).sum := by decide
  have hdescent : baseEnd_7512220 < baseStart_7512220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512253 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_7512253 : Nat := 118140960795 + 7512253 * 2 ^ 59
def prefixEnd_7512253 : Nat := 4983230072969 + 3 ^ 40 * 7512253 * 2
def baseEnd_7512253 : Nat := 3857396587180302009289283

theorem tailTrace_7512253 : CollatzResearch.WordTrace tailWord_7512253 prefixEnd_7512253 3857396587180302009289283 := by
  unfold tailWord_7512253
  simp only [CollatzResearch.WordTrace]
  refine ⟨273994376453397846513405413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182662917635598564342270275 273994376453397846513405413)
  ·
    refine ⟨51373945585012096221263515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 273994376453397846513405413 51373945585012096221263515)
    ·
      refine ⟨77060918377518144331895273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51373945585012096221263515 77060918377518144331895273)
      ·
        refine ⟨57795688783138608248921455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77060918377518144331895273 57795688783138608248921455)
        ·
          refine ⟨86693533174707912373382183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57795688783138608248921455 86693533174707912373382183)
          ·
            refine ⟨130040299762061868560073275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86693533174707912373382183 130040299762061868560073275)
            ·
              refine ⟨195060449643092802840109913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130040299762061868560073275 195060449643092802840109913)
              ·
                refine ⟨146295337232319602130082435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195060449643092802840109913 146295337232319602130082435)
                ·
                  refine ⟨219443005848479403195123653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146295337232319602130082435 219443005848479403195123653)
                  ·
                    refine ⟨41145563596589888099085685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 219443005848479403195123653 41145563596589888099085685)
                    ·
                      refine ⟨3857396587180302009289283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41145563596589888099085685 3857396587180302009289283)
                      ·
                        rfl

theorem cell23_7512253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_7512253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512253 prefixEnd_7512253 := by exact prefixLift 7512253
  have htrace : WordTrace (prefixWord ++ tailWord_7512253) baseStart_7512253 baseEnd_7512253 := by
    simpa [prefixWord, tailWord_7512253, baseEnd_7512253] using wordTrace_append hprefix tailTrace_7512253
  have hstable : (prefixWord ++ tailWord_7512253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512253).length < 2 ^ (prefixWord ++ tailWord_7512253).sum := by decide
  have hdescent : baseEnd_7512253 < baseStart_7512253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512258 : List Nat := [3, 5, 1, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_7512258 : Nat := 118140960795 + 7512258 * 2 ^ 59
def prefixEnd_7512258 : Nat := 4983230072969 + 3 ^ 40 * 7512258 * 2
def baseEnd_7512258 : Nat := 3857399154583574489726761

theorem tailTrace_7512258 : CollatzResearch.WordTrace tailWord_7512258 prefixEnd_7512258 3857399154583574489726761 := by
  unfold tailWord_7512258
  simp only [CollatzResearch.WordTrace]
  refine ⟨68498639704594933091834357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182663039212253154911558285 68498639704594933091834357)
  ·
    refine ⟨6421747472305774977359471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68498639704594933091834357 6421747472305774977359471)
    ·
      refine ⟨9632621208458662466039207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6421747472305774977359471 9632621208458662466039207)
      ·
        refine ⟨14448931812687993699058811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9632621208458662466039207 14448931812687993699058811)
        ·
          refine ⟨21673397719031990548588217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14448931812687993699058811 21673397719031990548588217)
          ·
            refine ⟨16255048289273992911441163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21673397719031990548588217 16255048289273992911441163)
            ·
              refine ⟨24382572433910989367161745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16255048289273992911441163 24382572433910989367161745)
              ·
                refine ⟨18286929325433242025371309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24382572433910989367161745 18286929325433242025371309)
                ·
                  refine ⟨6857598497037465759514241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18286929325433242025371309 6857598497037465759514241)
                  ·
                    refine ⟨5143198872778099319635681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6857598497037465759514241 5143198872778099319635681)
                    ·
                      refine ⟨3857399154583574489726761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5143198872778099319635681 3857399154583574489726761)
                      ·
                        rfl

theorem cell23_7512258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_7512258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512258 prefixEnd_7512258 := by exact prefixLift 7512258
  have htrace : WordTrace (prefixWord ++ tailWord_7512258) baseStart_7512258 baseEnd_7512258 := by
    simpa [prefixWord, tailWord_7512258, baseEnd_7512258] using wordTrace_append hprefix tailTrace_7512258
  have hstable : (prefixWord ++ tailWord_7512258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512258).length < 2 ^ (prefixWord ++ tailWord_7512258).sum := by decide
  have hdescent : baseEnd_7512258 < baseStart_7512258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512267 : List Nat := [1, 1, 1, 1, 3, 2, 4, 4, 1, 3, 2]
def baseStart_7512267 : Nat := 118140960795 + 7512267 * 2 ^ 59
def prefixEnd_7512267 : Nat := 4983230072969 + 3 ^ 40 * 7512267 * 2
def baseEnd_7512267 : Nat := 3857403775909464954514219

theorem tailTrace_7512267 : CollatzResearch.WordTrace tailWord_7512267 prefixEnd_7512267 3857403775909464954514219 := by
  unfold tailWord_7512267
  simp only [CollatzResearch.WordTrace]
  refine ⟨273994887075347126904415055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182663258050231417936276703 273994887075347126904415055)
  ·
    refine ⟨410992330613020690356622583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273994887075347126904415055 410992330613020690356622583)
    ·
      refine ⟨616488495919531035534933875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410992330613020690356622583 616488495919531035534933875)
      ·
        refine ⟨924732743879296553302400813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616488495919531035534933875 924732743879296553302400813)
        ·
          refine ⟨346774778954736207488400305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 924732743879296553302400813 346774778954736207488400305)
          ·
            refine ⟨260081084216052155616300229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346774778954736207488400305 260081084216052155616300229)
            ·
              refine ⟨48765203290509779178056293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260081084216052155616300229 48765203290509779178056293)
              ·
                refine ⟨9143475616970583595885555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48765203290509779178056293 9143475616970583595885555)
                ·
                  refine ⟨13715213425455875393828333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9143475616970583595885555 13715213425455875393828333)
                  ·
                    refine ⟨5143205034545953272685625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13715213425455875393828333 5143205034545953272685625)
                    ·
                      refine ⟨3857403775909464954514219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5143205034545953272685625 3857403775909464954514219)
                      ·
                        rfl

theorem cell23_7512267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 3, 2].length) (baseStart_7512267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512267 prefixEnd_7512267 := by exact prefixLift 7512267
  have htrace : WordTrace (prefixWord ++ tailWord_7512267) baseStart_7512267 baseEnd_7512267 := by
    simpa [prefixWord, tailWord_7512267, baseEnd_7512267] using wordTrace_append hprefix tailTrace_7512267
  have hstable : (prefixWord ++ tailWord_7512267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512267).length < 2 ^ (prefixWord ++ tailWord_7512267).sum := by decide
  have hdescent : baseEnd_7512267 < baseStart_7512267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512278 : List Nat := [5, 2, 1, 2, 1, 3, 2, 1, 1, 2, 3]
def baseStart_7512278 : Nat := 118140960795 + 7512278 * 2 ^ 59
def prefixEnd_7512278 : Nat := 4983230072969 + 3 ^ 40 * 7512278 * 2
def baseEnd_7512278 : Nat := 3857409424196664411476669

theorem tailTrace_7512278 : CollatzResearch.WordTrace tailWord_7512278 prefixEnd_7512278 3857409424196664411476669 := by
  unfold tailWord_7512278
  simp only [CollatzResearch.WordTrace]
  refine ⟨17124705517394204736441593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182663525518871517188710325 17124705517394204736441593)
  ·
    refine ⟨12843529138045653552331195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17124705517394204736441593 12843529138045653552331195)
    ·
      refine ⟨19265293707068480328496793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12843529138045653552331195 19265293707068480328496793)
      ·
        refine ⟨14448970280301360246372595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19265293707068480328496793 14448970280301360246372595)
        ·
          refine ⟨21673455420452040369558893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14448970280301360246372595 21673455420452040369558893)
          ·
            refine ⟨8127545782669515138584585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21673455420452040369558893 8127545782669515138584585)
            ·
              refine ⟨6095659337002136353938439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8127545782669515138584585 6095659337002136353938439)
              ·
                refine ⟨9143489005503204530907659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6095659337002136353938439 9143489005503204530907659)
                ·
                  refine ⟨13715233508254806796361489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9143489005503204530907659 13715233508254806796361489)
                  ·
                    refine ⟨10286425131191105097271117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13715233508254806796361489 10286425131191105097271117)
                    ·
                      refine ⟨3857409424196664411476669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10286425131191105097271117 3857409424196664411476669)
                      ·
                        rfl

theorem cell23_7512278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_7512278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512278 prefixEnd_7512278 := by exact prefixLift 7512278
  have htrace : WordTrace (prefixWord ++ tailWord_7512278) baseStart_7512278 baseEnd_7512278 := by
    simpa [prefixWord, tailWord_7512278, baseEnd_7512278] using wordTrace_append hprefix tailTrace_7512278
  have hstable : (prefixWord ++ tailWord_7512278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512278).length < 2 ^ (prefixWord ++ tailWord_7512278).sum := by decide
  have hdescent : baseEnd_7512278 < baseStart_7512278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512297 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 4, 2, 2]
def baseStart_7512297 : Nat := 118140960795 + 7512297 * 2 ^ 59
def prefixEnd_7512297 : Nat := 4983230072969 + 3 ^ 40 * 7512297 * 2
def baseEnd_7512297 : Nat := 3857419180329099837139081

theorem tailTrace_7512297 : CollatzResearch.WordTrace tailWord_7512297 prefixEnd_7512297 3857419180329099837139081 := by
  unfold tailWord_7512297
  simp only [CollatzResearch.WordTrace]
  refine ⟨273995981265238442028007145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182663987510158961352004763 273995981265238442028007145)
  ·
    refine ⟨205496985948928831521005359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273995981265238442028007145 205496985948928831521005359)
    ·
      refine ⟨308245478923393247281508039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205496985948928831521005359 308245478923393247281508039)
      ·
        refine ⟨462368218385089870922262059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308245478923393247281508039 462368218385089870922262059)
        ·
          refine ⟨693552327577634806383393089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462368218385089870922262059 693552327577634806383393089)
          ·
            refine ⟨520164245683226104787544817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 693552327577634806383393089 520164245683226104787544817)
            ·
              refine ⟨390123184262419578590658613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520164245683226104787544817 390123184262419578590658613)
              ·
                refine ⟨36574048524601835492874245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 390123184262419578590658613 36574048524601835492874245)
                ·
                  refine ⟨6857634098362844154913921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36574048524601835492874245 6857634098362844154913921)
                  ·
                    refine ⟨5143225573772133116185441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6857634098362844154913921 5143225573772133116185441)
                    ·
                      refine ⟨3857419180329099837139081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5143225573772133116185441 3857419180329099837139081)
                      ·
                        rfl

theorem cell23_7512297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 2, 2].length) (baseStart_7512297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512297 prefixEnd_7512297 := by exact prefixLift 7512297
  have htrace : WordTrace (prefixWord ++ tailWord_7512297) baseStart_7512297 baseEnd_7512297 := by
    simpa [prefixWord, tailWord_7512297, baseEnd_7512297] using wordTrace_append hprefix tailTrace_7512297
  have hstable : (prefixWord ++ tailWord_7512297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512297).length < 2 ^ (prefixWord ++ tailWord_7512297).sum := by decide
  have hdescent : baseEnd_7512297 < baseStart_7512297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512314 : List Nat := [3, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2]
def baseStart_7512314 : Nat := 118140960795 + 7512314 * 2 ^ 59
def prefixEnd_7512314 : Nat := 4983230072969 + 3 ^ 40 * 7512314 * 2
def baseEnd_7512314 : Nat := 3857427909500226270626503

theorem tailTrace_7512314 : CollatzResearch.WordTrace tailWord_7512314 prefixEnd_7512314 3857427909500226270626503 := by
  unfold tailWord_7512314
  simp only [CollatzResearch.WordTrace]
  refine ⟨68499150326544213482843999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182664400870784569287583997 68499150326544213482843999)
  ·
    refine ⟨102748725489816320224265999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68499150326544213482843999 102748725489816320224265999)
    ·
      refine ⟨154123088234724480336398999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102748725489816320224265999 154123088234724480336398999)
      ·
        refine ⟨231184632352086720504598499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154123088234724480336398999 231184632352086720504598499)
        ·
          refine ⟨346776948528130080756897749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231184632352086720504598499 346776948528130080756897749)
          ·
            refine ⟨8127584731128048767739791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 346776948528130080756897749 8127584731128048767739791)
            ·
              refine ⟨12191377096692073151609687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8127584731128048767739791 12191377096692073151609687)
              ·
                refine ⟨18287065645038109727414531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12191377096692073151609687 18287065645038109727414531)
                ·
                  refine ⟨27430598467557164591121797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18287065645038109727414531 27430598467557164591121797)
                  ·
                    refine ⟨5143237212666968360835337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27430598467557164591121797 5143237212666968360835337)
                    ·
                      refine ⟨3857427909500226270626503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5143237212666968360835337 3857427909500226270626503)
                      ·
                        rfl

theorem cell23_7512314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2].length) (baseStart_7512314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512314 prefixEnd_7512314 := by exact prefixLift 7512314
  have htrace : WordTrace (prefixWord ++ tailWord_7512314) baseStart_7512314 baseEnd_7512314 := by
    simpa [prefixWord, tailWord_7512314, baseEnd_7512314] using wordTrace_append hprefix tailTrace_7512314
  have hstable : (prefixWord ++ tailWord_7512314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512314).length < 2 ^ (prefixWord ++ tailWord_7512314).sum := by decide
  have hdescent : baseEnd_7512314 < baseStart_7512314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512330 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3]
def baseStart_7512330 : Nat := 118140960795 + 7512330 * 2 ^ 59
def prefixEnd_7512330 : Nat := 4983230072969 + 3 ^ 40 * 7512330 * 2
def baseEnd_7512330 : Nat := 3857436125190698208026429

theorem tailTrace_7512330 : CollatzResearch.WordTrace tailWord_7512330 prefixEnd_7512330 3857436125190698208026429 := by
  unfold tailWord_7512330
  simp only [CollatzResearch.WordTrace]
  refine ⟨68499296218529722165989611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182664789916079259109305629 68499296218529722165989611)
  ·
    refine ⟨102748944327794583248984417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68499296218529722165989611 102748944327794583248984417)
    ·
      refine ⟨77061708245845937436738313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102748944327794583248984417 77061708245845937436738313)
      ·
        refine ⟨57796281184384453077553735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77061708245845937436738313 57796281184384453077553735)
        ·
          refine ⟨86694421776576679616330603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57796281184384453077553735 86694421776576679616330603)
          ·
            refine ⟨130041632664865019424495905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86694421776576679616330603 130041632664865019424495905)
            ·
              refine ⟨97531224498648764568371929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130041632664865019424495905 97531224498648764568371929)
              ·
                refine ⟨73148418373986573426278947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97531224498648764568371929 73148418373986573426278947)
                ·
                  refine ⟨109722627560979860139418421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73148418373986573426278947 109722627560979860139418421)
                  ·
                    refine ⟨10286496333841861888070477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109722627560979860139418421 10286496333841861888070477)
                    ·
                      refine ⟨3857436125190698208026429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10286496333841861888070477 3857436125190698208026429)
                      ·
                        rfl

theorem cell23_7512330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_7512330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512330 prefixEnd_7512330 := by exact prefixLift 7512330
  have htrace : WordTrace (prefixWord ++ tailWord_7512330) baseStart_7512330 baseEnd_7512330 := by
    simpa [prefixWord, tailWord_7512330, baseEnd_7512330] using wordTrace_append hprefix tailTrace_7512330
  have hstable : (prefixWord ++ tailWord_7512330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512330).length < 2 ^ (prefixWord ++ tailWord_7512330).sum := by decide
  have hdescent : baseEnd_7512330 < baseStart_7512330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512337 : List Nat := [1, 2, 2, 1, 1, 5, 3, 3, 5]
def baseStart_7512337 : Nat := 118140960795 + 7512337 * 2 ^ 59
def prefixEnd_7512337 : Nat := 4983230072969 + 3 ^ 40 * 7512337 * 2
def baseEnd_7512337 : Nat := 428604413283919964515433

theorem tailTrace_7512337 : CollatzResearch.WordTrace tailWord_7512337 prefixEnd_7512337 428604413283919964515433 := by
  unfold tailWord_7512337
  simp only [CollatzResearch.WordTrace]
  refine ⟨273997440185093528859463265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182664960123395685906308843 273997440185093528859463265)
  ·
    refine ⟨205498080138820146644597449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273997440185093528859463265 205498080138820146644597449)
    ·
      refine ⟨154123560104115109983448087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205498080138820146644597449 154123560104115109983448087)
      ·
        refine ⟨231185340156172664975172131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154123560104115109983448087 231185340156172664975172131)
        ·
          refine ⟨346778010234258997462758197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231185340156172664975172131 346778010234258997462758197)
          ·
            refine ⟨32510438459461781012133581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 346778010234258997462758197 32510438459461781012133581)
            ·
              refine ⟨12191414422298167879550093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32510438459461781012133581 12191414422298167879550093)
              ·
                refine ⟨4571780408361812954831285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12191414422298167879550093 4571780408361812954831285)
                ·
                  refine ⟨428604413283919964515433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4571780408361812954831285 428604413283919964515433)
                  ·
                    rfl

theorem cell23_7512337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 5].length) (baseStart_7512337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512337 prefixEnd_7512337 := by exact prefixLift 7512337
  have htrace : WordTrace (prefixWord ++ tailWord_7512337) baseStart_7512337 baseEnd_7512337 := by
    simpa [prefixWord, tailWord_7512337, baseEnd_7512337] using wordTrace_append hprefix tailTrace_7512337
  have hstable : (prefixWord ++ tailWord_7512337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512337).length < 2 ^ (prefixWord ++ tailWord_7512337).sum := by decide
  have hdescent : baseEnd_7512337 < baseStart_7512337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512407 : List Nat := [1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 3]
def baseStart_7512407 : Nat := 118140960795 + 7512407 * 2 ^ 59
def prefixEnd_7512407 : Nat := 4983230072969 + 3 ^ 40 * 7512407 * 2
def baseEnd_7512407 : Nat := 3857475663201094406763575

theorem tailTrace_7512407 : CollatzResearch.WordTrace tailWord_7512407 prefixEnd_7512407 3857475663201094406763575 := by
  unfold tailWord_7512407
  simp only [CollatzResearch.WordTrace]
  refine ⟨273999993294839930814511475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182666662196559953876340983 273999993294839930814511475)
  ·
    refine ⟨410999989942259896221767213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273999993294839930814511475 410999989942259896221767213)
    ·
      refine ⟨154124996228347461083162705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410999989942259896221767213 154124996228347461083162705)
      ·
        refine ⟨115593747171260595812372029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154124996228347461083162705 115593747171260595812372029)
        ·
          refine ⟨43347655189222723429639511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115593747171260595812372029 43347655189222723429639511)
          ·
            refine ⟨65021482783834085144459267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43347655189222723429639511 65021482783834085144459267)
            ·
              refine ⟨97532224175751127716688901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65021482783834085144459267 97532224175751127716688901)
              ·
                refine ⟨18287292032953336446879169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97532224175751127716688901 18287292032953336446879169)
                ·
                  refine ⟨13715469024715002335159377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18287292032953336446879169 13715469024715002335159377)
                  ·
                    refine ⟨10286601768536251751369533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13715469024715002335159377 10286601768536251751369533)
                    ·
                      refine ⟨3857475663201094406763575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10286601768536251751369533 3857475663201094406763575)
                      ·
                        rfl

theorem cell23_7512407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_7512407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512407 prefixEnd_7512407 := by exact prefixLift 7512407
  have htrace : WordTrace (prefixWord ++ tailWord_7512407) baseStart_7512407 baseEnd_7512407 := by
    simpa [prefixWord, tailWord_7512407, baseEnd_7512407] using wordTrace_append hprefix tailTrace_7512407
  have hstable : (prefixWord ++ tailWord_7512407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512407).length < 2 ^ (prefixWord ++ tailWord_7512407).sum := by decide
  have hdescent : baseEnd_7512407 < baseStart_7512407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512438 : List Nat := [5, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4]
def baseStart_7512438 : Nat := 118140960795 + 7512438 * 2 ^ 59
def prefixEnd_7512438 : Nat := 4983230072969 + 3 ^ 40 * 7512438 * 2
def baseEnd_7512438 : Nat := 3857491581101383785475933

theorem tailTrace_7512438 : CollatzResearch.WordTrace tailWord_7512438 prefixEnd_7512438 3857491581101383785475933 := by
  unfold tailWord_7512438
  simp only [CollatzResearch.WordTrace]
  refine ⟨17125070247357976444305623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182667415971818415405926645 17125070247357976444305623)
  ·
    refine ⟨25687605371036964666458435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17125070247357976444305623 25687605371036964666458435)
    ·
      refine ⟨38531408056555446999687653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25687605371036964666458435 38531408056555446999687653)
      ·
        refine ⟨7224639010604146312441435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38531408056555446999687653 7224639010604146312441435)
        ·
          refine ⟨10836958515906219468662153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7224639010604146312441435 10836958515906219468662153)
          ·
            refine ⟨8127718886929664601496615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10836958515906219468662153 8127718886929664601496615)
            ·
              refine ⟨12191578330394496902244923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8127718886929664601496615 12191578330394496902244923)
              ·
                refine ⟨18287367495591745353367385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12191578330394496902244923 18287367495591745353367385)
                ·
                  refine ⟨13715525621693809015025539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18287367495591745353367385 13715525621693809015025539)
                  ·
                    refine ⟨20573288432540713522538309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13715525621693809015025539 20573288432540713522538309)
                    ·
                      refine ⟨3857491581101383785475933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20573288432540713522538309 3857491581101383785475933)
                      ·
                        rfl

theorem cell23_7512438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_7512438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512438 prefixEnd_7512438 := by exact prefixLift 7512438
  have htrace : WordTrace (prefixWord ++ tailWord_7512438) baseStart_7512438 baseEnd_7512438 := by
    simpa [prefixWord, tailWord_7512438, baseEnd_7512438] using wordTrace_append hprefix tailTrace_7512438
  have hstable : (prefixWord ++ tailWord_7512438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512438).length < 2 ^ (prefixWord ++ tailWord_7512438).sum := by decide
  have hdescent : baseEnd_7512438 < baseStart_7512438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512447 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 1, 5, 2]
def baseStart_7512447 : Nat := 118140960795 + 7512447 * 2 ^ 59
def prefixEnd_7512447 : Nat := 4983230072969 + 3 ^ 40 * 7512447 * 2
def baseEnd_7512447 : Nat := 3857496202427274250263391

theorem tailTrace_7512447 : CollatzResearch.WordTrace tailWord_7512447 prefixEnd_7512447 3857496202427274250263391 := by
  unfold tailWord_7512447
  simp only [CollatzResearch.WordTrace]
  refine ⟨274001452214695017645967595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182667634809796678430645063 274001452214695017645967595)
  ·
    refine ⟨411002178322042526468951393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274001452214695017645967595 411002178322042526468951393)
    ·
      refine ⟨308251633741531894851713545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411002178322042526468951393 308251633741531894851713545)
      ·
        refine ⟨231188725306148921138785159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308251633741531894851713545 231188725306148921138785159)
        ·
          refine ⟨346783087959223381708177739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231188725306148921138785159 346783087959223381708177739)
          ·
            refine ⟨520174631938835072562266609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346783087959223381708177739 520174631938835072562266609)
            ·
              refine ⟨390130973954126304421699957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520174631938835072562266609 390130973954126304421699957)
              ·
                refine ⟨36574778808199341039534371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 390130973954126304421699957 36574778808199341039534371)
                ·
                  refine ⟨54862168212299011559301557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36574778808199341039534371 54862168212299011559301557)
                  ·
                    refine ⟨5143328269903032333684521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54862168212299011559301557 5143328269903032333684521)
                    ·
                      refine ⟨3857496202427274250263391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5143328269903032333684521 3857496202427274250263391)
                      ·
                        rfl

theorem cell23_7512447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 5, 2].length) (baseStart_7512447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512447 prefixEnd_7512447 := by exact prefixLift 7512447
  have htrace : WordTrace (prefixWord ++ tailWord_7512447) baseStart_7512447 baseEnd_7512447 := by
    simpa [prefixWord, tailWord_7512447, baseEnd_7512447] using wordTrace_append hprefix tailTrace_7512447
  have hstable : (prefixWord ++ tailWord_7512447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512447).length < 2 ^ (prefixWord ++ tailWord_7512447).sum := by decide
  have hdescent : baseEnd_7512447 < baseStart_7512447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512471 : List Nat := [1, 1, 3, 3, 1, 1, 4, 4, 1, 1, 3]
def baseStart_7512471 : Nat := 118140960795 + 7512471 * 2 ^ 59
def prefixEnd_7512471 : Nat := 4983230072969 + 3 ^ 40 * 7512471 * 2
def baseEnd_7512471 : Nat := 3857508525962982156363281

theorem tailTrace_7512471 : CollatzResearch.WordTrace tailWord_7512471 prefixEnd_7512471 3857508525962982156363281 := by
  unfold tailWord_7512471
  simp only [CollatzResearch.WordTrace]
  refine ⟨274002327566608069744841267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182668218377738713163227511 274002327566608069744841267)
  ·
    refine ⟨411003491349912104617261901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274002327566608069744841267 411003491349912104617261901)
    ·
      refine ⟨154126309256217039231473213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411003491349912104617261901 154126309256217039231473213)
      ·
        refine ⟨57797365971081389711802455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154126309256217039231473213 57797365971081389711802455)
        ·
          refine ⟨86696048956622084567703683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57797365971081389711802455 86696048956622084567703683)
          ·
            refine ⟨130044073434933126851555525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86696048956622084567703683 130044073434933126851555525)
            ·
              refine ⟨24383263769049961284666661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130044073434933126851555525 24383263769049961284666661)
              ·
                refine ⟨4571861956696867740874999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24383263769049961284666661 4571861956696867740874999)
                ·
                  refine ⟨6857792935045301611312499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4571861956696867740874999 6857792935045301611312499)
                  ·
                    refine ⟨10286689402567952416968749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6857792935045301611312499 10286689402567952416968749)
                    ·
                      refine ⟨3857508525962982156363281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10286689402567952416968749 3857508525962982156363281)
                      ·
                        rfl

theorem cell23_7512471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_7512471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512471 prefixEnd_7512471 := by exact prefixLift 7512471
  have htrace : WordTrace (prefixWord ++ tailWord_7512471) baseStart_7512471 baseEnd_7512471 := by
    simpa [prefixWord, tailWord_7512471, baseEnd_7512471] using wordTrace_append hprefix tailTrace_7512471
  have hstable : (prefixWord ++ tailWord_7512471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512471).length < 2 ^ (prefixWord ++ tailWord_7512471).sum := by decide
  have hdescent : baseEnd_7512471 < baseStart_7512471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512534 : List Nat := [5, 2, 1, 1, 1, 1, 4, 8]
def baseStart_7512534 : Nat := 118140960795 + 7512534 * 2 ^ 59
def prefixEnd_7512534 : Nat := 4983230072969 + 3 ^ 40 * 7512534 * 2
def baseEnd_7512534 : Nat := 142871884268304274439833

theorem tailTrace_7512534 : CollatzResearch.WordTrace tailWord_7512534 prefixEnd_7512534 142871884268304274439833 := by
  unfold tailWord_7512534
  simp only [CollatzResearch.WordTrace]
  refine ⟨17125289085336239469024041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182669750243586554336256437 17125289085336239469024041)
  ·
    refine ⟨12843966814002179601768031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17125289085336239469024041 12843966814002179601768031)
    ·
      refine ⟨19265950221003269402652047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12843966814002179601768031 19265950221003269402652047)
      ·
        refine ⟨28898925331504904103978071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19265950221003269402652047 28898925331504904103978071)
        ·
          refine ⟨43348387997257356155967107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28898925331504904103978071 43348387997257356155967107)
          ·
            refine ⟨65022581995886034233950661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43348387997257356155967107 65022581995886034233950661)
            ·
              refine ⟨12191734124228631418865749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65022581995886034233950661 12191734124228631418865749)
              ·
                refine ⟨142871884268304274439833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12191734124228631418865749 142871884268304274439833)
                ·
                  rfl

theorem cell23_7512534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_7512534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512534 prefixEnd_7512534 := by exact prefixLift 7512534
  have htrace : WordTrace (prefixWord ++ tailWord_7512534) baseStart_7512534 baseEnd_7512534 := by
    simpa [prefixWord, tailWord_7512534, baseEnd_7512534] using wordTrace_append hprefix tailTrace_7512534
  have hstable : (prefixWord ++ tailWord_7512534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512534).length < 2 ^ (prefixWord ++ tailWord_7512534).sum := by decide
  have hdescent : baseEnd_7512534 < baseStart_7512534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512565 : List Nat := [1, 3, 5, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_7512565 : Nat := 118140960795 + 7512565 * 2 ^ 59
def prefixEnd_7512565 : Nat := 4983230072969 + 3 ^ 40 * 7512565 * 2
def baseEnd_7512565 : Nat := 3857556793144504788587849

theorem tailTrace_7512565 : CollatzResearch.WordTrace tailWord_7512565 prefixEnd_7512565 3857556793144504788587849 := by
  unfold tailWord_7512565
  simp only [CollatzResearch.WordTrace]
  refine ⟨274005756028267523798763149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182670504018845015865842099 274005756028267523798763149)
  ·
    refine ⟨102752158510600321424536181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274005756028267523798763149 102752158510600321424536181)
    ·
      refine ⟨9633014860368780133550267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102752158510600321424536181 9633014860368780133550267)
      ·
        refine ⟨14449522290553170200325401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9633014860368780133550267 14449522290553170200325401)
        ·
          refine ⟨10837141717914877650244051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14449522290553170200325401 10837141717914877650244051)
          ·
            refine ⟨16255712576872316475366077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10837141717914877650244051 16255712576872316475366077)
            ·
              refine ⟨6095892216327118678262279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16255712576872316475366077 6095892216327118678262279)
              ·
                refine ⟨9143838324490678017393419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6095892216327118678262279 9143838324490678017393419)
                ·
                  refine ⟨13715757486736017026090129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9143838324490678017393419 13715757486736017026090129)
                  ·
                    refine ⟨10286818115052012769567597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13715757486736017026090129 10286818115052012769567597)
                    ·
                      refine ⟨3857556793144504788587849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10286818115052012769567597 3857556793144504788587849)
                      ·
                        rfl

theorem cell23_7512565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_7512565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512565 prefixEnd_7512565 := by exact prefixLift 7512565
  have htrace : WordTrace (prefixWord ++ tailWord_7512565) baseStart_7512565 baseEnd_7512565 := by
    simpa [prefixWord, tailWord_7512565, baseEnd_7512565] using wordTrace_append hprefix tailTrace_7512565
  have hstable : (prefixWord ++ tailWord_7512565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512565).length < 2 ^ (prefixWord ++ tailWord_7512565).sum := by decide
  have hdescent : baseEnd_7512565 < baseStart_7512565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512584 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 5, 4, 2]
def baseStart_7512584 : Nat := 118140960795 + 7512584 * 2 ^ 59
def prefixEnd_7512584 : Nat := 4983230072969 + 3 ^ 40 * 7512584 * 2
def baseEnd_7512584 : Nat := 3857566549276940214250261

theorem tailTrace_7512584 : CollatzResearch.WordTrace tailWord_7512584 prefixEnd_7512584 3857566549276940214250261 := by
  unfold tailWord_7512584
  simp only [CollatzResearch.WordTrace]
  refine ⟨137003224507599345021852403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182670966010132460029136537 137003224507599345021852403)
  ·
    refine ⟨205504836761399017532778605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137003224507599345021852403 205504836761399017532778605)
    ·
      refine ⟨77064313785524631574791977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205504836761399017532778605 77064313785524631574791977)
      ·
        refine ⟨57798235339143473681093983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77064313785524631574791977 57798235339143473681093983)
        ·
          refine ⟨86697353008715210521640975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57798235339143473681093983 86697353008715210521640975)
          ·
            refine ⟨130046029513072815782461463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86697353008715210521640975 130046029513072815782461463)
            ·
              refine ⟨195069044269609223673692195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130046029513072815782461463 195069044269609223673692195)
              ·
                refine ⟨292603566404413835510538293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195069044269609223673692195 292603566404413835510538293)
                ·
                  refine ⟨27431584350413797079112965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 292603566404413835510538293 27431584350413797079112965)
                  ·
                    refine ⟨5143422065702586952333681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27431584350413797079112965 5143422065702586952333681)
                    ·
                      refine ⟨3857566549276940214250261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5143422065702586952333681 3857566549276940214250261)
                      ·
                        rfl

theorem cell23_7512584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_7512584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512584 prefixEnd_7512584 := by exact prefixLift 7512584
  have htrace : WordTrace (prefixWord ++ tailWord_7512584) baseStart_7512584 baseEnd_7512584 := by
    simpa [prefixWord, tailWord_7512584, baseEnd_7512584] using wordTrace_append hprefix tailTrace_7512584
  have hstable : (prefixWord ++ tailWord_7512584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512584).length < 2 ^ (prefixWord ++ tailWord_7512584).sum := by decide
  have hdescent : baseEnd_7512584 < baseStart_7512584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512622 : List Nat := [4, 1, 3, 1, 3, 2, 2, 1, 1, 3, 2]
def baseStart_7512622 : Nat := 118140960795 + 7512622 * 2 ^ 59
def prefixEnd_7512622 : Nat := 4983230072969 + 3 ^ 40 * 7512622 * 2
def baseEnd_7512622 : Nat := 3857586061541811065575087

theorem tailTrace_7512622 : CollatzResearch.WordTrace tailWord_7512622 prefixEnd_7512622 3857586061541811065575087 := by
  unfold tailWord_7512622
  simp only [CollatzResearch.WordTrace]
  refine ⟨34250979373632627816698515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182671889992707348355725413 34250979373632627816698515)
  ·
    refine ⟨51376469060448941725047773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34250979373632627816698515 51376469060448941725047773)
    ·
      refine ⟨19266175897668353146892915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51376469060448941725047773 19266175897668353146892915)
      ·
        refine ⟨28899263846502529720339373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19266175897668353146892915 28899263846502529720339373)
        ·
          refine ⟨10837223942438448645127265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28899263846502529720339373 10837223942438448645127265)
          ·
            refine ⟨8127917956828836483845449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10837223942438448645127265 8127917956828836483845449)
            ·
              refine ⟨6095938467621627362884087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8127917956828836483845449 6095938467621627362884087)
              ·
                refine ⟨9143907701432441044326131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6095938467621627362884087 9143907701432441044326131)
                ·
                  refine ⟨13715861552148661566489197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9143907701432441044326131 13715861552148661566489197)
                  ·
                    refine ⟨5143448082055748087433449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13715861552148661566489197 5143448082055748087433449)
                    ·
                      refine ⟨3857586061541811065575087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5143448082055748087433449 3857586061541811065575087)
                      ·
                        rfl

theorem cell23_7512622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_7512622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512622 prefixEnd_7512622 := by exact prefixLift 7512622
  have htrace : WordTrace (prefixWord ++ tailWord_7512622) baseStart_7512622 baseEnd_7512622 := by
    simpa [prefixWord, tailWord_7512622, baseEnd_7512622] using wordTrace_append hprefix tailTrace_7512622
  have hstable : (prefixWord ++ tailWord_7512622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512622).length < 2 ^ (prefixWord ++ tailWord_7512622).sum := by decide
  have hdescent : baseEnd_7512622 < baseStart_7512622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512624 : List Nat := [2, 1, 1, 1, 2, 3, 3, 5, 5]
def baseStart_7512624 : Nat := 118140960795 + 7512624 * 2 ^ 59
def prefixEnd_7512624 : Nat := 4983230072969 + 3 ^ 40 * 7512624 * 2
def baseEnd_7512624 : Nat := 428620787611457784194453

theorem tailTrace_7512624 : CollatzResearch.WordTrace tailWord_7512624 prefixEnd_7512624 428620787611457784194453 := by
  unfold tailWord_7512624
  simp only [CollatzResearch.WordTrace]
  refine ⟨137003953967526888437580463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182671938623369184583440617 137003953967526888437580463)
  ·
    refine ⟨205505930951290332656370695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137003953967526888437580463 205505930951290332656370695)
    ·
      refine ⟨308258896426935498984556043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205505930951290332656370695 308258896426935498984556043)
      ·
        refine ⟨462388344640403248476834065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308258896426935498984556043 462388344640403248476834065)
        ·
          refine ⟨346791258480302436357625549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462388344640403248476834065 346791258480302436357625549)
          ·
            refine ⟨130046721930113413634109581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346791258480302436357625549 130046721930113413634109581)
            ·
              refine ⟨48767520723792530112791093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130046721930113413634109581 48767520723792530112791093)
              ·
                refine ⟨4571955067855549698074165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48767520723792530112791093 4571955067855549698074165)
                ·
                  refine ⟨428620787611457784194453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4571955067855549698074165 428620787611457784194453)
                  ·
                    rfl

theorem cell23_7512624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 5].length) (baseStart_7512624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512624 prefixEnd_7512624 := by exact prefixLift 7512624
  have htrace : WordTrace (prefixWord ++ tailWord_7512624) baseStart_7512624 baseEnd_7512624 := by
    simpa [prefixWord, tailWord_7512624, baseEnd_7512624] using wordTrace_append hprefix tailTrace_7512624
  have hstable : (prefixWord ++ tailWord_7512624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512624).length < 2 ^ (prefixWord ++ tailWord_7512624).sum := by decide
  have hdescent : baseEnd_7512624 < baseStart_7512624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512634 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3]
def baseStart_7512634 : Nat := 118140960795 + 7512634 * 2 ^ 59
def prefixEnd_7512634 : Nat := 4983230072969 + 3 ^ 40 * 7512634 * 2
def baseEnd_7512634 : Nat := 3857592223309665018625031

theorem tailTrace_7512634 : CollatzResearch.WordTrace tailWord_7512634 prefixEnd_7512634 3857592223309665018625031 := by
  unfold tailWord_7512634
  simp only [CollatzResearch.WordTrace]
  refine ⟨68502068166254387145756239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182672181776678365722016637 68502068166254387145756239)
  ·
    refine ⟨102753102249381580718634359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68502068166254387145756239 102753102249381580718634359)
    ·
      refine ⟨154129653374072371077951539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102753102249381580718634359 154129653374072371077951539)
      ·
        refine ⟨231194480061108556616927309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154129653374072371077951539 231194480061108556616927309)
        ·
          refine ⟨86697930022915708731347741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231194480061108556616927309 86697930022915708731347741)
          ·
            refine ⟨32511723758593390774255403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86697930022915708731347741 32511723758593390774255403)
            ·
              refine ⟨48767585637890086161383105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32511723758593390774255403 48767585637890086161383105)
              ·
                refine ⟨36575689228417564621037329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48767585637890086161383105 36575689228417564621037329)
                ·
                  refine ⟨27431766921313173465777997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36575689228417564621037329 27431766921313173465777997)
                  ·
                    refine ⟨10286912595492440049666749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27431766921313173465777997 10286912595492440049666749)
                    ·
                      refine ⟨3857592223309665018625031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10286912595492440049666749 3857592223309665018625031)
                      ·
                        rfl

theorem cell23_7512634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3].length) (baseStart_7512634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512634 prefixEnd_7512634 := by exact prefixLift 7512634
  have htrace : WordTrace (prefixWord ++ tailWord_7512634) baseStart_7512634 baseEnd_7512634 := by
    simpa [prefixWord, tailWord_7512634, baseEnd_7512634] using wordTrace_append hprefix tailTrace_7512634
  have hstable : (prefixWord ++ tailWord_7512634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512634).length < 2 ^ (prefixWord ++ tailWord_7512634).sum := by decide
  have hdescent : baseEnd_7512634 < baseStart_7512634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512641 : List Nat := [1, 2, 5, 1, 1, 2, 2, 4, 5]
def baseStart_7512641 : Nat := 118140960795 + 7512641 * 2 ^ 59
def prefixEnd_7512641 : Nat := 4983230072969 + 3 ^ 40 * 7512641 * 2
def baseEnd_7512641 : Nat := 428621757519360721248611

theorem tailTrace_7512641 : CollatzResearch.WordTrace tailWord_7512641 prefixEnd_7512641 428621757519360721248611 := by
  unfold tailWord_7512641
  simp only [CollatzResearch.WordTrace]
  refine ⟨274008527975992188778529777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182672351983994792519019851 274008527975992188778529777)
  ·
    refine ⟨205506395981994141583897333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274008527975992188778529777 205506395981994141583897333)
    ·
      refine ⟨19266224623311950773490375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205506395981994141583897333 19266224623311950773490375)
      ·
        refine ⟨28899336934967926160235563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19266224623311950773490375 28899336934967926160235563)
        ·
          refine ⟨43349005402451889240353345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28899336934967926160235563 43349005402451889240353345)
          ·
            refine ⟨32511754051838916930265009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43349005402451889240353345 32511754051838916930265009)
            ·
              refine ⟨24383815538879187697698757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32511754051838916930265009 24383815538879187697698757)
              ·
                refine ⟨4571965413539847693318517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24383815538879187697698757 4571965413539847693318517)
                ·
                  refine ⟨428621757519360721248611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4571965413539847693318517 428621757519360721248611)
                  ·
                    rfl

theorem cell23_7512641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 5].length) (baseStart_7512641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512641 prefixEnd_7512641 := by exact prefixLift 7512641
  have htrace : WordTrace (prefixWord ++ tailWord_7512641) baseStart_7512641 baseEnd_7512641 := by
    simpa [prefixWord, tailWord_7512641, baseEnd_7512641] using wordTrace_append hprefix tailTrace_7512641
  have hstable : (prefixWord ++ tailWord_7512641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512641).length < 2 ^ (prefixWord ++ tailWord_7512641).sum := by decide
  have hdescent : baseEnd_7512641 < baseStart_7512641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512684 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 5, 4]
def baseStart_7512684 : Nat := 118140960795 + 7512684 * 2 ^ 59
def prefixEnd_7512684 : Nat := 4983230072969 + 3 ^ 40 * 7512684 * 2
def baseEnd_7512684 : Nat := 1285872632447463274333267

theorem tailTrace_7512684 : CollatzResearch.WordTrace tailWord_7512684 prefixEnd_7512684 1285872632447463274333267 := by
  unfold tailWord_7512684
  simp only [CollatzResearch.WordTrace]
  refine ⟨137005048157418203561172553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182673397543224271414896737 137005048157418203561172553)
  ·
    refine ⟨102753786118063652670879415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137005048157418203561172553 102753786118063652670879415)
    ·
      refine ⟨154130679177095479006319123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102753786118063652670879415 154130679177095479006319123)
      ·
        refine ⟨231196018765643218509478685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154130679177095479006319123 231196018765643218509478685)
        ·
          refine ⟨86698507037116206941054507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231196018765643218509478685 86698507037116206941054507)
          ·
            refine ⟨130047760555674310411581761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86698507037116206941054507 130047760555674310411581761)
            ·
              refine ⟨97535820416755732808686321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130047760555674310411581761 97535820416755732808686321)
              ·
                refine ⟨73151865312566799606514741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97535820416755732808686321 73151865312566799606514741)
                ·
                  refine ⟨6857987373053137463110757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73151865312566799606514741 6857987373053137463110757)
                  ·
                    refine ⟨1285872632447463274333267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6857987373053137463110757 1285872632447463274333267)
                    ·
                      rfl

theorem cell23_7512684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 4].length) (baseStart_7512684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512684 prefixEnd_7512684 := by exact prefixLift 7512684
  have htrace : WordTrace (prefixWord ++ tailWord_7512684) baseStart_7512684 baseEnd_7512684 := by
    simpa [prefixWord, tailWord_7512684, baseEnd_7512684] using wordTrace_append hprefix tailTrace_7512684
  have hstable : (prefixWord ++ tailWord_7512684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512684).length < 2 ^ (prefixWord ++ tailWord_7512684).sum := by decide
  have hdescent : baseEnd_7512684 < baseStart_7512684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512687 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 6]
def baseStart_7512687 : Nat := 118140960795 + 7512687 * 2 ^ 59
def prefixEnd_7512687 : Nat := 4983230072969 + 3 ^ 40 * 7512687 * 2
def baseEnd_7512687 : Nat := 3857619437784353311262287

theorem tailTrace_7512687 : CollatzResearch.WordTrace tailWord_7512687 prefixEnd_7512687 3857619437784353311262287 := by
  unfold tailWord_7512687
  simp only [CollatzResearch.WordTrace]
  refine ⟨274010205733825538634704315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182673470489217025756469543 274010205733825538634704315)
  ·
    refine ⟨411015308600738307952056473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274010205733825538634704315 411015308600738307952056473)
    ·
      refine ⟨308261481450553730964042355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411015308600738307952056473 308261481450553730964042355)
      ·
        refine ⟨462392222175830596446063533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308261481450553730964042355 462392222175830596446063533)
        ·
          refine ⟨173397083315936473667273825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 462392222175830596446063533 173397083315936473667273825)
          ·
            refine ⟨130047812486952355250455369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173397083315936473667273825 130047812486952355250455369)
            ·
              refine ⟨97535859365214266437841527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130047812486952355250455369 97535859365214266437841527)
              ·
                refine ⟨146303789047821399656762291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97535859365214266437841527 146303789047821399656762291)
                ·
                  refine ⟨219455683571732099485143437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146303789047821399656762291 219455683571732099485143437)
                  ·
                    refine ⟨82295881339399537306928789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 219455683571732099485143437 82295881339399537306928789)
                    ·
                      refine ⟨3857619437784353311262287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82295881339399537306928789 3857619437784353311262287)
                      ·
                        rfl

theorem cell23_7512687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_7512687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512687 prefixEnd_7512687 := by exact prefixLift 7512687
  have htrace : WordTrace (prefixWord ++ tailWord_7512687) baseStart_7512687 baseEnd_7512687 := by
    simpa [prefixWord, tailWord_7512687, baseEnd_7512687] using wordTrace_append hprefix tailTrace_7512687
  have hstable : (prefixWord ++ tailWord_7512687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512687).length < 2 ^ (prefixWord ++ tailWord_7512687).sum := by decide
  have hdescent : baseEnd_7512687 < baseStart_7512687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512804 : List Nat := [2, 3, 1, 1, 1, 5, 10]
def baseStart_7512804 : Nat := 118140960795 + 7512804 * 2 ^ 59
def prefixEnd_7512804 : Nat := 4983230072969 + 3 ^ 40 * 7512804 * 2
def baseEnd_7512804 : Nat := 47625673024949745104929

theorem tailTrace_7512804 : CollatzResearch.WordTrace tailWord_7512804 prefixEnd_7512804 47625673024949745104929 := by
  unfold tailWord_7512804
  simp only [CollatzResearch.WordTrace]
  refine ⟨137007236537200833808356733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182676315382934445077808977 137007236537200833808356733)
  ·
    refine ⟨51377713701450312678133775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137007236537200833808356733 51377713701450312678133775)
    ·
      refine ⟨77066570552175469017200663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51377713701450312678133775 77066570552175469017200663)
      ·
        refine ⟨115599855828263203525800995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77066570552175469017200663 115599855828263203525800995)
        ·
          refine ⟨173399783742394805288701493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115599855828263203525800995 173399783742394805288701493)
          ·
            refine ⟨16256229725849512995815765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173399783742394805288701493 16256229725849512995815765)
            ·
              refine ⟨47625673024949745104929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16256229725849512995815765 47625673024949745104929)
              ·
                rfl

theorem cell23_7512804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 10].length) (baseStart_7512804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512804 prefixEnd_7512804 := by exact prefixLift 7512804
  have htrace : WordTrace (prefixWord ++ tailWord_7512804) baseStart_7512804 baseEnd_7512804 := by
    simpa [prefixWord, tailWord_7512804, baseEnd_7512804] using wordTrace_append hprefix tailTrace_7512804
  have hstable : (prefixWord ++ tailWord_7512804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512804).length < 2 ^ (prefixWord ++ tailWord_7512804).sum := by decide
  have hdescent : baseEnd_7512804 < baseStart_7512804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512808 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 4, 4]
def baseStart_7512808 : Nat := 118140960795 + 7512808 * 2 ^ 59
def prefixEnd_7512808 : Nat := 4983230072969 + 3 ^ 40 * 7512808 * 2
def baseEnd_7512808 : Nat := 1285893856314515779283077

theorem tailTrace_7512808 : CollatzResearch.WordTrace tailWord_7512808 prefixEnd_7512808 1285893856314515779283077 := by
  unfold tailWord_7512808
  simp only [CollatzResearch.WordTrace]
  refine ⟨137007309483193588149929539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182676412644258117533239385 137007309483193588149929539)
  ·
    refine ⟨205510964224790382224894309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137007309483193588149929539 205510964224790382224894309)
    ·
      refine ⟨38533305792148196667167683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205510964224790382224894309 38533305792148196667167683)
      ·
        refine ⟨57799958688222295000751525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38533305792148196667167683 57799958688222295000751525)
        ·
          refine ⟨10837492254041680312640911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57799958688222295000751525 10837492254041680312640911)
          ·
            refine ⟨16256238381062520468961367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10837492254041680312640911 16256238381062520468961367)
            ·
              refine ⟨24384357571593780703442051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16256238381062520468961367 24384357571593780703442051)
              ·
                refine ⟨36576536357390671055163077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24384357571593780703442051 36576536357390671055163077)
                ·
                  refine ⟨6858100567010750822843077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36576536357390671055163077 6858100567010750822843077)
                  ·
                    refine ⟨1285893856314515779283077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6858100567010750822843077 1285893856314515779283077)
                    ·
                      rfl

theorem cell23_7512808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_7512808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512808 prefixEnd_7512808 := by exact prefixLift 7512808
  have htrace : WordTrace (prefixWord ++ tailWord_7512808) baseStart_7512808 baseEnd_7512808 := by
    simpa [prefixWord, tailWord_7512808, baseEnd_7512808] using wordTrace_append hprefix tailTrace_7512808
  have hstable : (prefixWord ++ tailWord_7512808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512808).length < 2 ^ (prefixWord ++ tailWord_7512808).sum := by decide
  have hdescent : baseEnd_7512808 < baseStart_7512808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512815 : List Nat := [1, 1, 2, 1, 5, 3, 2, 1, 3, 2, 2]
def baseStart_7512815 : Nat := 118140960795 + 7512815 * 2 ^ 59
def prefixEnd_7512815 : Nat := 4983230072969 + 3 ^ 40 * 7512815 * 2
def baseEnd_7512815 : Nat := 3857685163308128810461699

theorem tailTrace_7512815 : CollatzResearch.WordTrace tailWord_7512815 prefixEnd_7512815 3857685163308128810461699 := by
  unfold tailWord_7512815
  simp only [CollatzResearch.WordTrace]
  refine ⟨274014874277361816495363899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182676582851574544330242599 274014874277361816495363899)
  ·
    refine ⟨411022311416042724743045849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274014874277361816495363899 411022311416042724743045849)
    ·
      refine ⟨308266733562032043557284387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411022311416042724743045849 308266733562032043557284387)
      ·
        refine ⟨462400100343048065335926581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308266733562032043557284387 462400100343048065335926581)
        ·
          refine ⟨43350009407160756125243117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 462400100343048065335926581 43350009407160756125243117)
          ·
            refine ⟨16256253527685283546966169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43350009407160756125243117 16256253527685283546966169)
            ·
              refine ⟨12192190145763962660224627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16256253527685283546966169 12192190145763962660224627)
              ·
                refine ⟨18288285218645943990336941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12192190145763962660224627 18288285218645943990336941)
                ·
                  refine ⟨6858106956992228996376353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18288285218645943990336941 6858106956992228996376353)
                  ·
                    refine ⟨5143580217744171747282265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6858106956992228996376353 5143580217744171747282265)
                    ·
                      refine ⟨3857685163308128810461699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5143580217744171747282265 3857685163308128810461699)
                      ·
                        rfl

theorem cell23_7512815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 2, 2].length) (baseStart_7512815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512815 prefixEnd_7512815 := by exact prefixLift 7512815
  have htrace : WordTrace (prefixWord ++ tailWord_7512815) baseStart_7512815 baseEnd_7512815 := by
    simpa [prefixWord, tailWord_7512815, baseEnd_7512815] using wordTrace_append hprefix tailTrace_7512815
  have hstable : (prefixWord ++ tailWord_7512815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512815).length < 2 ^ (prefixWord ++ tailWord_7512815).sum := by decide
  have hdescent : baseEnd_7512815 < baseStart_7512815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512828 : List Nat := [2, 2, 2, 1, 3, 4, 1, 1, 1, 2, 4]
def baseStart_7512828 : Nat := 118140960795 + 7512828 * 2 ^ 59
def prefixEnd_7512828 : Nat := 4983230072969 + 3 ^ 40 * 7512828 * 2
def baseEnd_7512828 : Nat := 3857691838556637259599139

theorem tailTrace_7512828 : CollatzResearch.WordTrace tailWord_7512828 prefixEnd_7512828 3857691838556637259599139 := by
  unfold tailWord_7512828
  simp only [CollatzResearch.WordTrace]
  refine ⟨137007674213157359857793569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182676898950876479810391425 137007674213157359857793569)
  ·
    refine ⟨102755755659868019893345177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137007674213157359857793569 102755755659868019893345177)
    ·
      refine ⟨77066816744901014920008883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102755755659868019893345177 77066816744901014920008883)
      ·
        refine ⟨115600225117351522380013325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77066816744901014920008883 115600225117351522380013325)
        ·
          refine ⟨43350084419006820892504997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115600225117351522380013325 43350084419006820892504997)
          ·
            refine ⟨8128140828563778917344687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43350084419006820892504997 8128140828563778917344687)
            ·
              refine ⟨12192211242845668376017031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8128140828563778917344687 12192211242845668376017031)
              ·
                refine ⟨18288316864268502564025547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12192211242845668376017031 18288316864268502564025547)
                ·
                  refine ⟨27432475296402753846038321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18288316864268502564025547 27432475296402753846038321)
                  ·
                    refine ⟨20574356472302065384528741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27432475296402753846038321 20574356472302065384528741)
                    ·
                      refine ⟨3857691838556637259599139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20574356472302065384528741 3857691838556637259599139)
                      ·
                        rfl

theorem cell23_7512828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_7512828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512828 prefixEnd_7512828 := by exact prefixLift 7512828
  have htrace : WordTrace (prefixWord ++ tailWord_7512828) baseStart_7512828 baseEnd_7512828 := by
    simpa [prefixWord, tailWord_7512828, baseEnd_7512828] using wordTrace_append hprefix tailTrace_7512828
  have hstable : (prefixWord ++ tailWord_7512828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512828).length < 2 ^ (prefixWord ++ tailWord_7512828).sum := by decide
  have hdescent : baseEnd_7512828 < baseStart_7512828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512888 : List Nat := [2, 1, 2, 1, 3, 2, 2, 3, 1, 4, 2]
def baseStart_7512888 : Nat := 118140960795 + 7512888 * 2 ^ 59
def prefixEnd_7512888 : Nat := 4983230072969 + 3 ^ 40 * 7512888 * 2
def baseEnd_7512888 : Nat := 3857722647395907024848863

theorem tailTrace_7512888 : CollatzResearch.WordTrace tailWord_7512888 prefixEnd_7512888 3857722647395907024848863 := by
  unfold tailWord_7512888
  simp only [CollatzResearch.WordTrace]
  refine ⟨137008768403048674981385659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182678357870731566641847545 137008768403048674981385659)
  ·
    refine ⟨205513152604573012472078489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137008768403048674981385659 205513152604573012472078489)
    ·
      refine ⟨154134864453429759354058867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205513152604573012472078489 154134864453429759354058867)
      ·
        refine ⟨231202296680144639031088301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154134864453429759354058867 231202296680144639031088301)
        ·
          refine ⟨86700861255054239636658113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231202296680144639031088301 86700861255054239636658113)
          ·
            refine ⟨65025645941290679727493585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86700861255054239636658113 65025645941290679727493585)
            ·
              refine ⟨48769234455968009795620189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65025645941290679727493585 48769234455968009795620189)
              ·
                refine ⟨18288462920988003673357571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48769234455968009795620189 18288462920988003673357571)
                ·
                  refine ⟨27432694381482005510036357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18288462920988003673357571 27432694381482005510036357)
                  ·
                    refine ⟨5143630196527876033131817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27432694381482005510036357 5143630196527876033131817)
                    ·
                      refine ⟨3857722647395907024848863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5143630196527876033131817 3857722647395907024848863)
                      ·
                        rfl

theorem cell23_7512888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 1, 4, 2].length) (baseStart_7512888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512888 prefixEnd_7512888 := by exact prefixLift 7512888
  have htrace : WordTrace (prefixWord ++ tailWord_7512888) baseStart_7512888 baseEnd_7512888 := by
    simpa [prefixWord, tailWord_7512888, baseEnd_7512888] using wordTrace_append hprefix tailTrace_7512888
  have hstable : (prefixWord ++ tailWord_7512888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512888).length < 2 ^ (prefixWord ++ tailWord_7512888).sum := by decide
  have hdescent : baseEnd_7512888 < baseStart_7512888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512922 : List Nat := [3, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2]
def baseStart_7512922 : Nat := 118140960795 + 7512922 * 2 ^ 59
def prefixEnd_7512922 : Nat := 4983230072969 + 3 ^ 40 * 7512922 * 2
def baseEnd_7512922 : Nat := 3857740105738159891823707

theorem tailTrace_7512922 : CollatzResearch.WordTrace tailWord_7512922 prefixEnd_7512922 3857740105738159891823707 := by
  unfold tailWord_7512922
  simp only [CollatzResearch.WordTrace]
  refine ⟨68504694221993543442377255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182679184591982782513006013 68504694221993543442377255)
  ·
    refine ⟨102757041332990315163565883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68504694221993543442377255 102757041332990315163565883)
    ·
      refine ⟨154135561999485472745348825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102757041332990315163565883 154135561999485472745348825)
      ·
        refine ⟨115601671499614104559011619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154135561999485472745348825 115601671499614104559011619)
        ·
          refine ⟨173402507249421156838517429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115601671499614104559011619 173402507249421156838517429)
          ·
            refine ⟨16256485054633233453611009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173402507249421156838517429 16256485054633233453611009)
            ·
              refine ⟨12192363790974925090208257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16256485054633233453611009 12192363790974925090208257)
              ·
                refine ⟨9144272843231193817656193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12192363790974925090208257 9144272843231193817656193)
                ·
                  refine ⟨6858204632423395363242145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9144272843231193817656193 6858204632423395363242145)
                  ·
                    refine ⟨5143653474317546522431609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6858204632423395363242145 5143653474317546522431609)
                    ·
                      refine ⟨3857740105738159891823707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5143653474317546522431609 3857740105738159891823707)
                      ·
                        rfl

theorem cell23_7512922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_7512922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512922 prefixEnd_7512922 := by exact prefixLift 7512922
  have htrace : WordTrace (prefixWord ++ tailWord_7512922) baseStart_7512922 baseEnd_7512922 := by
    simpa [prefixWord, tailWord_7512922, baseEnd_7512922] using wordTrace_append hprefix tailTrace_7512922
  have hstable : (prefixWord ++ tailWord_7512922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512922).length < 2 ^ (prefixWord ++ tailWord_7512922).sum := by decide
  have hdescent : baseEnd_7512922 < baseStart_7512922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512928 : List Nat := [2, 1, 1, 3, 3, 1, 3, 4, 5]
def baseStart_7512928 : Nat := 118140960795 + 7512928 * 2 ^ 59
def prefixEnd_7512928 : Nat := 4983230072969 + 3 ^ 40 * 7512928 * 2
def baseEnd_7512928 : Nat := 428638131846898540927631

theorem tailTrace_7512928 : CollatzResearch.WordTrace tailWord_7512928 prefixEnd_7512928 428638131846898540927631 := by
  unfold tailWord_7512928
  simp only [CollatzResearch.WordTrace]
  refine ⟨137009497862976218397113719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182679330483968291196151625 137009497862976218397113719)
  ·
    refine ⟨205514246794464327595670579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137009497862976218397113719 205514246794464327595670579)
    ·
      refine ⟨308271370191696491393505869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205514246794464327595670579 308271370191696491393505869)
      ·
        refine ⟨115601763821886184272564701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308271370191696491393505869 115601763821886184272564701)
        ·
          refine ⟨43350661433207319102211763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115601763821886184272564701 43350661433207319102211763)
          ·
            refine ⟨65025992149810978653317645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43350661433207319102211763 65025992149810978653317645)
            ·
              refine ⟨24384747056179116994994117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65025992149810978653317645 24384747056179116994994117)
              ·
                refine ⟨4572140073033584436561397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24384747056179116994994117 4572140073033584436561397)
                ·
                  refine ⟨428638131846898540927631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4572140073033584436561397 428638131846898540927631)
                  ·
                    rfl

theorem cell23_7512928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 5].length) (baseStart_7512928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512928 prefixEnd_7512928 := by exact prefixLift 7512928
  have htrace : WordTrace (prefixWord ++ tailWord_7512928) baseStart_7512928 baseEnd_7512928 := by
    simpa [prefixWord, tailWord_7512928, baseEnd_7512928] using wordTrace_append hprefix tailTrace_7512928
  have hstable : (prefixWord ++ tailWord_7512928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512928).length < 2 ^ (prefixWord ++ tailWord_7512928).sum := by decide
  have hdescent : baseEnd_7512928 < baseStart_7512928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7512941 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_7512941 : Nat := 118140960795 + 7512941 * 2 ^ 59
def prefixEnd_7512941 : Nat := 4983230072969 + 3 ^ 40 * 7512941 * 2
def baseEnd_7512941 : Nat := 1285916620623531772495373

theorem tailTrace_7512941 : CollatzResearch.WordTrace tailWord_7512941 prefixEnd_7512941 1285916620623531772495373 := by
  unfold tailWord_7512941
  simp only [CollatzResearch.WordTrace]
  refine ⟨274019469874905340014450677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182679646583270226676300451 274019469874905340014450677)
  ·
    refine ⟨25689325300772375626354751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 274019469874905340014450677 25689325300772375626354751)
    ·
      refine ⟨38533987951158563439532127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25689325300772375626354751 38533987951158563439532127)
      ·
        refine ⟨57800981926737845159298191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38533987951158563439532127 57800981926737845159298191)
        ·
          refine ⟨86701472890106767738947287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57800981926737845159298191 86701472890106767738947287)
          ·
            refine ⟨130052209335160151608420931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86701472890106767738947287 130052209335160151608420931)
            ·
              refine ⟨195078314002740227412631397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130052209335160151608420931 195078314002740227412631397)
              ·
                refine ⟨36577183875513792639868387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195078314002740227412631397 36577183875513792639868387)
                ·
                  refine ⟨54865775813270688959802581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36577183875513792639868387 54865775813270688959802581)
                  ·
                    refine ⟨1285916620623531772495373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54865775813270688959802581 1285916620623531772495373)
                    ·
                      rfl

theorem cell23_7512941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_7512941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7512941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7512941 prefixEnd_7512941 := by exact prefixLift 7512941
  have htrace : WordTrace (prefixWord ++ tailWord_7512941) baseStart_7512941 baseEnd_7512941 := by
    simpa [prefixWord, tailWord_7512941, baseEnd_7512941] using wordTrace_append hprefix tailTrace_7512941
  have hstable : (prefixWord ++ tailWord_7512941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7512941).length < 2 ^ (prefixWord ++ tailWord_7512941).sum := by decide
  have hdescent : baseEnd_7512941 < baseStart_7512941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7512941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513090 : List Nat := [3, 4, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_7513090 : Nat := 118140960795 + 7513090 * 2 ^ 59
def prefixEnd_7513090 : Nat := 4983230072969 + 3 ^ 40 * 7513090 * 2
def baseEnd_7513090 : Nat := 1285942123496038411507645

theorem tailTrace_7513090 : CollatzResearch.WordTrace tailWord_7513090 prefixEnd_7513090 1285942123496038411507645 := by
  unfold tailWord_7513090
  simp only [CollatzResearch.WordTrace]
  refine ⟨68506226087841384615406181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182683269567577025641083149 68506226087841384615406181)
  ·
    refine ⟨12844917391470259615388659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68506226087841384615406181 12844917391470259615388659)
    ·
      refine ⟨19267376087205389423082989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12844917391470259615388659 19267376087205389423082989)
      ·
        refine ⟨7225266032702021033656121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19267376087205389423082989 7225266032702021033656121)
        ·
          refine ⟨5418949524526515775242091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7225266032702021033656121 5418949524526515775242091)
          ·
            refine ⟨8128424286789773662863137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5418949524526515775242091 8128424286789773662863137)
            ·
              refine ⟨6096318215092330247147353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8128424286789773662863137 6096318215092330247147353)
              ·
                refine ⟨4572238661319247685360515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6096318215092330247147353 4572238661319247685360515)
                ·
                  refine ⟨6858357991978871528040773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4572238661319247685360515 6858357991978871528040773)
                  ·
                    refine ⟨1285942123496038411507645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6858357991978871528040773 1285942123496038411507645)
                    ·
                      rfl

theorem cell23_7513090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_7513090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513090 prefixEnd_7513090 := by exact prefixLift 7513090
  have htrace : WordTrace (prefixWord ++ tailWord_7513090) baseStart_7513090 baseEnd_7513090 := by
    simpa [prefixWord, tailWord_7513090, baseEnd_7513090] using wordTrace_append hprefix tailTrace_7513090
  have hstable : (prefixWord ++ tailWord_7513090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513090).length < 2 ^ (prefixWord ++ tailWord_7513090).sum := by decide
  have hdescent : baseEnd_7513090 < baseStart_7513090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513096 : List Nat := [2, 1, 3, 2, 1, 5, 2, 2, 1, 1, 3]
def baseStart_7513096 : Nat := 118140960795 + 7513096 * 2 ^ 59
def prefixEnd_7513096 : Nat := 4983230072969 + 3 ^ 40 * 7513096 * 2
def baseEnd_7513096 : Nat := 3857829451372042211047907

theorem tailTrace_7513096 : CollatzResearch.WordTrace tailWord_7513096 prefixEnd_7513096 3857829451372042211047907 := by
  unfold tailWord_7513096
  simp only [CollatzResearch.WordTrace]
  refine ⟨137012561594671900743171571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182683415459562534324228761 137012561594671900743171571)
  ·
    refine ⟨205518842392007851114757357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137012561594671900743171571 205518842392007851114757357)
    ·
      refine ⟨77069565897002944168034009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205518842392007851114757357 77069565897002944168034009)
      ·
        refine ⟨57802174422752208126025507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77069565897002944168034009 57802174422752208126025507)
        ·
          refine ⟨86703261634128312189038261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57802174422752208126025507 86703261634128312189038261)
          ·
            refine ⟨8128430778199529267722337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86703261634128312189038261 8128430778199529267722337)
            ·
              refine ⟨6096323083649646950791753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8128430778199529267722337 6096323083649646950791753)
              ·
                refine ⟨4572242312737235213093815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6096323083649646950791753 4572242312737235213093815)
                ·
                  refine ⟨6858363469105852819640723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4572242312737235213093815 6858363469105852819640723)
                  ·
                    refine ⟨10287545203658779229461085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6858363469105852819640723 10287545203658779229461085)
                    ·
                      refine ⟨3857829451372042211047907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10287545203658779229461085 3857829451372042211047907)
                      ·
                        rfl

theorem cell23_7513096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_7513096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513096 prefixEnd_7513096 := by exact prefixLift 7513096
  have htrace : WordTrace (prefixWord ++ tailWord_7513096) baseStart_7513096 baseEnd_7513096 := by
    simpa [prefixWord, tailWord_7513096, baseEnd_7513096] using wordTrace_append hprefix tailTrace_7513096
  have hstable : (prefixWord ++ tailWord_7513096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513096).length < 2 ^ (prefixWord ++ tailWord_7513096).sum := by decide
  have hdescent : baseEnd_7513096 < baseStart_7513096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513228 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 3, 7]
def baseStart_7513228 : Nat := 118140960795 + 7513228 * 2 ^ 59
def prefixEnd_7513228 : Nat := 4983230072969 + 3 ^ 40 * 7513228 * 2
def baseEnd_7513228 : Nat := 1285965743606145231532433

theorem tailTrace_7513228 : CollatzResearch.WordTrace tailWord_7513228 prefixEnd_7513228 1285965743606145231532433 := by
  unfold tailWord_7513228
  simp only [CollatzResearch.WordTrace]
  refine ⟨137014968812432794015074169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182686625083243725353432225 137014968812432794015074169)
  ·
    refine ⟨102761226609324595511305627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137014968812432794015074169 102761226609324595511305627)
    ·
      refine ⟨154141839913986893266958441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102761226609324595511305627 154141839913986893266958441)
      ·
        refine ⟨115606379935490169950218831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154141839913986893266958441 115606379935490169950218831)
        ·
          refine ⟨173409569903235254925328247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115606379935490169950218831 173409569903235254925328247)
          ·
            refine ⟨260114354854852882387992371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173409569903235254925328247 260114354854852882387992371)
            ·
              refine ⟨390171532282279323581988557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260114354854852882387992371 390171532282279323581988557)
              ·
                refine ⟨146314324605854746343245709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 390171532282279323581988557 146314324605854746343245709)
                ·
                  refine ⟨54867871727195529878717141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146314324605854746343245709 54867871727195529878717141)
                  ·
                    refine ⟨1285965743606145231532433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54867871727195529878717141 1285965743606145231532433)
                    ·
                      rfl

theorem cell23_7513228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_7513228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513228 prefixEnd_7513228 := by exact prefixLift 7513228
  have htrace : WordTrace (prefixWord ++ tailWord_7513228) baseStart_7513228 baseEnd_7513228 := by
    simpa [prefixWord, tailWord_7513228, baseEnd_7513228] using wordTrace_append hprefix tailTrace_7513228
  have hstable : (prefixWord ++ tailWord_7513228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513228).length < 2 ^ (prefixWord ++ tailWord_7513228).sum := by decide
  have hdescent : baseEnd_7513228 < baseStart_7513228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513285 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 1, 4, 3]
def baseStart_7513285 : Nat := 118140960795 + 7513285 * 2 ^ 59
def prefixEnd_7513285 : Nat := 4983230072969 + 3 ^ 40 * 7513285 * 2
def baseEnd_7513285 : Nat := 3857926499215741971584537

theorem tailTrace_7513285 : CollatzResearch.WordTrace tailWord_7513285 prefixEnd_7513285 3857926499215741971584537 := by
  unfold tailWord_7513285
  simp only [CollatzResearch.WordTrace]
  refine ⟨274032016585659086764973309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182688011057106057843315539 274032016585659086764973309)
  ·
    refine ⟨102762006219622157536864991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274032016585659086764973309 102762006219622157536864991)
    ·
      refine ⟨154143009329433236305297487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102762006219622157536864991 154143009329433236305297487)
      ·
        refine ⟨231214513994149854457946231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154143009329433236305297487 231214513994149854457946231)
        ·
          refine ⟨346821770991224781686919347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231214513994149854457946231 346821770991224781686919347)
          ·
            refine ⟨520232656486837172530379021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346821770991224781686919347 520232656486837172530379021)
            ·
              refine ⟨195087246182563939698892133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 520232656486837172530379021 195087246182563939698892133)
              ·
                refine ⟨36578858659230738693542275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195087246182563939698892133 36578858659230738693542275)
                ·
                  refine ⟨54868287988846108040313413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36578858659230738693542275 54868287988846108040313413)
                  ·
                    refine ⟨10287803997908645257558765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54868287988846108040313413 10287803997908645257558765)
                    ·
                      refine ⟨3857926499215741971584537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10287803997908645257558765 3857926499215741971584537)
                      ·
                        rfl

theorem cell23_7513285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 4, 3].length) (baseStart_7513285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513285 prefixEnd_7513285 := by exact prefixLift 7513285
  have htrace : WordTrace (prefixWord ++ tailWord_7513285) baseStart_7513285 baseEnd_7513285 := by
    simpa [prefixWord, tailWord_7513285, baseEnd_7513285] using wordTrace_append hprefix tailTrace_7513285
  have hstable : (prefixWord ++ tailWord_7513285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513285).length < 2 ^ (prefixWord ++ tailWord_7513285).sum := by decide
  have hdescent : baseEnd_7513285 < baseStart_7513285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513322 : List Nat := [3, 1, 3, 1, 1, 3, 3, 2, 6]
def baseStart_7513322 : Nat := 118140960795 + 7513322 * 2 ^ 59
def prefixEnd_7513322 : Nat := 4983230072969 + 3 ^ 40 * 7513322 * 2
def baseEnd_7513322 : Nat := 428660610888884258535763

theorem tailTrace_7513322 : CollatzResearch.WordTrace tailWord_7513322 prefixEnd_7513322 428660610888884258535763 := by
  unfold tailWord_7513322
  simp only [CollatzResearch.WordTrace]
  refine ⟨68508341521631260521017555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182688910724350028056046813 68508341521631260521017555)
  ·
    refine ⟨102762512282446890781526333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68508341521631260521017555 102762512282446890781526333)
    ·
      refine ⟨38535942105917584043072375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102762512282446890781526333 38535942105917584043072375)
      ·
        refine ⟨57803913158876376064608563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38535942105917584043072375 57803913158876376064608563)
        ·
          refine ⟨86705869738314564096912845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57803913158876376064608563 86705869738314564096912845)
          ·
            refine ⟨32514701151867961536342317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86705869738314564096912845 32514701151867961536342317)
            ·
              refine ⟨12193012931950485576128369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32514701151867961536342317 12193012931950485576128369)
              ·
                refine ⟨9144759698962864182096277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12193012931950485576128369 9144759698962864182096277)
                ·
                  refine ⟨428660610888884258535763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9144759698962864182096277 428660610888884258535763)
                  ·
                    rfl

theorem cell23_7513322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 6].length) (baseStart_7513322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513322 prefixEnd_7513322 := by exact prefixLift 7513322
  have htrace : WordTrace (prefixWord ++ tailWord_7513322) baseStart_7513322 baseEnd_7513322 := by
    simpa [prefixWord, tailWord_7513322, baseEnd_7513322] using wordTrace_append hprefix tailTrace_7513322
  have hstable : (prefixWord ++ tailWord_7513322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513322).length < 2 ^ (prefixWord ++ tailWord_7513322).sum := by decide
  have hdescent : baseEnd_7513322 < baseStart_7513322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513365 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 3, 6]
def baseStart_7513365 : Nat := 118140960795 + 7513365 * 2 ^ 59
def prefixEnd_7513365 : Nat := 4983230072969 + 3 ^ 40 * 7513365 * 2
def baseEnd_7513365 : Nat := 1285989192556033886194723

theorem tailTrace_7513365 : CollatzResearch.WordTrace tailWord_7513365 prefixEnd_7513365 1285989192556033886194723 := by
  unfold tailWord_7513365
  simp only [CollatzResearch.WordTrace]
  refine ⟨274034934425369260427885549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182689956283579506951923699 274034934425369260427885549)
  ·
    refine ⟨102763100409513472660457081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274034934425369260427885549 102763100409513472660457081)
    ·
      refine ⟨77072325307135104495342811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102763100409513472660457081 77072325307135104495342811)
      ·
        refine ⟨115608487960702656743014217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77072325307135104495342811 115608487960702656743014217)
        ·
          refine ⟨86706365970526992557260663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115608487960702656743014217 86706365970526992557260663)
          ·
            refine ⟨130059548955790488835890995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86706365970526992557260663 130059548955790488835890995)
            ·
              refine ⟨195089323433685733253836493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130059548955790488835890995 195089323433685733253836493)
              ·
                refine ⟨73158496287632149970188685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195089323433685733253836493 73158496287632149970188685)
                ·
                  refine ⟨27434436107862056238820757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73158496287632149970188685 27434436107862056238820757)
                  ·
                    refine ⟨1285989192556033886194723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27434436107862056238820757 1285989192556033886194723)
                    ·
                      rfl

theorem cell23_7513365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_7513365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513365 prefixEnd_7513365 := by exact prefixLift 7513365
  have htrace : WordTrace (prefixWord ++ tailWord_7513365) baseStart_7513365 baseEnd_7513365 := by
    simpa [prefixWord, tailWord_7513365, baseEnd_7513365] using wordTrace_append hprefix tailTrace_7513365
  have hstable : (prefixWord ++ tailWord_7513365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513365).length < 2 ^ (prefixWord ++ tailWord_7513365).sum := by decide
  have hdescent : baseEnd_7513365 < baseStart_7513365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513376 : List Nat := [2, 1, 1, 5, 3, 1, 1, 2, 2, 3, 2]
def baseStart_7513376 : Nat := 118140960795 + 7513376 * 2 ^ 59
def prefixEnd_7513376 : Nat := 4983230072969 + 3 ^ 40 * 7513376 * 2
def baseEnd_7513376 : Nat := 3857973225955301115546619

theorem tailTrace_7513376 : CollatzResearch.WordTrace tailWord_7513376 prefixEnd_7513376 3857973225955301115546619 := by
  unfold tailWord_7513376
  simp only [CollatzResearch.WordTrace]
  refine ⟨137017667814164704653267991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182690223752219606204357321 137017667814164704653267991)
  ·
    refine ⟨205526501721247056979901987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137017667814164704653267991 205526501721247056979901987)
    ·
      refine ⟨308289752581870585469852981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205526501721247056979901987 308289752581870585469852981)
      ·
        refine ⟨28902164304550367387798717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 308289752581870585469852981 28902164304550367387798717)
        ·
          refine ⟨10838311614206387770424519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28902164304550367387798717 10838311614206387770424519)
          ·
            refine ⟨16257467421309581655636779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10838311614206387770424519 16257467421309581655636779)
            ·
              refine ⟨24386201131964372483455169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16257467421309581655636779 24386201131964372483455169)
              ·
                refine ⟨18289650848973279362591377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24386201131964372483455169 18289650848973279362591377)
                ·
                  refine ⟨13717238136729959521943533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18289650848973279362591377 13717238136729959521943533)
                  ·
                    refine ⟨5143964301273734820728825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13717238136729959521943533 5143964301273734820728825)
                    ·
                      refine ⟨3857973225955301115546619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5143964301273734820728825 3857973225955301115546619)
                      ·
                        rfl

theorem cell23_7513376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_7513376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513376 prefixEnd_7513376 := by exact prefixLift 7513376
  have htrace : WordTrace (prefixWord ++ tailWord_7513376) baseStart_7513376 baseEnd_7513376 := by
    simpa [prefixWord, tailWord_7513376, baseEnd_7513376] using wordTrace_append hprefix tailTrace_7513376
  have hstable : (prefixWord ++ tailWord_7513376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513376).length < 2 ^ (prefixWord ++ tailWord_7513376).sum := by decide
  have hdescent : baseEnd_7513376 < baseStart_7513376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513392 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 3]
def baseStart_7513392 : Nat := 118140960795 + 7513392 * 2 ^ 59
def prefixEnd_7513392 : Nat := 4983230072969 + 3 ^ 40 * 7513392 * 2
def baseEnd_7513392 : Nat := 3857981441645773052946545

theorem tailTrace_7513392 : CollatzResearch.WordTrace tailWord_7513392 prefixEnd_7513392 3857981441645773052946545 := by
  unfold tailWord_7513392
  simp only [CollatzResearch.WordTrace]
  refine ⟨137017959598135722019559215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182690612797514296026078953 137017959598135722019559215)
  ·
    refine ⟨205526939397203583029338823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137017959598135722019559215 205526939397203583029338823)
    ·
      refine ⟨308290409095805374544008235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205526939397203583029338823 308290409095805374544008235)
      ·
        refine ⟨462435613643708061816012353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308290409095805374544008235 462435613643708061816012353)
        ·
          refine ⟨346826710232781046362009265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462435613643708061816012353 346826710232781046362009265)
          ·
            refine ⟨260120032674585784771506949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346826710232781046362009265 260120032674585784771506949)
            ·
              refine ⟨48772506126484834644657553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260120032674585784771506949 48772506126484834644657553)
              ·
                refine ⟨36579379594863625983493165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48772506126484834644657553 36579379594863625983493165)
                ·
                  refine ⟨13717267348073859743809937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36579379594863625983493165 13717267348073859743809937)
                  ·
                    refine ⟨10287950511055394807857453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13717267348073859743809937 10287950511055394807857453)
                    ·
                      refine ⟨3857981441645773052946545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10287950511055394807857453 3857981441645773052946545)
                      ·
                        rfl

theorem cell23_7513392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 3].length) (baseStart_7513392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513392 prefixEnd_7513392 := by exact prefixLift 7513392
  have htrace : WordTrace (prefixWord ++ tailWord_7513392) baseStart_7513392 baseEnd_7513392 := by
    simpa [prefixWord, tailWord_7513392, baseEnd_7513392] using wordTrace_append hprefix tailTrace_7513392
  have hstable : (prefixWord ++ tailWord_7513392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513392).length < 2 ^ (prefixWord ++ tailWord_7513392).sum := by decide
  have hdescent : baseEnd_7513392 < baseStart_7513392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513395 : List Nat := [1, 1, 1, 2, 5, 2, 1, 10]
def baseStart_7513395 : Nat := 118140960795 + 7513395 * 2 ^ 59
def prefixEnd_7513395 : Nat := 4983230072969 + 3 ^ 40 * 7513395 * 2
def baseEnd_7513395 : Nat := 142888258595842094118853

theorem tailTrace_7513395 : CollatzResearch.WordTrace tailWord_7513395 prefixEnd_7513395 142888258595842094118853 := by
  unfold tailWord_7513395
  simp only [CollatzResearch.WordTrace]
  refine ⟨274036028615260575551477639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182690685743507050367651759 274036028615260575551477639)
  ·
    refine ⟨411054042922890863327216459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274036028615260575551477639 411054042922890863327216459)
    ·
      refine ⟨616581064384336294990824689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411054042922890863327216459 616581064384336294990824689)
      ·
        refine ⟨462435798288252221243118517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616581064384336294990824689 462435798288252221243118517)
        ·
          refine ⟨43353356089523645741542361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 462435798288252221243118517 43353356089523645741542361)
          ·
            refine ⟨32515017067142734306156771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43353356089523645741542361 32515017067142734306156771)
            ·
              refine ⟨48772525600714101459235157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32515017067142734306156771 48772525600714101459235157)
              ·
                refine ⟨142888258595842094118853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48772525600714101459235157 142888258595842094118853)
                ·
                  rfl

theorem cell23_7513395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 10].length) (baseStart_7513395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513395 prefixEnd_7513395 := by exact prefixLift 7513395
  have htrace : WordTrace (prefixWord ++ tailWord_7513395) baseStart_7513395 baseEnd_7513395 := by
    simpa [prefixWord, tailWord_7513395, baseEnd_7513395] using wordTrace_append hprefix tailTrace_7513395
  have hstable : (prefixWord ++ tailWord_7513395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513395).length < 2 ^ (prefixWord ++ tailWord_7513395).sum := by decide
  have hdescent : baseEnd_7513395 < baseStart_7513395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513402 : List Nat := [3, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4]
def baseStart_7513402 : Nat := 118140960795 + 7513402 * 2 ^ 59
def prefixEnd_7513402 : Nat := 4983230072969 + 3 ^ 40 * 7513402 * 2
def baseEnd_7513402 : Nat := 3857986576452318013821499

theorem tailTrace_7513402 : CollatzResearch.WordTrace tailWord_7513402 prefixEnd_7513402 3857986576452318013821499 := by
  unfold tailWord_7513402
  simp only [CollatzResearch.WordTrace]
  refine ⟨68509070981558803936745615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182690855950823477164654973 68509070981558803936745615)
  ·
    refine ⟨102763606472338205905118423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68509070981558803936745615 102763606472338205905118423)
    ·
      refine ⟨154145409708507308857677635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102763606472338205905118423 154145409708507308857677635)
      ·
        refine ⟨231218114562760963286516453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154145409708507308857677635 231218114562760963286516453)
        ·
          refine ⟨43353396480517680616221835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231218114562760963286516453 43353396480517680616221835)
          ·
            refine ⟨65030094720776520924332753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43353396480517680616221835 65030094720776520924332753)
            ·
              refine ⟨48772571040582390693249565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65030094720776520924332753 48772571040582390693249565)
              ·
                refine ⟨18289714140218396509968587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48772571040582390693249565 18289714140218396509968587)
                ·
                  refine ⟨27434571210327594764952881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18289714140218396509968587 27434571210327594764952881)
                  ·
                    refine ⟨20575928407745696073714661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27434571210327594764952881 20575928407745696073714661)
                    ·
                      refine ⟨3857986576452318013821499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20575928407745696073714661 3857986576452318013821499)
                      ·
                        rfl

theorem cell23_7513402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_7513402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513402 prefixEnd_7513402 := by exact prefixLift 7513402
  have htrace : WordTrace (prefixWord ++ tailWord_7513402) baseStart_7513402 baseEnd_7513402 := by
    simpa [prefixWord, tailWord_7513402, baseEnd_7513402] using wordTrace_append hprefix tailTrace_7513402
  have hstable : (prefixWord ++ tailWord_7513402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513402).length < 2 ^ (prefixWord ++ tailWord_7513402).sum := by decide
  have hdescent : baseEnd_7513402 < baseStart_7513402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513406 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 5, 2, 2]
def baseStart_7513406 : Nat := 118140960795 + 7513406 * 2 ^ 59
def prefixEnd_7513406 : Nat := 4983230072969 + 3 ^ 40 * 7513406 * 2
def baseEnd_7513406 : Nat := 3857988630374935998171481

theorem tailTrace_7513406 : CollatzResearch.WordTrace tailWord_7513406 prefixEnd_7513406 3857988630374935998171481 := by
  unfold tailWord_7513406
  simp only [CollatzResearch.WordTrace]
  refine ⟨34254553727277590553766009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182690953212147149620085381 34254553727277590553766009)
  ·
    refine ⟨25690915295458192915324507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34254553727277590553766009 25690915295458192915324507)
    ·
      refine ⟨38536372943187289372986761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25690915295458192915324507 38536372943187289372986761)
      ·
        refine ⟨28902279707390467029740071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38536372943187289372986761 28902279707390467029740071)
        ·
          refine ⟨43353419561085700544610107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28902279707390467029740071 43353419561085700544610107)
          ·
            refine ⟨65030129341628550816915161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43353419561085700544610107 65030129341628550816915161)
            ·
              refine ⟨48772597006221413112686371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65030129341628550816915161 48772597006221413112686371)
              ·
                refine ⟨73158895509332119669029557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48772597006221413112686371 73158895509332119669029557)
                ·
                  refine ⟨6858646453999886218971521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73158895509332119669029557 6858646453999886218971521)
                  ·
                    refine ⟨5143984840499914664228641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6858646453999886218971521 5143984840499914664228641)
                    ·
                      refine ⟨3857988630374935998171481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5143984840499914664228641 3857988630374935998171481)
                      ·
                        rfl

theorem cell23_7513406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_7513406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513406 prefixEnd_7513406 := by exact prefixLift 7513406
  have htrace : WordTrace (prefixWord ++ tailWord_7513406) baseStart_7513406 baseEnd_7513406 := by
    simpa [prefixWord, tailWord_7513406, baseEnd_7513406] using wordTrace_append hprefix tailTrace_7513406
  have hstable : (prefixWord ++ tailWord_7513406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513406).length < 2 ^ (prefixWord ++ tailWord_7513406).sum := by decide
  have hdescent : baseEnd_7513406 < baseStart_7513406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513440 : List Nat := [2, 1, 1, 3, 4, 1, 4, 2, 1, 2, 2]
def baseStart_7513440 : Nat := 118140960795 + 7513440 * 2 ^ 59
def prefixEnd_7513440 : Nat := 4983230072969 + 3 ^ 40 * 7513440 * 2
def baseEnd_7513440 : Nat := 3858006088717188865146325

theorem tailTrace_7513440 : CollatzResearch.WordTrace tailWord_7513440 prefixEnd_7513440 3858006088717188865146325 := by
  unfold tailWord_7513440
  simp only [CollatzResearch.WordTrace]
  refine ⟨137018834950048774118432887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182691779933398365491243849 137018834950048774118432887)
  ·
    refine ⟨205528252425073161177649331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137018834950048774118432887 205528252425073161177649331)
    ·
      refine ⟨308292378637609741766473997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205528252425073161177649331 308292378637609741766473997)
      ·
        refine ⟨115609641989103653162427749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308292378637609741766473997 115609641989103653162427749)
        ·
          refine ⟨21676807872956934967955203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115609641989103653162427749 21676807872956934967955203)
          ·
            refine ⟨32515211809435402451932805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21676807872956934967955203 32515211809435402451932805)
            ·
              refine ⟨6096602214269137959737401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32515211809435402451932805 6096602214269137959737401)
              ·
                refine ⟨4572451660701853469803051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6096602214269137959737401 4572451660701853469803051)
                ·
                  refine ⟨6858677491052780204704577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4572451660701853469803051 6858677491052780204704577)
                  ·
                    refine ⟨5144008118289585153528433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6858677491052780204704577 5144008118289585153528433)
                    ·
                      refine ⟨3858006088717188865146325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5144008118289585153528433 3858006088717188865146325)
                      ·
                        rfl

theorem cell23_7513440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 1, 2, 2].length) (baseStart_7513440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513440 prefixEnd_7513440 := by exact prefixLift 7513440
  have htrace : WordTrace (prefixWord ++ tailWord_7513440) baseStart_7513440 baseEnd_7513440 := by
    simpa [prefixWord, tailWord_7513440, baseEnd_7513440] using wordTrace_append hprefix tailTrace_7513440
  have hstable : (prefixWord ++ tailWord_7513440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513440).length < 2 ^ (prefixWord ++ tailWord_7513440).sum := by decide
  have hdescent : baseEnd_7513440 < baseStart_7513440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513442 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_7513442 : Nat := 118140960795 + 7513442 * 2 ^ 59
def prefixEnd_7513442 : Nat := 4983230072969 + 3 ^ 40 * 7513442 * 2
def baseEnd_7513442 : Nat := 1286002371892832619107105

theorem tailTrace_7513442 : CollatzResearch.WordTrace tailWord_7513442 prefixEnd_7513442 1286002371892832619107105 := by
  unfold tailWord_7513442
  simp only [CollatzResearch.WordTrace]
  refine ⟨68509435711522575644609645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182691828564060201718959053 68509435711522575644609645)
  ·
    refine ⟨25691038391820965866728617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68509435711522575644609645 25691038391820965866728617)
    ·
      refine ⟨19268278793865724400046463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25691038391820965866728617 19268278793865724400046463)
      ·
        refine ⟨28902418190798586600069695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19268278793865724400046463 28902418190798586600069695)
        ·
          refine ⟨43353627286197879900104543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28902418190798586600069695 43353627286197879900104543)
          ·
            refine ⟨65030440929296819850156815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43353627286197879900104543 65030440929296819850156815)
            ·
              refine ⟨97545661393945229775235223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65030440929296819850156815 97545661393945229775235223)
              ·
                refine ⟨146318492090917844662852835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97545661393945229775235223 146318492090917844662852835)
                ·
                  refine ⟨219477738136376766994279253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146318492090917844662852835 219477738136376766994279253)
                  ·
                    refine ⟨1286002371892832619107105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 219477738136376766994279253 1286002371892832619107105)
                    ·
                      rfl

theorem cell23_7513442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_7513442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513442 prefixEnd_7513442 := by exact prefixLift 7513442
  have htrace : WordTrace (prefixWord ++ tailWord_7513442) baseStart_7513442 baseEnd_7513442 := by
    simpa [prefixWord, tailWord_7513442, baseEnd_7513442] using wordTrace_append hprefix tailTrace_7513442
  have hstable : (prefixWord ++ tailWord_7513442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513442).length < 2 ^ (prefixWord ++ tailWord_7513442).sum := by decide
  have hdescent : baseEnd_7513442 < baseStart_7513442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513572 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_7513572 : Nat := 118140960795 + 7513572 * 2 ^ 59
def prefixEnd_7513572 : Nat := 4983230072969 + 3 ^ 40 * 7513572 * 2
def baseEnd_7513572 : Nat := 3858073868163582348695717

theorem tailTrace_7513572 : CollatzResearch.WordTrace tailWord_7513572 prefixEnd_7513572 3858073868163582348695717 := by
  unfold tailWord_7513572
  simp only [CollatzResearch.WordTrace]
  refine ⟨137021242167809667390335485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182694989557079556520447313 137021242167809667390335485)
  ·
    refine ⟨51382965812928625271375807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137021242167809667390335485 51382965812928625271375807)
    ·
      refine ⟨77074448719392937907063711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51382965812928625271375807 77074448719392937907063711)
      ·
        refine ⟨115611673079089406860595567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77074448719392937907063711 115611673079089406860595567)
        ·
          refine ⟨173417509618634110290893351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115611673079089406860595567 173417509618634110290893351)
          ·
            refine ⟨260126264427951165436340027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173417509618634110290893351 260126264427951165436340027)
            ·
              refine ⟨390189396641926748154510041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260126264427951165436340027 390189396641926748154510041)
              ·
                refine ⟨292642047481445061115882531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390189396641926748154510041 292642047481445061115882531)
                ·
                  refine ⟨438963071222167591673823797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292642047481445061115882531 438963071222167591673823797)
                  ·
                    refine ⟨41152787927078211719420981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 438963071222167591673823797 41152787927078211719420981)
                    ·
                      refine ⟨3858073868163582348695717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41152787927078211719420981 3858073868163582348695717)
                      ·
                        rfl

theorem cell23_7513572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_7513572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513572 prefixEnd_7513572 := by exact prefixLift 7513572
  have htrace : WordTrace (prefixWord ++ tailWord_7513572) baseStart_7513572 baseEnd_7513572 := by
    simpa [prefixWord, tailWord_7513572, baseEnd_7513572] using wordTrace_append hprefix tailTrace_7513572
  have hstable : (prefixWord ++ tailWord_7513572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513572).length < 2 ^ (prefixWord ++ tailWord_7513572).sum := by decide
  have hdescent : baseEnd_7513572 < baseStart_7513572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513586 : List Nat := [3, 2, 1, 4, 1, 1, 1, 3, 2, 1, 4]
def baseStart_7513586 : Nat := 118140960795 + 7513586 * 2 ^ 59
def prefixEnd_7513586 : Nat := 4983230072969 + 3 ^ 40 * 7513586 * 2
def baseEnd_7513586 : Nat := 3858081056892745293920653

theorem tailTrace_7513586 : CollatzResearch.WordTrace tailWord_7513586 prefixEnd_7513586 3858081056892745293920653 := by
  unfold tailWord_7513586
  simp only [CollatzResearch.WordTrace]
  refine ⟨68510748739392153792920153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182695329971712410114453741 68510748739392153792920153)
  ·
    refine ⟨51383061554544115344690115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68510748739392153792920153 51383061554544115344690115)
    ·
      refine ⟨77074592331816173017035173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51383061554544115344690115 77074592331816173017035173)
      ·
        refine ⟨14451486062215532440694095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77074592331816173017035173 14451486062215532440694095)
        ·
          refine ⟨21677229093323298661041143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14451486062215532440694095 21677229093323298661041143)
          ·
            refine ⟨32515843639984947991561715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21677229093323298661041143 32515843639984947991561715)
            ·
              refine ⟨48773765459977421987342573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32515843639984947991561715 48773765459977421987342573)
              ·
                refine ⟨18290162047491533245253465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48773765459977421987342573 18290162047491533245253465)
                ·
                  refine ⟨13717621535618649933940099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18290162047491533245253465 13717621535618649933940099)
                  ·
                    refine ⟨20576432303427974900910149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13717621535618649933940099 20576432303427974900910149)
                    ·
                      refine ⟨3858081056892745293920653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20576432303427974900910149 3858081056892745293920653)
                      ·
                        rfl

theorem cell23_7513586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_7513586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513586 prefixEnd_7513586 := by exact prefixLift 7513586
  have htrace : WordTrace (prefixWord ++ tailWord_7513586) baseStart_7513586 baseEnd_7513586 := by
    simpa [prefixWord, tailWord_7513586, baseEnd_7513586] using wordTrace_append hprefix tailTrace_7513586
  have hstable : (prefixWord ++ tailWord_7513586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513586).length < 2 ^ (prefixWord ++ tailWord_7513586).sum := by decide
  have hdescent : baseEnd_7513586 < baseStart_7513586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513609 : List Nat := [1, 2, 1, 1, 3, 1, 6, 2, 6]
def baseStart_7513609 : Nat := 118140960795 + 7513609 * 2 ^ 59
def prefixEnd_7513609 : Nat := 4983230072969 + 3 ^ 40 * 7513609 * 2
def baseEnd_7513609 : Nat := 428676985216422078214783

theorem tailTrace_7513609 : CollatzResearch.WordTrace tailWord_7513609 prefixEnd_7513609 428676985216422078214783 := by
  unfold tailWord_7513609
  simp only [CollatzResearch.WordTrace]
  refine ⟨274043833836485290099767881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182695889224323526733178587 274043833836485290099767881)
  ·
    refine ⟨205532875377363967574825911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274043833836485290099767881 205532875377363967574825911)
    ·
      refine ⟨308299313066045951362238867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205532875377363967574825911 308299313066045951362238867)
      ·
        refine ⟨462448969599068927043358301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308299313066045951362238867 462448969599068927043358301)
        ·
          refine ⟨173418363599650847641259363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 462448969599068927043358301 173418363599650847641259363)
          ·
            refine ⟨260127545399476271461889045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173418363599650847641259363 260127545399476271461889045)
            ·
              refine ⟨12193478690600450224776049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 260127545399476271461889045 12193478690600450224776049)
              ·
                refine ⟨9145109017950337668582037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12193478690600450224776049 9145109017950337668582037)
                ·
                  refine ⟨428676985216422078214783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9145109017950337668582037 428676985216422078214783)
                  ·
                    rfl

theorem cell23_7513609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 6].length) (baseStart_7513609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513609 prefixEnd_7513609 := by exact prefixLift 7513609
  have htrace : WordTrace (prefixWord ++ tailWord_7513609) baseStart_7513609 baseEnd_7513609 := by
    simpa [prefixWord, tailWord_7513609, baseEnd_7513609] using wordTrace_append hprefix tailTrace_7513609
  have hstable : (prefixWord ++ tailWord_7513609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513609).length < 2 ^ (prefixWord ++ tailWord_7513609).sum := by decide
  have hdescent : baseEnd_7513609 < baseStart_7513609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513620 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_7513620 : Nat := 118140960795 + 7513620 * 2 ^ 59
def prefixEnd_7513620 : Nat := 4983230072969 + 3 ^ 40 * 7513620 * 2
def baseEnd_7513620 : Nat := 3858098515234998160895497

theorem tailTrace_7513620 : CollatzResearch.WordTrace tailWord_7513620 prefixEnd_7513620 3858098515234998160895497 := by
  unfold tailWord_7513620
  simp only [CollatzResearch.WordTrace]
  refine ⟨137022117519722719489209157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182696156692963625985612209 137022117519722719489209157)
  ·
    refine ⟨25691647034948009904226717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137022117519722719489209157 25691647034948009904226717)
    ·
      refine ⟨9634367638105503714085019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25691647034948009904226717 9634367638105503714085019)
      ·
        refine ⟨14451551457158255571127529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9634367638105503714085019 14451551457158255571127529)
        ·
          refine ⟨10838663592868691678345647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14451551457158255571127529 10838663592868691678345647)
          ·
            refine ⟨16257995389303037517518471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10838663592868691678345647 16257995389303037517518471)
            ·
              refine ⟨24386993083954556276277707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16257995389303037517518471 24386993083954556276277707)
              ·
                refine ⟨36580489625931834414416561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24386993083954556276277707 36580489625931834414416561)
                ·
                  refine ⟨27435367219448875810812421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36580489625931834414416561 27435367219448875810812421)
                  ·
                    refine ⟨5144131353646664214527329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27435367219448875810812421 5144131353646664214527329)
                    ·
                      refine ⟨3858098515234998160895497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5144131353646664214527329 3858098515234998160895497)
                      ·
                        rfl

theorem cell23_7513620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_7513620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513620 prefixEnd_7513620 := by exact prefixLift 7513620
  have htrace : WordTrace (prefixWord ++ tailWord_7513620) baseStart_7513620 baseEnd_7513620 := by
    simpa [prefixWord, tailWord_7513620, baseEnd_7513620] using wordTrace_append hprefix tailTrace_7513620
  have hstable : (prefixWord ++ tailWord_7513620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513620).length < 2 ^ (prefixWord ++ tailWord_7513620).sum := by decide
  have hdescent : baseEnd_7513620 < baseStart_7513620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513640 : List Nat := [2, 1, 5, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_7513640 : Nat := 118140960795 + 7513640 * 2 ^ 59
def prefixEnd_7513640 : Nat := 4983230072969 + 3 ^ 40 * 7513640 * 2
def baseEnd_7513640 : Nat := 3858108784848088082645405

theorem tailTrace_7513640 : CollatzResearch.WordTrace tailWord_7513640 prefixEnd_7513640 3858108784848088082645405 := by
  unfold tailWord_7513640
  simp only [CollatzResearch.WordTrace]
  refine ⟨137022482249686491197073187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182696642999581988262764249 137022482249686491197073187)
  ·
    refine ⟨205533723374529736795609781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137022482249686491197073187 205533723374529736795609781)
    ·
      refine ⟨19268786566362162824588417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205533723374529736795609781 19268786566362162824588417)
      ·
        refine ⟨14451589924771622118441313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19268786566362162824588417 14451589924771622118441313)
        ·
          refine ⟨10838692443578716588830985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14451589924771622118441313 10838692443578716588830985)
          ·
            refine ⟨8129019332684037441623239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10838692443578716588830985 8129019332684037441623239)
            ·
              refine ⟨12193528999026056162434859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8129019332684037441623239 12193528999026056162434859)
              ·
                refine ⟨18290293498539084243652289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12193528999026056162434859 18290293498539084243652289)
                ·
                  refine ⟨13717720123904313182739217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18290293498539084243652289 13717720123904313182739217)
                  ·
                    refine ⟨10288290092928234887054413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13717720123904313182739217 10288290092928234887054413)
                    ·
                      refine ⟨3858108784848088082645405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10288290092928234887054413 3858108784848088082645405)
                      ·
                        rfl

theorem cell23_7513640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_7513640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513640 prefixEnd_7513640 := by exact prefixLift 7513640
  have htrace : WordTrace (prefixWord ++ tailWord_7513640) baseStart_7513640 baseEnd_7513640 := by
    simpa [prefixWord, tailWord_7513640, baseEnd_7513640] using wordTrace_append hprefix tailTrace_7513640
  have hstable : (prefixWord ++ tailWord_7513640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513640).length < 2 ^ (prefixWord ++ tailWord_7513640).sum := by decide
  have hdescent : baseEnd_7513640 < baseStart_7513640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513656 : List Nat := [2, 1, 2, 1, 4, 3, 1, 3, 1, 5]
def baseStart_7513656 : Nat := 118140960795 + 7513656 * 2 ^ 59
def prefixEnd_7513656 : Nat := 4983230072969 + 3 ^ 40 * 7513656 * 2
def baseEnd_7513656 : Nat := 1286039000179520006681777

theorem tailTrace_7513656 : CollatzResearch.WordTrace tailWord_7513656 prefixEnd_7513656 1286039000179520006681777 := by
  unfold tailWord_7513656
  simp only [CollatzResearch.WordTrace]
  refine ⟨137022774033657508563364411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182697032044876678084485881 137022774033657508563364411)
  ·
    refine ⟨205534161050486262845046617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137022774033657508563364411 205534161050486262845046617)
    ·
      refine ⟨154150620787864697133784963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205534161050486262845046617 154150620787864697133784963)
      ·
        refine ⟨231225931181797045700677445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154150620787864697133784963 231225931181797045700677445)
        ·
          refine ⟨43354862096586946068877021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231225931181797045700677445 43354862096586946068877021)
          ·
            refine ⟨16258073286220104775828883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43354862096586946068877021 16258073286220104775828883)
            ·
              refine ⟨24387109929330157163743325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16258073286220104775828883 24387109929330157163743325)
              ·
                refine ⟨9145166223498808936403747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24387109929330157163743325 9145166223498808936403747)
                ·
                  refine ⟨13717749335248213404605621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9145166223498808936403747 13717749335248213404605621)
                  ·
                    refine ⟨1286039000179520006681777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13717749335248213404605621 1286039000179520006681777)
                    ·
                      rfl

theorem cell23_7513656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 1, 5].length) (baseStart_7513656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513656 prefixEnd_7513656 := by exact prefixLift 7513656
  have htrace : WordTrace (prefixWord ++ tailWord_7513656) baseStart_7513656 baseEnd_7513656 := by
    simpa [prefixWord, tailWord_7513656, baseEnd_7513656] using wordTrace_append hprefix tailTrace_7513656
  have hstable : (prefixWord ++ tailWord_7513656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513656).length < 2 ^ (prefixWord ++ tailWord_7513656).sum := by decide
  have hdescent : baseEnd_7513656 < baseStart_7513656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513699 : List Nat := [1, 1, 1, 5, 1, 4, 1, 9]
def baseStart_7513699 : Nat := 118140960795 + 7513699 * 2 ^ 59
def prefixEnd_7513699 : Nat := 4983230072969 + 3 ^ 40 * 7513699 * 2
def baseEnd_7513699 : Nat := 142894040007655679696579

theorem tailTrace_7513699 : CollatzResearch.WordTrace tailWord_7513699 prefixEnd_7513699 142894040007655679696579 := by
  unfold tailWord_7513699
  simp only [CollatzResearch.WordTrace]
  refine ⟨274047116406159235470544151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182698077604106156980362767 274047116406159235470544151)
  ·
    refine ⟨411070674609238853205816227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274047116406159235470544151 411070674609238853205816227)
    ·
      refine ⟨616606011913858279808724341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411070674609238853205816227 616606011913858279808724341)
      ·
        refine ⟨57806813616924213732067907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 616606011913858279808724341 57806813616924213732067907)
        ·
          refine ⟨86710220425386320598101861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57806813616924213732067907 86710220425386320598101861)
          ·
            refine ⟨16258166329759935112144099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86710220425386320598101861 16258166329759935112144099)
            ·
              refine ⟨24387249494639902668216149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16258166329759935112144099 24387249494639902668216149)
              ·
                refine ⟨142894040007655679696579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24387249494639902668216149 142894040007655679696579)
                ·
                  rfl

theorem cell23_7513699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 9].length) (baseStart_7513699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513699 prefixEnd_7513699 := by exact prefixLift 7513699
  have htrace : WordTrace (prefixWord ++ tailWord_7513699) baseStart_7513699 baseEnd_7513699 := by
    simpa [prefixWord, tailWord_7513699, baseEnd_7513699] using wordTrace_append hprefix tailTrace_7513699
  have hstable : (prefixWord ++ tailWord_7513699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513699).length < 2 ^ (prefixWord ++ tailWord_7513699).sum := by decide
  have hdescent : baseEnd_7513699 < baseStart_7513699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513753 : List Nat := [1, 2, 1, 2, 1, 2, 2, 6, 1, 3, 2]
def baseStart_7513753 : Nat := 118140960795 + 7513753 * 2 ^ 59
def prefixEnd_7513753 : Nat := 4983230072969 + 3 ^ 40 * 7513753 * 2
def baseEnd_7513753 : Nat := 3858166808162046140532385

theorem tailTrace_7513753 : CollatzResearch.WordTrace tailWord_7513753 prefixEnd_7513753 3858166808162046140532385 := by
  unfold tailWord_7513753
  simp only [CollatzResearch.WordTrace]
  refine ⟨274049085947963602693009913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182699390631975735128673275 274049085947963602693009913)
  ·
    refine ⟨205536814460972702019757435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274049085947963602693009913 205536814460972702019757435)
    ·
      refine ⟨308305221691459053029636153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205536814460972702019757435 308305221691459053029636153)
      ·
        refine ⟨231228916268594289772227115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308305221691459053029636153 231228916268594289772227115)
        ·
          refine ⟨346843374402891434658340673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231228916268594289772227115 346843374402891434658340673)
          ·
            refine ⟨260132530802168575993755505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346843374402891434658340673 260132530802168575993755505)
            ·
              refine ⟨195099398101626431995316629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260132530802168575993755505 195099398101626431995316629)
              ·
                refine ⟨9145284286013738999780467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 195099398101626431995316629 9145284286013738999780467)
                ·
                  refine ⟨13717926429020608499670701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9145284286013738999780467 13717926429020608499670701)
                  ·
                    refine ⟨5144222410882728187376513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13717926429020608499670701 5144222410882728187376513)
                    ·
                      refine ⟨3858166808162046140532385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5144222410882728187376513 3858166808162046140532385)
                      ·
                        rfl

theorem cell23_7513753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 3, 2].length) (baseStart_7513753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513753 prefixEnd_7513753 := by exact prefixLift 7513753
  have htrace : WordTrace (prefixWord ++ tailWord_7513753) baseStart_7513753 baseEnd_7513753 := by
    simpa [prefixWord, tailWord_7513753, baseEnd_7513753] using wordTrace_append hprefix tailTrace_7513753
  have hstable : (prefixWord ++ tailWord_7513753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513753).length < 2 ^ (prefixWord ++ tailWord_7513753).sum := by decide
  have hdescent : baseEnd_7513753 < baseStart_7513753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513769 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 6, 1, 5]
def baseStart_7513769 : Nat := 118140960795 + 7513769 * 2 ^ 59
def prefixEnd_7513769 : Nat := 4983230072969 + 3 ^ 40 * 7513769 * 2
def baseEnd_7513769 : Nat := 3858175023852518077932311

theorem tailTrace_7513769 : CollatzResearch.WordTrace tailWord_7513769 prefixEnd_7513769 3858175023852518077932311 := by
  unfold tailWord_7513769
  simp only [CollatzResearch.WordTrace]
  refine ⟨274049669515905637425592361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182699779677270424950394907 274049669515905637425592361)
  ·
    refine ⟨205537252136929228069194271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274049669515905637425592361 205537252136929228069194271)
    ·
      refine ⟨308305878205393842103791407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205537252136929228069194271 308305878205393842103791407)
      ·
        refine ⟨462458817308090763155687111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308305878205393842103791407 462458817308090763155687111)
        ·
          refine ⟨693688225962136144733530667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462458817308090763155687111 693688225962136144733530667)
          ·
            refine ⟨1040532338943204217100296001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693688225962136144733530667 1040532338943204217100296001)
            ·
              refine ⟨780399254207403162825222001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1040532338943204217100296001 780399254207403162825222001)
              ·
                refine ⟨585299440655552372118916501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780399254207403162825222001 585299440655552372118916501)
                ·
                  refine ⟨27435911280729017443074211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 585299440655552372118916501 27435911280729017443074211)
                  ·
                    refine ⟨41153866921093526164611317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27435911280729017443074211 41153866921093526164611317)
                    ·
                      refine ⟨3858175023852518077932311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41153866921093526164611317 3858175023852518077932311)
                      ·
                        rfl

theorem cell23_7513769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 1, 5].length) (baseStart_7513769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513769 prefixEnd_7513769 := by exact prefixLift 7513769
  have htrace : WordTrace (prefixWord ++ tailWord_7513769) baseStart_7513769 baseEnd_7513769 := by
    simpa [prefixWord, tailWord_7513769, baseEnd_7513769] using wordTrace_append hprefix tailTrace_7513769
  have hstable : (prefixWord ++ tailWord_7513769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513769).length < 2 ^ (prefixWord ++ tailWord_7513769).sum := by decide
  have hdescent : baseEnd_7513769 < baseStart_7513769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513786 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3]
def baseStart_7513786 : Nat := 118140960795 + 7513786 * 2 ^ 59
def prefixEnd_7513786 : Nat := 4983230072969 + 3 ^ 40 * 7513786 * 2
def baseEnd_7513786 : Nat := 3858183753023644511419733

theorem tailTrace_7513786 : CollatzResearch.WordTrace tailWord_7513786 prefixEnd_7513786 3858183753023644511419733 := by
  unfold tailWord_7513786
  simp only [CollatzResearch.WordTrace]
  refine ⟨68512572389211012332240303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182700193037896032885974141 68512572389211012332240303)
  ·
    refine ⟨102768858583816518498360455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68512572389211012332240303 102768858583816518498360455)
    ·
      refine ⟨154153287875724777747540683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102768858583816518498360455 154153287875724777747540683)
      ·
        refine ⟨231229931813587166621311025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154153287875724777747540683 231229931813587166621311025)
        ·
          refine ⟨173422448860190374965983269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231229931813587166621311025 173422448860190374965983269)
          ·
            refine ⟨32516709161285695306121863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173422448860190374965983269 32516709161285695306121863)
            ·
              refine ⟨48775063741928542959182795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32516709161285695306121863 48775063741928542959182795)
              ·
                refine ⟨73162595612892814438774193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48775063741928542959182795 73162595612892814438774193)
                ·
                  refine ⟨54871946709669610829080645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73162595612892814438774193 54871946709669610829080645)
                  ·
                    refine ⟨10288490008063052030452621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54871946709669610829080645 10288490008063052030452621)
                    ·
                      refine ⟨3858183753023644511419733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10288490008063052030452621 3858183753023644511419733)
                      ·
                        rfl

theorem cell23_7513786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3].length) (baseStart_7513786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513786 prefixEnd_7513786 := by exact prefixLift 7513786
  have htrace : WordTrace (prefixWord ++ tailWord_7513786) baseStart_7513786 baseEnd_7513786 := by
    simpa [prefixWord, tailWord_7513786, baseEnd_7513786] using wordTrace_append hprefix tailTrace_7513786
  have hstable : (prefixWord ++ tailWord_7513786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513786).length < 2 ^ (prefixWord ++ tailWord_7513786).sum := by decide
  have hdescent : baseEnd_7513786 < baseStart_7513786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513794 : List Nat := [3, 5, 1, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_7513794 : Nat := 118140960795 + 7513794 * 2 ^ 59
def prefixEnd_7513794 : Nat := 4983230072969 + 3 ^ 40 * 7513794 * 2
def baseEnd_7513794 : Nat := 3858187860868880480119697

theorem tailTrace_7513794 : CollatzResearch.WordTrace tailWord_7513794 prefixEnd_7513794 3858187860868880480119697 := by
  unfold tailWord_7513794
  simp only [CollatzResearch.WordTrace]
  refine ⟨68512645335203766673813109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182700387560543377796834957 68512645335203766673813109)
  ·
    refine ⟨6423060500175353125669979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68512645335203766673813109 6423060500175353125669979)
    ·
      refine ⟨9634590750263029688504969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6423060500175353125669979 9634590750263029688504969)
      ·
        refine ⟨7225943062697272266378727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9634590750263029688504969 7225943062697272266378727)
        ·
          refine ⟨10838914594045908399568091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7225943062697272266378727 10838914594045908399568091)
          ·
            refine ⟨16258371891068862599352137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10838914594045908399568091 16258371891068862599352137)
            ·
              refine ⟨12193778918301646949514103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16258371891068862599352137 12193778918301646949514103)
              ·
                refine ⟨18290668377452470424271155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12193778918301646949514103 18290668377452470424271155)
                ·
                  refine ⟨27436002566178705636406733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18290668377452470424271155 27436002566178705636406733)
                  ·
                    refine ⟨10288500962317014613652525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27436002566178705636406733 10288500962317014613652525)
                    ·
                      refine ⟨3858187860868880480119697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10288500962317014613652525 3858187860868880480119697)
                      ·
                        rfl

theorem cell23_7513794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_7513794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513794 prefixEnd_7513794 := by exact prefixLift 7513794
  have htrace : WordTrace (prefixWord ++ tailWord_7513794) baseStart_7513794 baseEnd_7513794 := by
    simpa [prefixWord, tailWord_7513794, baseEnd_7513794] using wordTrace_append hprefix tailTrace_7513794
  have hstable : (prefixWord ++ tailWord_7513794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513794).length < 2 ^ (prefixWord ++ tailWord_7513794).sum := by decide
  have hdescent : baseEnd_7513794 < baseStart_7513794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513800 : List Nat := [2, 1, 3, 1, 2, 2, 1, 5, 2, 2, 2]
def baseStart_7513800 : Nat := 118140960795 + 7513800 * 2 ^ 59
def prefixEnd_7513800 : Nat := 4983230072969 + 3 ^ 40 * 7513800 * 2
def baseEnd_7513800 : Nat := 3858190941752807456644669

theorem tailTrace_7513800 : CollatzResearch.WordTrace tailWord_7513800 prefixEnd_7513800 3858190941752807456644669 := by
  unfold tailWord_7513800
  simp only [CollatzResearch.WordTrace]
  refine ⟨137025400089396664859985427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182700533452528886479980569 137025400089396664859985427)
  ·
    refine ⟨205538100134094997289978141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137025400089396664859985427 205538100134094997289978141)
    ·
      refine ⟨77076787550285623983741803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205538100134094997289978141 77076787550285623983741803)
      ·
        refine ⟨115615181325428435975612705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77076787550285623983741803 115615181325428435975612705)
        ·
          refine ⟨86711385994071326981709529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115615181325428435975612705 86711385994071326981709529)
          ·
            refine ⟨65033539495553495236282147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86711385994071326981709529 65033539495553495236282147)
            ·
              refine ⟨97550309243330242854423221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65033539495553495236282147 97550309243330242854423221)
              ·
                refine ⟨9145341491562210267602177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97550309243330242854423221 9145341491562210267602177)
                ·
                  refine ⟨6859006118671657700701633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9145341491562210267602177 6859006118671657700701633)
                  ·
                    refine ⟨5144254589003743275526225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6859006118671657700701633 5144254589003743275526225)
                    ·
                      refine ⟨3858190941752807456644669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5144254589003743275526225 3858190941752807456644669)
                      ·
                        rfl

theorem cell23_7513800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_7513800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513800 prefixEnd_7513800 := by exact prefixLift 7513800
  have htrace : WordTrace (prefixWord ++ tailWord_7513800) baseStart_7513800 baseEnd_7513800 := by
    simpa [prefixWord, tailWord_7513800, baseEnd_7513800] using wordTrace_append hprefix tailTrace_7513800
  have hstable : (prefixWord ++ tailWord_7513800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513800).length < 2 ^ (prefixWord ++ tailWord_7513800).sum := by decide
  have hdescent : baseEnd_7513800 < baseStart_7513800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513806 : List Nat := [4, 1, 1, 1, 3, 1, 3, 2, 7]
def baseStart_7513806 : Nat := 118140960795 + 7513806 * 2 ^ 59
def prefixEnd_7513806 : Nat := 4983230072969 + 3 ^ 40 * 7513806 * 2
def baseEnd_7513806 : Nat := 428688224737414937018849

theorem tailTrace_7513806 : CollatzResearch.WordTrace tailWord_7513806 prefixEnd_7513806 428688224737414937018849 := by
  unfold tailWord_7513806
  simp only [CollatzResearch.WordTrace]
  refine ⟨34256377377096449093086159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182700679344514395163126181 34256377377096449093086159)
  ·
    refine ⟨51384566065644673639629239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34256377377096449093086159 51384566065644673639629239)
    ·
      refine ⟨77076849098467010459443859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51384566065644673639629239 77076849098467010459443859)
      ·
        refine ⟨115615273647700515689165789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77076849098467010459443859 115615273647700515689165789)
        ·
          refine ⟨43355727617887693383437171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115615273647700515689165789 43355727617887693383437171)
          ·
            refine ⟨65033591426831540075155757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43355727617887693383437171 65033591426831540075155757)
            ·
              refine ⟨24387596785061827528183409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65033591426831540075155757 24387596785061827528183409)
              ·
                refine ⟨18290697588796370646137557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24387596785061827528183409 18290697588796370646137557)
                ·
                  refine ⟨428688224737414937018849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18290697588796370646137557 428688224737414937018849)
                  ·
                    rfl

theorem cell23_7513806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_7513806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513806 prefixEnd_7513806 := by exact prefixLift 7513806
  have htrace : WordTrace (prefixWord ++ tailWord_7513806) baseStart_7513806 baseEnd_7513806 := by
    simpa [prefixWord, tailWord_7513806, baseEnd_7513806] using wordTrace_append hprefix tailTrace_7513806
  have hstable : (prefixWord ++ tailWord_7513806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513806).length < 2 ^ (prefixWord ++ tailWord_7513806).sum := by decide
  have hdescent : baseEnd_7513806 < baseStart_7513806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513816 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 1, 5, 3]
def baseStart_7513816 : Nat := 118140960795 + 7513816 * 2 ^ 59
def prefixEnd_7513816 : Nat := 4983230072969 + 3 ^ 40 * 7513816 * 2
def baseEnd_7513816 : Nat := 3858199157443279394044595

theorem tailTrace_7513816 : CollatzResearch.WordTrace tailWord_7513816 prefixEnd_7513816 3858199157443279394044595 := by
  unfold tailWord_7513816
  simp only [CollatzResearch.WordTrace]
  refine ⟨137025691873367682226276651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182700922497823576301702201 137025691873367682226276651)
  ·
    refine ⟨205538537810051523339414977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137025691873367682226276651 205538537810051523339414977)
    ·
      refine ⟨154153903357538642504561233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205538537810051523339414977 154153903357538642504561233)
      ·
        refine ⟨115615427518153981878420925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154153903357538642504561233 115615427518153981878420925)
        ·
          refine ⟨43355785319307743204407847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115615427518153981878420925 43355785319307743204407847)
          ·
            refine ⟨65033677978961614806611771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43355785319307743204407847 65033677978961614806611771)
            ·
              refine ⟨97550516968442422209917657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65033677978961614806611771 97550516968442422209917657)
              ·
                refine ⟨73162887726331816657438243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97550516968442422209917657 73162887726331816657438243)
                ·
                  refine ⟨109744331589497724986157365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73162887726331816657438243 109744331589497724986157365)
                  ·
                    refine ⟨10288531086515411717452253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109744331589497724986157365 10288531086515411717452253)
                    ·
                      refine ⟨3858199157443279394044595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10288531086515411717452253 3858199157443279394044595)
                      ·
                        rfl

theorem cell23_7513816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_7513816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513816 prefixEnd_7513816 := by exact prefixLift 7513816
  have htrace : WordTrace (prefixWord ++ tailWord_7513816) baseStart_7513816 baseEnd_7513816 := by
    simpa [prefixWord, tailWord_7513816, baseEnd_7513816] using wordTrace_append hprefix tailTrace_7513816
  have hstable : (prefixWord ++ tailWord_7513816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513816).length < 2 ^ (prefixWord ++ tailWord_7513816).sum := by decide
  have hdescent : baseEnd_7513816 < baseStart_7513816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513821 : List Nat := [1, 4, 3, 3, 1, 2, 2, 1, 1, 3, 2]
def baseStart_7513821 : Nat := 118140960795 + 7513821 * 2 ^ 59
def prefixEnd_7513821 : Nat := 4983230072969 + 3 ^ 40 * 7513821 * 2
def baseEnd_7513821 : Nat := 3858201724846551874482073

theorem tailTrace_7513821 : CollatzResearch.WordTrace tailWord_7513821 prefixEnd_7513821 3858201724846551874482073 := by
  unfold tailWord_7513821
  simp only [CollatzResearch.WordTrace]
  refine ⟨274051566111717250306485317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182701044074478166870990211 274051566111717250306485317)
  ·
    refine ⟨51384668645946984432465997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274051566111717250306485317 51384668645946984432465997)
    ·
      refine ⟨19269250742230119162174749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51384668645946984432465997 19269250742230119162174749)
      ·
        refine ⟨7225969028336294685815531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19269250742230119162174749 7225969028336294685815531)
        ·
          refine ⟨10838953542504442028723297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7225969028336294685815531 10838953542504442028723297)
          ·
            refine ⟨8129215156878331521542473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10838953542504442028723297 8129215156878331521542473)
            ·
              refine ⟨6096911367658748641156855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8129215156878331521542473 6096911367658748641156855)
              ·
                refine ⟨9145367051488122961735283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6096911367658748641156855 9145367051488122961735283)
                ·
                  refine ⟨13718050577232184442602925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9145367051488122961735283 13718050577232184442602925)
                  ·
                    refine ⟨5144268966462069165976097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13718050577232184442602925 5144268966462069165976097)
                    ·
                      refine ⟨3858201724846551874482073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5144268966462069165976097 3858201724846551874482073)
                      ·
                        rfl

theorem cell23_7513821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_7513821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513821 prefixEnd_7513821 := by exact prefixLift 7513821
  have htrace : WordTrace (prefixWord ++ tailWord_7513821) baseStart_7513821 baseEnd_7513821 := by
    simpa [prefixWord, tailWord_7513821, baseEnd_7513821] using wordTrace_append hprefix tailTrace_7513821
  have hstable : (prefixWord ++ tailWord_7513821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513821).length < 2 ^ (prefixWord ++ tailWord_7513821).sum := by decide
  have hdescent : baseEnd_7513821 < baseStart_7513821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513823 : List Nat := [1, 1, 2, 3, 2, 2, 4, 3, 5]
def baseStart_7513823 : Nat := 118140960795 + 7513823 * 2 ^ 59
def prefixEnd_7513823 : Nat := 4983230072969 + 3 ^ 40 * 7513823 * 2
def baseEnd_7513823 : Nat := 428689194645317874073007

theorem tailTrace_7513823 : CollatzResearch.WordTrace tailWord_7513823 prefixEnd_7513823 428689194645317874073007 := by
  unfold tailWord_7513823
  simp only [CollatzResearch.WordTrace]
  refine ⟨274051639057710004648058123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182701092705140003098705415 274051639057710004648058123)
  ·
    refine ⟨411077458586565006972087185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274051639057710004648058123 411077458586565006972087185)
    ·
      refine ⟨308308093939923755229065389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411077458586565006972087185 308308093939923755229065389)
      ·
        refine ⟨115615535227471408210899521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308308093939923755229065389 115615535227471408210899521)
        ·
          refine ⟨86711651420603556158174641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115615535227471408210899521 86711651420603556158174641)
          ·
            refine ⟨65033738565452667118630981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86711651420603556158174641 65033738565452667118630981)
            ·
              refine ⟨12193825981022375084743309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65033738565452667118630981 12193825981022375084743309)
              ·
                refine ⟨4572684742883390656778741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12193825981022375084743309 4572684742883390656778741)
                ·
                  refine ⟨428689194645317874073007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4572684742883390656778741 428689194645317874073007)
                  ·
                    rfl

theorem cell23_7513823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 5].length) (baseStart_7513823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513823 prefixEnd_7513823 := by exact prefixLift 7513823
  have htrace : WordTrace (prefixWord ++ tailWord_7513823) baseStart_7513823 baseEnd_7513823 := by
    simpa [prefixWord, tailWord_7513823, baseEnd_7513823] using wordTrace_append hprefix tailTrace_7513823
  have hstable : (prefixWord ++ tailWord_7513823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513823).length < 2 ^ (prefixWord ++ tailWord_7513823).sum := by decide
  have hdescent : baseEnd_7513823 < baseStart_7513823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513836 : List Nat := [2, 2, 1, 1, 2, 2, 2, 4, 2, 5]
def baseStart_7513836 : Nat := 118140960795 + 7513836 * 2 ^ 59
def prefixEnd_7513836 : Nat := 4983230072969 + 3 ^ 40 * 7513836 * 2
def baseEnd_7513836 : Nat := 1286069809018789771931501

theorem tailTrace_7513836 : CollatzResearch.WordTrace tailWord_7513836 prefixEnd_7513836 1286069809018789771931501 := by
  unfold tailWord_7513836
  simp only [CollatzResearch.WordTrace]
  refine ⟨137026056603331453934140681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182701408804441938578854241 137026056603331453934140681)
  ·
    refine ⟨102769542452498590450605511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137026056603331453934140681 102769542452498590450605511)
    ·
      refine ⟨154154313678747885675908267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102769542452498590450605511 154154313678747885675908267)
      ·
        refine ⟨231231470518121828513862401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154154313678747885675908267 231231470518121828513862401)
        ·
          refine ⟨173423602888591371385396801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231231470518121828513862401 173423602888591371385396801)
          ·
            refine ⟨130067702166443528539047601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173423602888591371385396801 130067702166443528539047601)
            ·
              refine ⟨97550776624832646404285701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130067702166443528539047601 97550776624832646404285701)
              ·
                refine ⟨18290770617156121200803569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97550776624832646404285701 18290770617156121200803569)
                ·
                  refine ⟨13718077962867090900602677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18290770617156121200803569 13718077962867090900602677)
                  ·
                    refine ⟨1286069809018789771931501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13718077962867090900602677 1286069809018789771931501)
                    ·
                      rfl

theorem cell23_7513836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_7513836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513836 prefixEnd_7513836 := by exact prefixLift 7513836
  have htrace : WordTrace (prefixWord ++ tailWord_7513836) baseStart_7513836 baseEnd_7513836 := by
    simpa [prefixWord, tailWord_7513836, baseEnd_7513836] using wordTrace_append hprefix tailTrace_7513836
  have hstable : (prefixWord ++ tailWord_7513836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513836).length < 2 ^ (prefixWord ++ tailWord_7513836).sum := by decide
  have hdescent : baseEnd_7513836 < baseStart_7513836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513856 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 4]
def baseStart_7513856 : Nat := 118140960795 + 7513856 * 2 ^ 59
def prefixEnd_7513856 : Nat := 4983230072969 + 3 ^ 40 * 7513856 * 2
def baseEnd_7513856 : Nat := 3858219696669459237544411

theorem tailTrace_7513856 : CollatzResearch.WordTrace tailWord_7513856 prefixEnd_7513856 3858219696669459237544411 := by
  unfold tailWord_7513856
  simp only [CollatzResearch.WordTrace]
  refine ⟨137026421333295225642004711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182701895111060300856006281 137026421333295225642004711)
  ·
    refine ⟨205539631999942838463007067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137026421333295225642004711 205539631999942838463007067)
    ·
      refine ⟨308309447999914257694510601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205539631999942838463007067 308309447999914257694510601)
      ·
        refine ⟨231232085999935693270882951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308309447999914257694510601 231232085999935693270882951)
        ·
          refine ⟨346848128999903539906324427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231232085999935693270882951 346848128999903539906324427)
          ·
            refine ⟨520272193499855309859486641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346848128999903539906324427 520272193499855309859486641)
            ·
              refine ⟨390204145124891482394614981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520272193499855309859486641 390204145124891482394614981)
              ·
                refine ⟨73163277210917152948990309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 390204145124891482394614981 73163277210917152948990309)
                ·
                  refine ⟨13718114477046966177935683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73163277210917152948990309 13718114477046966177935683)
                  ·
                    refine ⟨20577171715570449266903525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13718114477046966177935683 20577171715570449266903525)
                    ·
                      refine ⟨3858219696669459237544411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20577171715570449266903525 3858219696669459237544411)
                      ·
                        rfl

theorem cell23_7513856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_7513856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513856 prefixEnd_7513856 := by exact prefixLift 7513856
  have htrace : WordTrace (prefixWord ++ tailWord_7513856) baseStart_7513856 baseEnd_7513856 := by
    simpa [prefixWord, tailWord_7513856, baseEnd_7513856] using wordTrace_append hprefix tailTrace_7513856
  have hstable : (prefixWord ++ tailWord_7513856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513856).length < 2 ^ (prefixWord ++ tailWord_7513856).sum := by decide
  have hdescent : baseEnd_7513856 < baseStart_7513856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513893 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 4, 2, 3]
def baseStart_7513893 : Nat := 118140960795 + 7513893 * 2 ^ 59
def prefixEnd_7513893 : Nat := 4983230072969 + 3 ^ 40 * 7513893 * 2
def baseEnd_7513893 : Nat := 3858238695453675592781741

theorem tailTrace_7513893 : CollatzResearch.WordTrace tailWord_7513893 prefixEnd_7513893 3858238695453675592781741 := by
  unfold tailWord_7513893
  simp only [CollatzResearch.WordTrace]
  refine ⟨274054192167456406603106333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182702794778304271068737555 274054192167456406603106333)
  ·
    refine ⟨102770322062796152476164875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274054192167456406603106333 102770322062796152476164875)
    ·
      refine ⟨154155483094194228714247313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102770322062796152476164875 154155483094194228714247313)
      ·
        refine ⟨115616612320645671535685485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154155483094194228714247313 115616612320645671535685485)
        ·
          refine ⟨43356229620242126825882057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115616612320645671535685485 43356229620242126825882057)
          ·
            refine ⟨32517172215181595119411543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43356229620242126825882057 32517172215181595119411543)
            ·
              refine ⟨48775758322772392679117315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32517172215181595119411543 48775758322772392679117315)
              ·
                refine ⟨73163637484158589018675973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48775758322772392679117315 73163637484158589018675973)
                ·
                  refine ⟨13718182028279735441001745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73163637484158589018675973 13718182028279735441001745)
                  ·
                    refine ⟨10288636521209801580751309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13718182028279735441001745 10288636521209801580751309)
                    ·
                      refine ⟨3858238695453675592781741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10288636521209801580751309 3858238695453675592781741)
                      ·
                        rfl

theorem cell23_7513893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_7513893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513893 prefixEnd_7513893 := by exact prefixLift 7513893
  have htrace : WordTrace (prefixWord ++ tailWord_7513893) baseStart_7513893 baseEnd_7513893 := by
    simpa [prefixWord, tailWord_7513893, baseEnd_7513893] using wordTrace_append hprefix tailTrace_7513893
  have hstable : (prefixWord ++ tailWord_7513893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513893).length < 2 ^ (prefixWord ++ tailWord_7513893).sum := by decide
  have hdescent : baseEnd_7513893 < baseStart_7513893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513900 : List Nat := [2, 2, 1, 1, 1, 7, 1, 1, 3, 4]
def baseStart_7513900 : Nat := 118140960795 + 7513900 * 2 ^ 59
def prefixEnd_7513900 : Nat := 4983230072969 + 3 ^ 40 * 7513900 * 2
def baseEnd_7513900 : Nat := 1286080763272752355131403

theorem tailTrace_7513900 : CollatzResearch.WordTrace tailWord_7513900 prefixEnd_7513900 1286080763272752355131403 := by
  unfold tailWord_7513900
  simp only [CollatzResearch.WordTrace]
  refine ⟨137027223739215523399305577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182702964985620697865740769 137027223739215523399305577)
  ·
    refine ⟨102770417804411642549479183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137027223739215523399305577 102770417804411642549479183)
    ·
      refine ⟨154155626706617463824218775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102770417804411642549479183 154155626706617463824218775)
      ·
        refine ⟨231233440059926195736328163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154155626706617463824218775 231233440059926195736328163)
        ·
          refine ⟨346850160089889293604492245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231233440059926195736328163 346850160089889293604492245)
          ·
            refine ⟨8129300627106780318855287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 346850160089889293604492245 8129300627106780318855287)
            ·
              refine ⟨12193950940660170478282931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8129300627106780318855287 12193950940660170478282931)
              ·
                refine ⟨18290926410990255717424397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12193950940660170478282931 18290926410990255717424397)
                ·
                  refine ⟨6859097404121345894034149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18290926410990255717424397 6859097404121345894034149)
                  ·
                    refine ⟨1286080763272752355131403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6859097404121345894034149 1286080763272752355131403)
                    ·
                      rfl

theorem cell23_7513900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 4].length) (baseStart_7513900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513900 prefixEnd_7513900 := by exact prefixLift 7513900
  have htrace : WordTrace (prefixWord ++ tailWord_7513900) baseStart_7513900 baseEnd_7513900 := by
    simpa [prefixWord, tailWord_7513900, baseEnd_7513900] using wordTrace_append hprefix tailTrace_7513900
  have hstable : (prefixWord ++ tailWord_7513900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513900).length < 2 ^ (prefixWord ++ tailWord_7513900).sum := by decide
  have hdescent : baseEnd_7513900 < baseStart_7513900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513916 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_7513916 : Nat := 118140960795 + 7513916 * 2 ^ 59
def prefixEnd_7513916 : Nat := 4983230072969 + 3 ^ 40 * 7513916 * 2
def baseEnd_7513916 : Nat := 3858250505508729002794135

theorem tailTrace_7513916 : CollatzResearch.WordTrace tailWord_7513916 prefixEnd_7513916 3858250505508729002794135 := by
  unfold tailWord_7513916
  simp only [CollatzResearch.WordTrace]
  refine ⟨137027515523186540765596801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182703354030915387687462401 137027515523186540765596801)
  ·
    refine ⟨102770636642389905574197601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137027515523186540765596801 102770636642389905574197601)
    ·
      refine ⟨77077977481792429180648201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102770636642389905574197601 77077977481792429180648201)
      ·
        refine ⟨57808483111344321885486151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77077977481792429180648201 57808483111344321885486151)
        ·
          refine ⟨86712724667016482828229227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57808483111344321885486151 86712724667016482828229227)
          ·
            refine ⟨130069087000524724242343841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86712724667016482828229227 130069087000524724242343841)
            ·
              refine ⟨97551815250393543181757881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130069087000524724242343841 97551815250393543181757881)
              ·
                refine ⟨73163861437795157386318411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97551815250393543181757881 73163861437795157386318411)
                ·
                  refine ⟨109745792156692736079477617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73163861437795157386318411 109745792156692736079477617)
                  ·
                    refine ⟨82309344117519552059608213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109745792156692736079477617 82309344117519552059608213)
                    ·
                      refine ⟨3858250505508729002794135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82309344117519552059608213 3858250505508729002794135)
                      ·
                        rfl

theorem cell23_7513916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_7513916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513916 prefixEnd_7513916 := by exact prefixLift 7513916
  have htrace : WordTrace (prefixWord ++ tailWord_7513916) baseStart_7513916 baseEnd_7513916 := by
    simpa [prefixWord, tailWord_7513916, baseEnd_7513916] using wordTrace_append hprefix tailTrace_7513916
  have hstable : (prefixWord ++ tailWord_7513916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513916).length < 2 ^ (prefixWord ++ tailWord_7513916).sum := by decide
  have hdescent : baseEnd_7513916 < baseStart_7513916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513963 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 2, 6, 2]
def baseStart_7513963 : Nat := 118140960795 + 7513963 * 2 ^ 59
def prefixEnd_7513963 : Nat := 4983230072969 + 3 ^ 40 * 7513963 * 2
def baseEnd_7513963 : Nat := 3858274639099490318906419

theorem tailTrace_7513963 : CollatzResearch.WordTrace tailWord_7513963 prefixEnd_7513963 3858274639099490318906419 := by
  unfold tailWord_7513963
  simp only [CollatzResearch.WordTrace]
  refine ⟨274056745277202808558154543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182704496851468539038769695 274056745277202808558154543)
  ·
    refine ⟨411085117915804212837231815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274056745277202808558154543 411085117915804212837231815)
    ·
      refine ⟨616627676873706319255847723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411085117915804212837231815 616627676873706319255847723)
      ·
        refine ⟨924941515310559478883771585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616627676873706319255847723 924941515310559478883771585)
        ·
          refine ⟨693706136482919609162828689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 924941515310559478883771585 693706136482919609162828689)
          ·
            refine ⟨520279602362189706872121517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 693706136482919609162828689 520279602362189706872121517)
            ·
              refine ⟨195104850885821140077045569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 520279602362189706872121517 195104850885821140077045569)
              ·
                refine ⟨146328638164365855057784177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195104850885821140077045569 146328638164365855057784177)
                ·
                  refine ⟨109746478623274391293338133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146328638164365855057784177 109746478623274391293338133)
                  ·
                    refine ⟨5144366185465987091875225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109746478623274391293338133 5144366185465987091875225)
                    ·
                      refine ⟨3858274639099490318906419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5144366185465987091875225 3858274639099490318906419)
                      ·
                        rfl

theorem cell23_7513963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 6, 2].length) (baseStart_7513963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513963 prefixEnd_7513963 := by exact prefixLift 7513963
  have htrace : WordTrace (prefixWord ++ tailWord_7513963) baseStart_7513963 baseEnd_7513963 := by
    simpa [prefixWord, tailWord_7513963, baseEnd_7513963] using wordTrace_append hprefix tailTrace_7513963
  have hstable : (prefixWord ++ tailWord_7513963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513963).length < 2 ^ (prefixWord ++ tailWord_7513963).sum := by decide
  have hdescent : baseEnd_7513963 < baseStart_7513963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513974 : List Nat := [5, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3]
def baseStart_7513974 : Nat := 118140960795 + 7513974 * 2 ^ 59
def prefixEnd_7513974 : Nat := 4983230072969 + 3 ^ 40 * 7513974 * 2
def baseEnd_7513974 : Nat := 3858280287386689775868869

theorem tailTrace_7513974 : CollatzResearch.WordTrace tailWord_7513974 prefixEnd_7513974 3858280287386689775868869 := by
  unfold tailWord_7513974
  simp only [CollatzResearch.WordTrace]
  refine ⟨17128571655010184839800311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182704764320108638291203317 17128571655010184839800311)
  ·
    refine ⟨25692857482515277259700467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17128571655010184839800311 25692857482515277259700467)
    ·
      refine ⟨38539286223772915889550701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25692857482515277259700467 38539286223772915889550701)
      ·
        refine ⟨14452232333914843458581513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38539286223772915889550701 14452232333914843458581513)
        ·
          refine ⟨10839174250436132593936135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14452232333914843458581513 10839174250436132593936135)
          ·
            refine ⟨16258761375654198890904203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10839174250436132593936135 16258761375654198890904203)
            ·
              refine ⟨24388142063481298336356305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16258761375654198890904203 24388142063481298336356305)
              ·
                refine ⟨18291106547610973752267229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24388142063481298336356305 18291106547610973752267229)
                ·
                  refine ⟨6859164955354115157100211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18291106547610973752267229 6859164955354115157100211)
                  ·
                    refine ⟨10288747433031172735650317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6859164955354115157100211 10288747433031172735650317)
                    ·
                      refine ⟨3858280287386689775868869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10288747433031172735650317 3858280287386689775868869)
                      ·
                        rfl

theorem cell23_7513974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_7513974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513974 prefixEnd_7513974 := by exact prefixLift 7513974
  have htrace : WordTrace (prefixWord ++ tailWord_7513974) baseStart_7513974 baseEnd_7513974 := by
    simpa [prefixWord, tailWord_7513974, baseEnd_7513974] using wordTrace_append hprefix tailTrace_7513974
  have hstable : (prefixWord ++ tailWord_7513974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513974).length < 2 ^ (prefixWord ++ tailWord_7513974).sum := by decide
  have hdescent : baseEnd_7513974 < baseStart_7513974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513976 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 5, 1, 6]
def baseStart_7513976 : Nat := 118140960795 + 7513976 * 2 ^ 59
def prefixEnd_7513976 : Nat := 4983230072969 + 3 ^ 40 * 7513976 * 2
def baseEnd_7513976 : Nat := 3858281314347998768043859

theorem tailTrace_7513976 : CollatzResearch.WordTrace tailWord_7513976 prefixEnd_7513976 3858281314347998768043859 := by
  unfold tailWord_7513976
  simp only [CollatzResearch.WordTrace]
  refine ⟨137028609713077855889188891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182704812950770474518918521 137028609713077855889188891)
  ·
    refine ⟨205542914569616783833783337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137028609713077855889188891 205542914569616783833783337)
    ·
      refine ⟨154157185927212587875337503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205542914569616783833783337 154157185927212587875337503)
      ·
        refine ⟨231235778890818881813006255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154157185927212587875337503 231235778890818881813006255)
        ·
          refine ⟨346853668336228322719509383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231235778890818881813006255 346853668336228322719509383)
          ·
            refine ⟨520280502504342484079264075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346853668336228322719509383 520280502504342484079264075)
            ·
              refine ⟨780420753756513726118896113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520280502504342484079264075 780420753756513726118896113)
              ·
                refine ⟨585315565317385294589172085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780420753756513726118896113 585315565317385294589172085)
                ·
                  refine ⟨54873334248504871367734883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 585315565317385294589172085 54873334248504871367734883)
                  ·
                    refine ⟨82310001372757307051602325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54873334248504871367734883 82310001372757307051602325)
                    ·
                      refine ⟨3858281314347998768043859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82310001372757307051602325 3858281314347998768043859)
                      ·
                        rfl

theorem cell23_7513976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_7513976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513976 prefixEnd_7513976 := by exact prefixLift 7513976
  have htrace : WordTrace (prefixWord ++ tailWord_7513976) baseStart_7513976 baseEnd_7513976 := by
    simpa [prefixWord, tailWord_7513976, baseEnd_7513976] using wordTrace_append hprefix tailTrace_7513976
  have hstable : (prefixWord ++ tailWord_7513976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513976).length < 2 ^ (prefixWord ++ tailWord_7513976).sum := by decide
  have hdescent : baseEnd_7513976 < baseStart_7513976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513993 : List Nat := [1, 2, 1, 1, 5, 1, 1, 4, 1, 2, 4]
def baseStart_7513993 : Nat := 118140960795 + 7513993 * 2 ^ 59
def prefixEnd_7513993 : Nat := 4983230072969 + 3 ^ 40 * 7513993 * 2
def baseEnd_7513993 : Nat := 3858290043519125201531281

theorem tailTrace_7513993 : CollatzResearch.WordTrace tailWord_7513993 prefixEnd_7513993 3858290043519125201531281 := by
  unfold tailWord_7513993
  simp only [CollatzResearch.WordTrace]
  refine ⟨274057839467094123681746633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182705226311396082454497755 274057839467094123681746633)
  ·
    refine ⟨205543379600320592761309975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274057839467094123681746633 205543379600320592761309975)
    ·
      refine ⟨308315069400480889141964963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205543379600320592761309975 308315069400480889141964963)
      ·
        refine ⟨462472604100721333712947445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308315069400480889141964963 462472604100721333712947445)
        ·
          refine ⟨43356806634442625035588823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 462472604100721333712947445 43356806634442625035588823)
          ·
            refine ⟨65035209951663937553383235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43356806634442625035588823 65035209951663937553383235)
            ·
              refine ⟨97552814927495906330074853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65035209951663937553383235 97552814927495906330074853)
              ·
                refine ⟨18291152798905482436889035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97552814927495906330074853 18291152798905482436889035)
                ·
                  refine ⟨27436729198358223655333553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18291152798905482436889035 27436729198358223655333553)
                  ·
                    refine ⟨20577546898768667741500165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27436729198358223655333553 20577546898768667741500165)
                    ·
                      refine ⟨3858290043519125201531281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20577546898768667741500165 3858290043519125201531281)
                      ·
                        rfl

theorem cell23_7513993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 2, 4].length) (baseStart_7513993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513993 prefixEnd_7513993 := by exact prefixLift 7513993
  have htrace : WordTrace (prefixWord ++ tailWord_7513993) baseStart_7513993 baseEnd_7513993 := by
    simpa [prefixWord, tailWord_7513993, baseEnd_7513993] using wordTrace_append hprefix tailTrace_7513993
  have hstable : (prefixWord ++ tailWord_7513993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513993).length < 2 ^ (prefixWord ++ tailWord_7513993).sum := by decide
  have hdescent : baseEnd_7513993 < baseStart_7513993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7513994 : List Nat := [3, 1, 2, 4, 2, 2, 2, 1, 1, 5]
def baseStart_7513994 : Nat := 118140960795 + 7513994 * 2 ^ 59
def prefixEnd_7513994 : Nat := 4983230072969 + 3 ^ 40 * 7513994 * 2
def baseEnd_7513994 : Nat := 1286096852333259899206259

theorem tailTrace_7513994 : CollatzResearch.WordTrace tailWord_7513994 prefixEnd_7513994 1286096852333259899206259 := by
  unfold tailWord_7513994
  simp only [CollatzResearch.WordTrace]
  refine ⟨68514468985022625213133259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182705250626727000568355357 68514468985022625213133259)
  ·
    refine ⟨102771703477533937819699889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68514468985022625213133259 102771703477533937819699889)
    ·
      refine ⟨77078777608150453364774917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102771703477533937819699889 77078777608150453364774917)
      ·
        refine ⟨14452270801528210005895297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77078777608150453364774917 14452270801528210005895297)
        ·
          refine ⟨10839203101146157504421473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14452270801528210005895297 10839203101146157504421473)
          ·
            refine ⟨8129402325859618128316105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10839203101146157504421473 8129402325859618128316105)
            ·
              refine ⟨6097051744394713596237079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8129402325859618128316105 6097051744394713596237079)
              ·
                refine ⟨9145577616592070394355619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6097051744394713596237079 9145577616592070394355619)
                ·
                  refine ⟨13718366424888105591533429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9145577616592070394355619 13718366424888105591533429)
                  ·
                    refine ⟨1286096852333259899206259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13718366424888105591533429 1286096852333259899206259)
                    ·
                      rfl

theorem cell23_7513994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_7513994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7513994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7513994 prefixEnd_7513994 := by exact prefixLift 7513994
  have htrace : WordTrace (prefixWord ++ tailWord_7513994) baseStart_7513994 baseEnd_7513994 := by
    simpa [prefixWord, tailWord_7513994, baseEnd_7513994] using wordTrace_append hprefix tailTrace_7513994
  have hstable : (prefixWord ++ tailWord_7513994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7513994).length < 2 ^ (prefixWord ++ tailWord_7513994).sum := by decide
  have hdescent : baseEnd_7513994 < baseStart_7513994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7513994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514007 : List Nat := [1, 1, 3, 3, 1, 5, 1, 2, 2, 4]
def baseStart_7514007 : Nat := 118140960795 + 7514007 * 2 ^ 59
def prefixEnd_7514007 : Nat := 4983230072969 + 3 ^ 40 * 7514007 * 2
def baseEnd_7514007 : Nat := 1286099077416096048918739

theorem tailTrace_7514007 : CollatzResearch.WordTrace tailWord_7514007 prefixEnd_7514007 1286099077416096048918739 := by
  unfold tailWord_7514007
  simp only [CollatzResearch.WordTrace]
  refine ⟨274058350089043404072756275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182705566726028936048504183 274058350089043404072756275)
  ·
    refine ⟨411087525133565106109134413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274058350089043404072756275 411087525133565106109134413)
    ·
      refine ⟨154157821925086914790925405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411087525133565106109134413 154157821925086914790925405)
      ·
        refine ⟨57809183221907593046597027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154157821925086914790925405 57809183221907593046597027)
        ·
          refine ⟨86713774832861389569895541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57809183221907593046597027 86713774832861389569895541)
          ·
            refine ⟨8129416390580755272177707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86713774832861389569895541 8129416390580755272177707)
            ·
              refine ⟨12194124585871132908266561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8129416390580755272177707 12194124585871132908266561)
              ·
                refine ⟨9145593439403349681199921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12194124585871132908266561 9145593439403349681199921)
                ·
                  refine ⟨6859195079552512260899941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9145593439403349681199921 6859195079552512260899941)
                  ·
                    refine ⟨1286099077416096048918739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6859195079552512260899941 1286099077416096048918739)
                    ·
                      rfl

theorem cell23_7514007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 4].length) (baseStart_7514007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514007 prefixEnd_7514007 := by exact prefixLift 7514007
  have htrace : WordTrace (prefixWord ++ tailWord_7514007) baseStart_7514007 baseEnd_7514007 := by
    simpa [prefixWord, tailWord_7514007, baseEnd_7514007] using wordTrace_append hprefix tailTrace_7514007
  have hstable : (prefixWord ++ tailWord_7514007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514007).length < 2 ^ (prefixWord ++ tailWord_7514007).sum := by decide
  have hdescent : baseEnd_7514007 < baseStart_7514007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514024 : List Nat := [2, 1, 6, 2, 1, 2, 1, 1, 1, 6]
def baseStart_7514024 : Nat := 118140960795 + 7514024 * 2 ^ 59
def prefixEnd_7514024 : Nat := 4983230072969 + 3 ^ 40 * 7514024 * 2
def baseEnd_7514024 : Nat := 1286101987139804860081213

theorem tailTrace_7514024 : CollatzResearch.WordTrace tailWord_7514024 prefixEnd_7514024 1286101987139804860081213 := by
  unfold tailWord_7514024
  simp only [CollatzResearch.WordTrace]
  refine ⟨137029485064990907988062563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182705980086654543984083417 137029485064990907988062563)
  ·
    refine ⟨205544227597486361982093845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137029485064990907988062563 205544227597486361982093845)
    ·
      refine ⟨9634885668632173217910649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 205544227597486361982093845 9634885668632173217910649)
      ·
        refine ⟨7226164251474129913432987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9634885668632173217910649 7226164251474129913432987)
        ·
          refine ⟨10839246377211194870149481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7226164251474129913432987 10839246377211194870149481)
          ·
            refine ⟨8129434782908396152612111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10839246377211194870149481 8129434782908396152612111)
            ·
              refine ⟨12194152174362594228918167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8129434782908396152612111 12194152174362594228918167)
              ·
                refine ⟨18291228261543891343377251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12194152174362594228918167 18291228261543891343377251)
                ·
                  refine ⟨27436842392315837015065877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18291228261543891343377251 27436842392315837015065877)
                  ·
                    refine ⟨1286101987139804860081213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27436842392315837015065877 1286101987139804860081213)
                    ·
                      rfl

theorem cell23_7514024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_7514024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514024 prefixEnd_7514024 := by exact prefixLift 7514024
  have htrace : WordTrace (prefixWord ++ tailWord_7514024) baseStart_7514024 baseEnd_7514024 := by
    simpa [prefixWord, tailWord_7514024, baseEnd_7514024] using wordTrace_append hprefix tailTrace_7514024
  have hstable : (prefixWord ++ tailWord_7514024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514024).length < 2 ^ (prefixWord ++ tailWord_7514024).sum := by decide
  have hdescent : baseEnd_7514024 < baseStart_7514024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514120 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 2, 3, 3]
def baseStart_7514120 : Nat := 118140960795 + 7514120 * 2 ^ 59
def prefixEnd_7514120 : Nat := 4983230072969 + 3 ^ 40 * 7514120 * 2
def baseEnd_7514120 : Nat := 3858355255562246204643197

theorem tailTrace_7514120 : CollatzResearch.WordTrace tailWord_7514120 prefixEnd_7514120 3858355255562246204643197 := by
  unfold tailWord_7514120
  simp only [CollatzResearch.WordTrace]
  refine ⟨137031235768817012185809907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182708314358422682914413209 137031235768817012185809907)
  ·
    refine ⟨205546853653225518278714861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137031235768817012185809907 205546853653225518278714861)
    ·
      refine ⟨77080070119959569354518073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205546853653225518278714861 77080070119959569354518073)
      ·
        refine ⟨57810052589969677015888555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77080070119959569354518073 57810052589969677015888555)
        ·
          refine ⟨86715078884954515523832833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57810052589969677015888555 86715078884954515523832833)
          ·
            refine ⟨65036309163715886642874625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86715078884954515523832833 65036309163715886642874625)
            ·
              refine ⟨48777231872786914982155969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65036309163715886642874625 48777231872786914982155969)
              ·
                refine ⟨36582923904590186236616977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48777231872786914982155969 36582923904590186236616977)
                ·
                  refine ⟨27437192928442639677462733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36582923904590186236616977 27437192928442639677462733)
                  ·
                    refine ⟨10288947348165989879048525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27437192928442639677462733 10288947348165989879048525)
                    ·
                      refine ⟨3858355255562246204643197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10288947348165989879048525 3858355255562246204643197)
                      ·
                        rfl

theorem cell23_7514120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_7514120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514120 prefixEnd_7514120 := by exact prefixLift 7514120
  have htrace : WordTrace (prefixWord ++ tailWord_7514120) baseStart_7514120 baseEnd_7514120 := by
    simpa [prefixWord, tailWord_7514120, baseEnd_7514120] using wordTrace_append hprefix tailTrace_7514120
  have hstable : (prefixWord ++ tailWord_7514120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514120).length < 2 ^ (prefixWord ++ tailWord_7514120).sum := by decide
  have hdescent : baseEnd_7514120 < baseStart_7514120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514160 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 4]
def baseStart_7514160 : Nat := 118140960795 + 7514160 * 2 ^ 59
def prefixEnd_7514160 : Nat := 4983230072969 + 3 ^ 40 * 7514160 * 2
def baseEnd_7514160 : Nat := 3858375794788426048143013

theorem tailTrace_7514160 : CollatzResearch.WordTrace tailWord_7514160 prefixEnd_7514160 3858375794788426048143013 := by
  unfold tailWord_7514160
  simp only [CollatzResearch.WordTrace]
  refine ⟨137031965228744555601537967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182709286971659407468717289 137031965228744555601537967)
  ·
    refine ⟨205547947843116833402306951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137031965228744555601537967 205547947843116833402306951)
    ·
      refine ⟨308321921764675250103460427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205547947843116833402306951 308321921764675250103460427)
      ·
        refine ⟨462482882647012875155190641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308321921764675250103460427 462482882647012875155190641)
        ·
          refine ⟨346862161985259656366392981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462482882647012875155190641 346862161985259656366392981)
          ·
            refine ⟨16259163843059046392174671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 346862161985259656366392981 16259163843059046392174671)
            ·
              refine ⟨24388745764588569588262007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16259163843059046392174671 24388745764588569588262007)
              ·
                refine ⟨36583118646882854382393011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24388745764588569588262007 36583118646882854382393011)
                ·
                  refine ⟨54874677970324281573589517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36583118646882854382393011 54874677970324281573589517)
                  ·
                    refine ⟨20578004238871605590096069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54874677970324281573589517 20578004238871605590096069)
                    ·
                      refine ⟨3858375794788426048143013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20578004238871605590096069 3858375794788426048143013)
                      ·
                        rfl

theorem cell23_7514160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 4].length) (baseStart_7514160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514160 prefixEnd_7514160 := by exact prefixLift 7514160
  have htrace : WordTrace (prefixWord ++ tailWord_7514160) baseStart_7514160 baseEnd_7514160 := by
    simpa [prefixWord, tailWord_7514160, baseEnd_7514160] using wordTrace_append hprefix tailTrace_7514160
  have hstable : (prefixWord ++ tailWord_7514160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514160).length < 2 ^ (prefixWord ++ tailWord_7514160).sum := by decide
  have hdescent : baseEnd_7514160 < baseStart_7514160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514170 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 7, 4]
def baseStart_7514170 : Nat := 118140960795 + 7514170 * 2 ^ 59
def prefixEnd_7514170 : Nat := 4983230072969 + 3 ^ 40 * 7514170 * 2
def baseEnd_7514170 : Nat := 1286126976531657003005989

theorem tailTrace_7514170 : CollatzResearch.WordTrace tailWord_7514170 prefixEnd_7514170 1286126976531657003005989 := by
  unfold tailWord_7514170
  simp only [CollatzResearch.WordTrace]
  refine ⟨68516073796863220727734991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182709530124968588607293309 68516073796863220727734991)
  ·
    refine ⟨102774110695294831091602487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68516073796863220727734991 102774110695294831091602487)
    ·
      refine ⟨154161166042942246637403731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102774110695294831091602487 154161166042942246637403731)
      ·
        refine ⟨231241749064413369956105597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154161166042942246637403731 231241749064413369956105597)
        ·
          refine ⟨86715655899155013733539599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231241749064413369956105597 86715655899155013733539599)
          ·
            refine ⟨130073483848732520600309399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86715655899155013733539599 130073483848732520600309399)
            ·
              refine ⟨195110225773098780900464099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130073483848732520600309399 195110225773098780900464099)
              ·
                refine ⟨292665338659648171350696149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195110225773098780900464099 292665338659648171350696149)
                ·
                  refine ⟨6859343874835504016031941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 292665338659648171350696149 6859343874835504016031941)
                  ·
                    refine ⟨1286126976531657003005989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6859343874835504016031941 1286126976531657003005989)
                    ·
                      rfl

theorem cell23_7514170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 7, 4].length) (baseStart_7514170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514170 prefixEnd_7514170 := by exact prefixLift 7514170
  have htrace : WordTrace (prefixWord ++ tailWord_7514170) baseStart_7514170 baseEnd_7514170 := by
    simpa [prefixWord, tailWord_7514170, baseEnd_7514170] using wordTrace_append hprefix tailTrace_7514170
  have hstable : (prefixWord ++ tailWord_7514170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514170).length < 2 ^ (prefixWord ++ tailWord_7514170).sum := by decide
  have hdescent : baseEnd_7514170 < baseStart_7514170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514271 : List Nat := [1, 1, 2, 6, 1, 2, 2, 1, 2, 3, 2]
def baseStart_7514271 : Nat := 118140960795 + 7514271 * 2 ^ 59
def prefixEnd_7514271 : Nat := 4983230072969 + 3 ^ 40 * 7514271 * 2
def baseEnd_7514271 : Nat := 3858432791141075113855003

theorem tailTrace_7514271 : CollatzResearch.WordTrace tailWord_7514271 prefixEnd_7514271 3858432791141075113855003 := by
  unfold tailWord_7514271
  simp only [CollatzResearch.WordTrace]
  refine ⟨274067978960086977160366667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182711985973391318106911111 274067978960086977160366667)
  ·
    refine ⟨411101968440130465740550001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274067978960086977160366667 411101968440130465740550001)
    ·
      refine ⟨308326476330097849305412501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411101968440130465740550001 308326476330097849305412501)
      ·
        refine ⟨14452803577973336686191211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 308326476330097849305412501 14452803577973336686191211)
        ·
          refine ⟨21679205366960005029286817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14452803577973336686191211 21679205366960005029286817)
          ·
            refine ⟨16259404025220003771965113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21679205366960005029286817 16259404025220003771965113)
            ·
              refine ⟨12194553018915002828973835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16259404025220003771965113 12194553018915002828973835)
              ·
                refine ⟨18291829528372504243460753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12194553018915002828973835 18291829528372504243460753)
                ·
                  refine ⟨13718872146279378182595565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18291829528372504243460753 13718872146279378182595565)
                  ·
                    refine ⟨5144577054854766818473337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13718872146279378182595565 5144577054854766818473337)
                    ·
                      refine ⟨3858432791141075113855003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5144577054854766818473337 3858432791141075113855003)
                      ·
                        rfl

theorem cell23_7514271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_7514271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514271 prefixEnd_7514271 := by exact prefixLift 7514271
  have htrace : WordTrace (prefixWord ++ tailWord_7514271) baseStart_7514271 baseEnd_7514271 := by
    simpa [prefixWord, tailWord_7514271, baseEnd_7514271] using wordTrace_append hprefix tailTrace_7514271
  have hstable : (prefixWord ++ tailWord_7514271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514271).length < 2 ^ (prefixWord ++ tailWord_7514271).sum := by decide
  have hdescent : baseEnd_7514271 < baseStart_7514271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514351 : List Nat := [1, 1, 2, 1, 6, 1, 3, 2, 2, 1, 3]
def baseStart_7514351 : Nat := 118140960795 + 7514351 * 2 ^ 59
def prefixEnd_7514351 : Nat := 4983230072969 + 3 ^ 40 * 7514351 * 2
def baseEnd_7514351 : Nat := 3858473869593434800854635

theorem tailTrace_7514351 : CollatzResearch.WordTrace tailWord_7514351 prefixEnd_7514351 3858473869593434800854635 := by
  unfold tailWord_7514351
  simp only [CollatzResearch.WordTrace]
  refine ⟨274070896799797150823278907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182713931199864767215519271 274070896799797150823278907)
  ·
    refine ⟨411106345199695726234918361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274070896799797150823278907 411106345199695726234918361)
    ·
      refine ⟨308329758899771794676188771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411106345199695726234918361 308329758899771794676188771)
      ·
        refine ⟨462494638349657692014283157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308329758899771794676188771 462494638349657692014283157)
        ·
          refine ⟨21679436172640204313169523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 462494638349657692014283157 21679436172640204313169523)
          ·
            refine ⟨32519154258960306469754285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21679436172640204313169523 32519154258960306469754285)
            ·
              refine ⟨12194682847110114926157857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32519154258960306469754285 12194682847110114926157857)
              ·
                refine ⟨9146012135332586194618393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12194682847110114926157857 9146012135332586194618393)
                ·
                  refine ⟨6859509101499439645963795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9146012135332586194618393 6859509101499439645963795)
                  ·
                    refine ⟨10289263652249159468945693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6859509101499439645963795 10289263652249159468945693)
                    ·
                      refine ⟨3858473869593434800854635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10289263652249159468945693 3858473869593434800854635)
                      ·
                        rfl

theorem cell23_7514351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 1, 3].length) (baseStart_7514351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514351 prefixEnd_7514351 := by exact prefixLift 7514351
  have htrace : WordTrace (prefixWord ++ tailWord_7514351) baseStart_7514351 baseEnd_7514351 := by
    simpa [prefixWord, tailWord_7514351, baseEnd_7514351] using wordTrace_append hprefix tailTrace_7514351
  have hstable : (prefixWord ++ tailWord_7514351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514351).length < 2 ^ (prefixWord ++ tailWord_7514351).sum := by decide
  have hdescent : baseEnd_7514351 < baseStart_7514351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514391 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 4, 2, 2]
def baseStart_7514391 : Nat := 118140960795 + 7514391 * 2 ^ 59
def prefixEnd_7514391 : Nat := 4983230072969 + 3 ^ 40 * 7514391 * 2
def baseEnd_7514391 : Nat := 3858494408819614644354451

theorem tailTrace_7514391 : CollatzResearch.WordTrace tailWord_7514391 prefixEnd_7514391 3858494408819614644354451 := by
  unfold tailWord_7514391
  simp only [CollatzResearch.WordTrace]
  refine ⟨274072355719652237654735027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182714903813101491769823351 274072355719652237654735027)
  ·
    refine ⟨411108533579478356482102541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274072355719652237654735027 411108533579478356482102541)
    ·
      refine ⟨154165700092304383680788453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411108533579478356482102541 154165700092304383680788453)
      ·
        refine ⟨28906068767307071940147835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154165700092304383680788453 28906068767307071940147835)
        ·
          refine ⟨43359103150960607910221753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28906068767307071940147835 43359103150960607910221753)
          ·
            refine ⟨32519327363220455932666315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43359103150960607910221753 32519327363220455932666315)
            ·
              refine ⟨48778991044830683898999473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32519327363220455932666315 48778991044830683898999473)
              ·
                refine ⟨36584243283623012924249605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48778991044830683898999473 36584243283623012924249605)
                ·
                  refine ⟨6859545615679314923296801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36584243283623012924249605 6859545615679314923296801)
                  ·
                    refine ⟨5144659211759486192472601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6859545615679314923296801 5144659211759486192472601)
                    ·
                      refine ⟨3858494408819614644354451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5144659211759486192472601 3858494408819614644354451)
                      ·
                        rfl

theorem cell23_7514391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_7514391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514391 prefixEnd_7514391 := by exact prefixLift 7514391
  have htrace : WordTrace (prefixWord ++ tailWord_7514391) baseStart_7514391 baseEnd_7514391 := by
    simpa [prefixWord, tailWord_7514391, baseEnd_7514391] using wordTrace_append hprefix tailTrace_7514391
  have hstable : (prefixWord ++ tailWord_7514391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514391).length < 2 ^ (prefixWord ++ tailWord_7514391).sum := by decide
  have hdescent : baseEnd_7514391 < baseStart_7514391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514394 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5]
def baseStart_7514394 : Nat := 118140960795 + 7514394 * 2 ^ 59
def prefixEnd_7514394 : Nat := 4983230072969 + 3 ^ 40 * 7514394 * 2
def baseEnd_7514394 : Nat := 3858495949261578132616937

theorem tailTrace_7514394 : CollatzResearch.WordTrace tailWord_7514394 prefixEnd_7514394 3858495949261578132616937 := by
  unfold tailWord_7514394
  simp only [CollatzResearch.WordTrace]
  refine ⟨68518116284660342291773559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182714976759094246111396157 68518116284660342291773559)
  ·
    refine ⟨102777174426990513437660339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68518116284660342291773559 102777174426990513437660339)
    ·
      refine ⟨154165761640485770156490509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102777174426990513437660339 154165761640485770156490509)
      ·
        refine ⟨57812160615182163808683941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154165761640485770156490509 57812160615182163808683941)
        ·
          refine ⟨10839780115346655714128239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57812160615182163808683941 10839780115346655714128239)
          ·
            refine ⟨16259670173019983571192359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10839780115346655714128239 16259670173019983571192359)
            ·
              refine ⟨24389505259529975356788539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16259670173019983571192359 24389505259529975356788539)
              ·
                refine ⟨36584257889294963035182809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24389505259529975356788539 36584257889294963035182809)
                ·
                  refine ⟨27438193416971222276387107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36584257889294963035182809 27438193416971222276387107)
                  ·
                    refine ⟨41157290125456833414580661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27438193416971222276387107 41157290125456833414580661)
                    ·
                      refine ⟨3858495949261578132616937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41157290125456833414580661 3858495949261578132616937)
                      ·
                        rfl

theorem cell23_7514394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_7514394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514394 prefixEnd_7514394 := by exact prefixLift 7514394
  have htrace : WordTrace (prefixWord ++ tailWord_7514394) baseStart_7514394 baseEnd_7514394 := by
    simpa [prefixWord, tailWord_7514394, baseEnd_7514394] using wordTrace_append hprefix tailTrace_7514394
  have hstable : (prefixWord ++ tailWord_7514394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514394).length < 2 ^ (prefixWord ++ tailWord_7514394).sum := by decide
  have hdescent : baseEnd_7514394 < baseStart_7514394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514425 : List Nat := [1, 2, 1, 6, 1, 1, 4, 1, 2, 2, 2]
def baseStart_7514425 : Nat := 118140960795 + 7514425 * 2 ^ 59
def prefixEnd_7514425 : Nat := 4983230072969 + 3 ^ 40 * 7514425 * 2
def baseEnd_7514425 : Nat := 3858511867161867511329295

theorem tailTrace_7514425 : CollatzResearch.WordTrace tailWord_7514425 prefixEnd_7514425 3858511867161867511329295 := by
  unfold tailWord_7514425
  simp only [CollatzResearch.WordTrace]
  refine ⟨274073595801529061461472729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182715730534352707640981819 274073595801529061461472729)
  ·
    refine ⟨205555196851146796096104547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274073595801529061461472729 205555196851146796096104547)
    ·
      refine ⟨308332795276720194144156821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205555196851146796096104547 308332795276720194144156821)
      ·
        refine ⟨14453099778596259100507351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 308332795276720194144156821 14453099778596259100507351)
        ·
          refine ⟨21679649667894388650761027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14453099778596259100507351 21679649667894388650761027)
          ·
            refine ⟨32519474501841582976141541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21679649667894388650761027 32519474501841582976141541)
            ·
              refine ⟨6097401469095296808026539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32519474501841582976141541 6097401469095296808026539)
              ·
                refine ⟨9146102203642945212039809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6097401469095296808026539 9146102203642945212039809)
                ·
                  refine ⟨6859576652732208909029857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9146102203642945212039809 6859576652732208909029857)
                  ·
                    refine ⟨5144682489549156681772393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6859576652732208909029857 5144682489549156681772393)
                    ·
                      refine ⟨3858511867161867511329295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5144682489549156681772393 3858511867161867511329295)
                      ·
                        rfl

theorem cell23_7514425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_7514425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514425 prefixEnd_7514425 := by exact prefixLift 7514425
  have htrace : WordTrace (prefixWord ++ tailWord_7514425) baseStart_7514425 baseEnd_7514425 := by
    simpa [prefixWord, tailWord_7514425, baseEnd_7514425] using wordTrace_append hprefix tailTrace_7514425
  have hstable : (prefixWord ++ tailWord_7514425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514425).length < 2 ^ (prefixWord ++ tailWord_7514425).sum := by decide
  have hdescent : baseEnd_7514425 < baseStart_7514425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514444 : List Nat := [2, 2, 1, 3, 2, 1, 4, 1, 2, 5]
def baseStart_7514444 : Nat := 118140960795 + 7514444 * 2 ^ 59
def prefixEnd_7514444 : Nat := 4983230072969 + 3 ^ 40 * 7514444 * 2
def baseEnd_7514444 : Nat := 1286173874431434312330569

theorem tailTrace_7514444 : CollatzResearch.WordTrace tailWord_7514444 prefixEnd_7514444 1286173874431434312330569 := by
  unfold tailWord_7514444
  simp only [CollatzResearch.WordTrace]
  refine ⟨137037144394230113853207193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182716192525640151804276257 137037144394230113853207193)
  ·
    refine ⟨102777858295672585389905395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137037144394230113853207193 102777858295672585389905395)
    ·
      refine ⟨154166787443508878084858093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102777858295672585389905395 154166787443508878084858093)
      ·
        refine ⟨57812545291315829281821785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154166787443508878084858093 57812545291315829281821785)
        ·
          refine ⟨43359408968486871961366339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57812545291315829281821785 43359408968486871961366339)
          ·
            refine ⟨65039113452730307942049509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43359408968486871961366339 65039113452730307942049509)
            ·
              refine ⟨12194833772386932739134283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65039113452730307942049509 12194833772386932739134283)
              ·
                refine ⟨18292250658580399108701425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12194833772386932739134283 18292250658580399108701425)
                ·
                  refine ⟨13719187993935299331526069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18292250658580399108701425 13719187993935299331526069)
                  ·
                    refine ⟨1286173874431434312330569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13719187993935299331526069 1286173874431434312330569)
                    ·
                      rfl

theorem cell23_7514444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 2, 5].length) (baseStart_7514444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514444 prefixEnd_7514444 := by exact prefixLift 7514444
  have htrace : WordTrace (prefixWord ++ tailWord_7514444) baseStart_7514444 baseEnd_7514444 := by
    simpa [prefixWord, tailWord_7514444, baseEnd_7514444] using wordTrace_append hprefix tailTrace_7514444
  have hstable : (prefixWord ++ tailWord_7514444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514444).length < 2 ^ (prefixWord ++ tailWord_7514444).sum := by decide
  have hdescent : baseEnd_7514444 < baseStart_7514444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514467 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 5]
def baseStart_7514467 : Nat := 118140960795 + 7514467 * 2 ^ 59
def prefixEnd_7514467 : Nat := 4983230072969 + 3 ^ 40 * 7514467 * 2
def baseEnd_7514467 : Nat := 3858533433349356347004101

theorem tailTrace_7514467 : CollatzResearch.WordTrace tailWord_7514467 prefixEnd_7514467 3858533433349356347004101 := by
  unfold tailWord_7514467
  simp only [CollatzResearch.WordTrace]
  refine ⟨274075127667376902634501655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182716751778251268423001103 274075127667376902634501655)
  ·
    refine ⟨411112691501065353951752483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274075127667376902634501655 411112691501065353951752483)
    ·
      refine ⟨616669037251598030927628725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411112691501065353951752483 616669037251598030927628725)
      ·
        refine ⟨57812722242337315399465193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 616669037251598030927628725 57812722242337315399465193)
        ·
          refine ⟨43359541681752986549598895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57812722242337315399465193 43359541681752986549598895)
          ·
            refine ⟨65039312522629479824398343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43359541681752986549598895 65039312522629479824398343)
            ·
              refine ⟨97558968783944219736597515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65039312522629479824398343 97558968783944219736597515)
              ·
                refine ⟨146338453175916329604896273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97558968783944219736597515 146338453175916329604896273)
                ·
                  refine ⟨109753839881937247203672205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146338453175916329604896273 109753839881937247203672205)
                  ·
                    refine ⟨41157689955726467701377077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109753839881937247203672205 41157689955726467701377077)
                    ·
                      refine ⟨3858533433349356347004101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41157689955726467701377077 3858533433349356347004101)
                      ·
                        rfl

theorem cell23_7514467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_7514467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514467 prefixEnd_7514467 := by exact prefixLift 7514467
  have htrace : WordTrace (prefixWord ++ tailWord_7514467) baseStart_7514467 baseEnd_7514467 := by
    simpa [prefixWord, tailWord_7514467, baseEnd_7514467] using wordTrace_append hprefix tailTrace_7514467
  have hstable : (prefixWord ++ tailWord_7514467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514467).length < 2 ^ (prefixWord ++ tailWord_7514467).sum := by decide
  have hdescent : baseEnd_7514467 < baseStart_7514467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514498 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_7514498 : Nat := 118140960795 + 7514498 * 2 ^ 59
def prefixEnd_7514498 : Nat := 4983230072969 + 3 ^ 40 * 7514498 * 2
def baseEnd_7514498 : Nat := 3858549351249645725716459

theorem tailTrace_7514498 : CollatzResearch.WordTrace tailWord_7514498 prefixEnd_7514498 3858549351249645725716459 := by
  unfold tailWord_7514498
  simp only [CollatzResearch.WordTrace]
  refine ⟨68519064582566148732220037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182717505553509729952586765 68519064582566148732220037)
  ·
    refine ⟨12847324609231152887291257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68519064582566148732220037 12847324609231152887291257)
    ·
      refine ⟨9635493456923364665468443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12847324609231152887291257 9635493456923364665468443)
      ·
        refine ⟨14453240185385046998202665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9635493456923364665468443 14453240185385046998202665)
        ·
          refine ⟨10839930139038785248651999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14453240185385046998202665 10839930139038785248651999)
          ·
            refine ⟨16259895208558177872977999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10839930139038785248651999 16259895208558177872977999)
            ·
              refine ⟨24389842812837266809466999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16259895208558177872977999 24389842812837266809466999)
              ·
                refine ⟨36584764219255900214200499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24389842812837266809466999 36584764219255900214200499)
                ·
                  refine ⟨54877146328883850321300749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36584764219255900214200499 54877146328883850321300749)
                  ·
                    refine ⟨20578929873331443870487781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54877146328883850321300749 20578929873331443870487781)
                    ·
                      refine ⟨3858549351249645725716459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20578929873331443870487781 3858549351249645725716459)
                      ·
                        rfl

theorem cell23_7514498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_7514498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514498 prefixEnd_7514498 := by exact prefixLift 7514498
  have htrace : WordTrace (prefixWord ++ tailWord_7514498) baseStart_7514498 baseEnd_7514498 := by
    simpa [prefixWord, tailWord_7514498, baseEnd_7514498] using wordTrace_append hprefix tailTrace_7514498
  have hstable : (prefixWord ++ tailWord_7514498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514498).length < 2 ^ (prefixWord ++ tailWord_7514498).sum := by decide
  have hdescent : baseEnd_7514498 < baseStart_7514498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514508 : List Nat := [2, 2, 1, 2, 1, 5, 2, 3, 1, 4]
def baseStart_7514508 : Nat := 118140960795 + 7514508 * 2 ^ 59
def prefixEnd_7514508 : Nat := 4983230072969 + 3 ^ 40 * 7514508 * 2
def baseEnd_7514508 : Nat := 1286184828685396895530471

theorem tailTrace_7514508 : CollatzResearch.WordTrace tailWord_7514508 prefixEnd_7514508 1286184828685396895530471 := by
  unfold tailWord_7514508
  simp only [CollatzResearch.WordTrace]
  refine ⟨137038311530114183318372089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182717748706818911091162785 137038311530114183318372089)
  ·
    refine ⟨102778733647585637488779067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137038311530114183318372089 102778733647585637488779067)
    ·
      refine ⟨154168100471378456233168601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102778733647585637488779067 154168100471378456233168601)
      ·
        refine ⟨115626075353533842174876451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154168100471378456233168601 115626075353533842174876451)
        ·
          refine ⟨173439113030300763262314677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115626075353533842174876451 173439113030300763262314677)
          ·
            refine ⟨16259916846590696555842001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173439113030300763262314677 16259916846590696555842001)
            ·
              refine ⟨12194937634943022416881501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16259916846590696555842001 12194937634943022416881501)
              ·
                refine ⟨4573101613103633406330563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12194937634943022416881501 4573101613103633406330563)
                ·
                  refine ⟨6859652419655450109495845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4573101613103633406330563 6859652419655450109495845)
                  ·
                    refine ⟨1286184828685396895530471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6859652419655450109495845 1286184828685396895530471)
                    ·
                      rfl

theorem cell23_7514508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 1, 4].length) (baseStart_7514508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514508 prefixEnd_7514508 := by exact prefixLift 7514508
  have htrace : WordTrace (prefixWord ++ tailWord_7514508) baseStart_7514508 baseEnd_7514508 := by
    simpa [prefixWord, tailWord_7514508, baseEnd_7514508] using wordTrace_append hprefix tailTrace_7514508
  have hstable : (prefixWord ++ tailWord_7514508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514508).length < 2 ^ (prefixWord ++ tailWord_7514508).sum := by decide
  have hdescent : baseEnd_7514508 < baseStart_7514508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514531 : List Nat := [1, 1, 1, 4, 1, 4, 1, 3, 3, 1, 3]
def baseStart_7514531 : Nat := 118140960795 + 7514531 * 2 ^ 59
def prefixEnd_7514531 : Nat := 4983230072969 + 3 ^ 40 * 7514531 * 2
def baseEnd_7514531 : Nat := 3858566296111244096603807

theorem tailTrace_7514531 : CollatzResearch.WordTrace tailWord_7514531 prefixEnd_7514531 3858566296111244096603807 := by
  unfold tailWord_7514531
  simp only [CollatzResearch.WordTrace]
  refine ⟨274077461939145041564831447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182718307959430027709887631 274077461939145041564831447)
  ·
    refine ⟨411116192908717562347247171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274077461939145041564831447 411116192908717562347247171)
    ·
      refine ⟨616674289363076343520870757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411116192908717562347247171 616674289363076343520870757)
      ·
        refine ⟨115626429255576814410163267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 616674289363076343520870757 115626429255576814410163267)
        ·
          refine ⟨173439643883365221615244901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115626429255576814410163267 173439643883365221615244901)
          ·
            refine ⟨32519933228130979052858419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173439643883365221615244901 32519933228130979052858419)
            ·
              refine ⟨48779899842196468579287629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32519933228130979052858419 48779899842196468579287629)
              ·
                refine ⟨18292462440823675717232861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48779899842196468579287629 18292462440823675717232861)
                ·
                  refine ⟨6859673415308878393962323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18292462440823675717232861 6859673415308878393962323)
                  ·
                    refine ⟨10289510122963317590943485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6859673415308878393962323 10289510122963317590943485)
                    ·
                      refine ⟨3858566296111244096603807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10289510122963317590943485 3858566296111244096603807)
                      ·
                        rfl

theorem cell23_7514531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_7514531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514531 prefixEnd_7514531 := by exact prefixLift 7514531
  have htrace : WordTrace (prefixWord ++ tailWord_7514531) baseStart_7514531 baseEnd_7514531 := by
    simpa [prefixWord, tailWord_7514531, baseEnd_7514531] using wordTrace_append hprefix tailTrace_7514531
  have hstable : (prefixWord ++ tailWord_7514531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514531).length < 2 ^ (prefixWord ++ tailWord_7514531).sum := by decide
  have hdescent : baseEnd_7514531 < baseStart_7514531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514551 : List Nat := [1, 1, 3, 1, 3, 4, 2, 2, 1, 5]
def baseStart_7514551 : Nat := 118140960795 + 7514551 * 2 ^ 59
def prefixEnd_7514551 : Nat := 4983230072969 + 3 ^ 40 * 7514551 * 2
def baseEnd_7514551 : Nat := 1286192188574778006117905

theorem tailTrace_7514551 : CollatzResearch.WordTrace tailWord_7514551 prefixEnd_7514551 1286192188574778006117905 := by
  unfold tailWord_7514551
  simp only [CollatzResearch.WordTrace]
  refine ⟨274078191399072584980559507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182718794266048389987039671 274078191399072584980559507)
  ·
    refine ⟨411117287098608877470839261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274078191399072584980559507 411117287098608877470839261)
    ·
      refine ⟨154168982661978329051564723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411117287098608877470839261 154168982661978329051564723)
      ·
        refine ⟨231253473992967493577347085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154168982661978329051564723 231253473992967493577347085)
        ·
          refine ⟨86720052747362810091505157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231253473992967493577347085 86720052747362810091505157)
          ·
            refine ⟨16260009890130526892157217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86720052747362810091505157 16260009890130526892157217)
            ·
              refine ⟨12195007417597895169117913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16260009890130526892157217 12195007417597895169117913)
              ·
                refine ⟨9146255563198421376838435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12195007417597895169117913 9146255563198421376838435)
                ·
                  refine ⟨13719383344797632065257653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9146255563198421376838435 13719383344797632065257653)
                  ·
                    refine ⟨1286192188574778006117905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13719383344797632065257653 1286192188574778006117905)
                    ·
                      rfl

theorem cell23_7514551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 5].length) (baseStart_7514551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514551 prefixEnd_7514551 := by exact prefixLift 7514551
  have htrace : WordTrace (prefixWord ++ tailWord_7514551) baseStart_7514551 baseEnd_7514551 := by
    simpa [prefixWord, tailWord_7514551, baseEnd_7514551] using wordTrace_append hprefix tailTrace_7514551
  have hstable : (prefixWord ++ tailWord_7514551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514551).length < 2 ^ (prefixWord ++ tailWord_7514551).sum := by decide
  have hdescent : baseEnd_7514551 < baseStart_7514551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514554 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4]
def baseStart_7514554 : Nat := 118140960795 + 7514554 * 2 ^ 59
def prefixEnd_7514554 : Nat := 4983230072969 + 3 ^ 40 * 7514554 * 2
def baseEnd_7514554 : Nat := 3858578106166297506616201

theorem tailTrace_7514554 : CollatzResearch.WordTrace tailWord_7514554 prefixEnd_7514554 3858578106166297506616201 := by
  unfold tailWord_7514554
  simp only [CollatzResearch.WordTrace]
  refine ⟨68519575204515429123229679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182718867212041144328612477 68519575204515429123229679)
  ·
    refine ⟨102779362806773143684844519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68519575204515429123229679 102779362806773143684844519)
    ·
      refine ⟨154169044210159715527266779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102779362806773143684844519 154169044210159715527266779)
      ·
        refine ⟨231253566315239573290900169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154169044210159715527266779 231253566315239573290900169)
        ·
          refine ⟨173440174736429679968175127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231253566315239573290900169 173440174736429679968175127)
          ·
            refine ⟨260160262104644519952262691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173440174736429679968175127 260160262104644519952262691)
            ·
              refine ⟨390240393156966779928394037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260160262104644519952262691 390240393156966779928394037)
              ·
                refine ⟨36585036858465635618286941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 390240393156966779928394037 36585036858465635618286941)
                ·
                  refine ⟨13719388821924613356857603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36585036858465635618286941 13719388821924613356857603)
                  ·
                    refine ⟨20579083232886920035286405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13719388821924613356857603 20579083232886920035286405)
                    ·
                      refine ⟨3858578106166297506616201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20579083232886920035286405 3858578106166297506616201)
                      ·
                        rfl

theorem cell23_7514554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_7514554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514554 prefixEnd_7514554 := by exact prefixLift 7514554
  have htrace : WordTrace (prefixWord ++ tailWord_7514554) baseStart_7514554 baseEnd_7514554 := by
    simpa [prefixWord, tailWord_7514554, baseEnd_7514554] using wordTrace_append hprefix tailTrace_7514554
  have hstable : (prefixWord ++ tailWord_7514554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514554).length < 2 ^ (prefixWord ++ tailWord_7514554).sum := by decide
  have hdescent : baseEnd_7514554 < baseStart_7514554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514581 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 4, 4]
def baseStart_7514581 : Nat := 118140960795 + 7514581 * 2 ^ 59
def prefixEnd_7514581 : Nat := 4983230072969 + 3 ^ 40 * 7514581 * 2
def baseEnd_7514581 : Nat := 1286197323381322966992859

theorem tailTrace_7514581 : CollatzResearch.WordTrace tailWord_7514581 prefixEnd_7514581 1286197323381322966992859 := by
  unfold tailWord_7514581
  simp only [CollatzResearch.WordTrace]
  refine ⟨274079285588963900104151597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182719523725975933402767731 274079285588963900104151597)
  ·
    refine ⟨102779732095861462539056849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274079285588963900104151597 102779732095861462539056849)
    ·
      refine ⟨77084799071896096904292637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102779732095861462539056849 77084799071896096904292637)
      ·
        refine ⟨28906799651961036339109739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77084799071896096904292637 28906799651961036339109739)
        ·
          refine ⟨43360199477941554508664609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28906799651961036339109739 43360199477941554508664609)
          ·
            refine ⟨32520149608456165881498457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43360199477941554508664609 32520149608456165881498457)
            ·
              refine ⟨24390112206342124411123843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32520149608456165881498457 24390112206342124411123843)
              ·
                refine ⟨36585168309513186616685765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24390112206342124411123843 36585168309513186616685765)
                ·
                  refine ⟨6859719058033722490628581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36585168309513186616685765 6859719058033722490628581)
                  ·
                    refine ⟨1286197323381322966992859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6859719058033722490628581 1286197323381322966992859)
                    ·
                      rfl

theorem cell23_7514581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_7514581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514581 prefixEnd_7514581 := by exact prefixLift 7514581
  have htrace : WordTrace (prefixWord ++ tailWord_7514581) baseStart_7514581 baseEnd_7514581 := by
    simpa [prefixWord, tailWord_7514581, baseEnd_7514581] using wordTrace_append hprefix tailTrace_7514581
  have hstable : (prefixWord ++ tailWord_7514581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514581).length < 2 ^ (prefixWord ++ tailWord_7514581).sum := by decide
  have hdescent : baseEnd_7514581 < baseStart_7514581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514587 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 9]
def baseStart_7514587 : Nat := 118140960795 + 7514587 * 2 ^ 59
def prefixEnd_7514587 : Nat := 4983230072969 + 3 ^ 40 * 7514587 * 2
def baseEnd_7514587 : Nat := 3858595051027895877503549

theorem tailTrace_7514587 : CollatzResearch.WordTrace tailWord_7514587 prefixEnd_7514587 3858595051027895877503549 := by
  unfold tailWord_7514587
  simp only [CollatzResearch.WordTrace]
  refine ⟨274079504426942163128870015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182719669617961442085913343 274079504426942163128870015)
  ·
    refine ⟨411119256640413244693305023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274079504426942163128870015 411119256640413244693305023)
    ·
      refine ⟨616678884960619867039957535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411119256640413244693305023 616678884960619867039957535)
      ·
        refine ⟨925018327440929800559936303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616678884960619867039957535 925018327440929800559936303)
        ·
          refine ⟨1387527491161394700839904455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925018327440929800559936303 1387527491161394700839904455)
          ·
            refine ⟨2081291236742092051259856683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1387527491161394700839904455 2081291236742092051259856683)
            ·
              refine ⟨3121936855113138076889785025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2081291236742092051259856683 3121936855113138076889785025)
              ·
                refine ⟨2341452641334853557667338769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3121936855113138076889785025 2341452641334853557667338769)
                ·
                  refine ⟨1756089481001140168250504077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2341452641334853557667338769 1756089481001140168250504077)
                  ·
                    refine ⟨658533555375427563093939029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1756089481001140168250504077 658533555375427563093939029)
                    ·
                      refine ⟨3858595051027895877503549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 658533555375427563093939029 3858595051027895877503549)
                      ·
                        rfl

theorem cell23_7514587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 9].length) (baseStart_7514587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514587 prefixEnd_7514587 := by exact prefixLift 7514587
  have htrace : WordTrace (prefixWord ++ tailWord_7514587) baseStart_7514587 baseEnd_7514587 := by
    simpa [prefixWord, tailWord_7514587, baseEnd_7514587] using wordTrace_append hprefix tailTrace_7514587
  have hstable : (prefixWord ++ tailWord_7514587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514587).length < 2 ^ (prefixWord ++ tailWord_7514587).sum := by decide
  have hdescent : baseEnd_7514587 < baseStart_7514587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514605 : List Nat := [1, 5, 1, 3, 1, 3, 1, 2, 1, 1, 4]
def baseStart_7514605 : Nat := 118140960795 + 7514605 * 2 ^ 59
def prefixEnd_7514605 : Nat := 4983230072969 + 3 ^ 40 * 7514605 * 2
def baseEnd_7514605 : Nat := 3858604293679676807078467

theorem tailTrace_7514605 : CollatzResearch.WordTrace tailWord_7514605 prefixEnd_7514605 3858604293679676807078467 := by
  unfold tailWord_7514605
  simp only [CollatzResearch.WordTrace]
  refine ⟨274080160940876952203025269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182720107293917968135350179 274080160940876952203025269)
  ·
    refine ⟨25695015088207214269033619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 274080160940876952203025269 25695015088207214269033619)
    ·
      refine ⟨38542522632310821403550429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25695015088207214269033619 38542522632310821403550429)
      ·
        refine ⟨14453445987116558026331411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38542522632310821403550429 14453445987116558026331411)
        ·
          refine ⟨21680168980674837039497117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14453445987116558026331411 21680168980674837039497117)
          ·
            refine ⟨8130063367753063889811419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21680168980674837039497117 8130063367753063889811419)
            ·
              refine ⟨12195095051629595834717129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8130063367753063889811419 12195095051629595834717129)
              ·
                refine ⟨9146321288722196876037847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12195095051629595834717129 9146321288722196876037847)
                ·
                  refine ⟨13719481933083295314056771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9146321288722196876037847 13719481933083295314056771)
                  ·
                    refine ⟨20579222899624942971085157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13719481933083295314056771 20579222899624942971085157)
                    ·
                      refine ⟨3858604293679676807078467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20579222899624942971085157 3858604293679676807078467)
                      ·
                        rfl

theorem cell23_7514605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_7514605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514605 prefixEnd_7514605 := by exact prefixLift 7514605
  have htrace : WordTrace (prefixWord ++ tailWord_7514605) baseStart_7514605 baseEnd_7514605 := by
    simpa [prefixWord, tailWord_7514605, baseEnd_7514605] using wordTrace_append hprefix tailTrace_7514605
  have hstable : (prefixWord ++ tailWord_7514605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514605).length < 2 ^ (prefixWord ++ tailWord_7514605).sum := by decide
  have hdescent : baseEnd_7514605 < baseStart_7514605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514621 : List Nat := [1, 4, 1, 1, 1, 3, 3, 2, 1, 3, 3]
def baseStart_7514621 : Nat := 118140960795 + 7514621 * 2 ^ 59
def prefixEnd_7514621 : Nat := 4983230072969 + 3 ^ 40 * 7514621 * 2
def baseEnd_7514621 : Nat := 3858612509370148744478393

theorem tailTrace_7514621 : CollatzResearch.WordTrace tailWord_7514621 prefixEnd_7514621 3858612509370148744478393 := by
  unfold tailWord_7514621
  simp only [CollatzResearch.WordTrace]
  refine ⟨274080744508818986935607717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182720496339212657957071811 274080744508818986935607717)
  ·
    refine ⟨51390139595403560050426447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274080744508818986935607717 51390139595403560050426447)
    ·
      refine ⟨77085209393105340075639671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51390139595403560050426447 77085209393105340075639671)
      ·
        refine ⟨115627814089658010113459507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77085209393105340075639671 115627814089658010113459507)
        ·
          refine ⟨173441721134487015170189261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115627814089658010113459507 173441721134487015170189261)
          ·
            refine ⟨65040645425432630688820973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173441721134487015170189261 65040645425432630688820973)
            ·
              refine ⟨24390242034537236508307865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65040645425432630688820973 24390242034537236508307865)
              ·
                refine ⟨18292681525902927381230899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24390242034537236508307865 18292681525902927381230899)
                ·
                  refine ⟨27439022288854391071846349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18292681525902927381230899 27439022288854391071846349)
                  ·
                    refine ⟨10289633358320396651942381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27439022288854391071846349 10289633358320396651942381)
                    ·
                      refine ⟨3858612509370148744478393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10289633358320396651942381 3858612509370148744478393)
                      ·
                        rfl

theorem cell23_7514621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_7514621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514621 prefixEnd_7514621 := by exact prefixLift 7514621
  have htrace : WordTrace (prefixWord ++ tailWord_7514621) baseStart_7514621 baseEnd_7514621 := by
    simpa [prefixWord, tailWord_7514621, baseEnd_7514621] using wordTrace_append hprefix tailTrace_7514621
  have hstable : (prefixWord ++ tailWord_7514621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514621).length < 2 ^ (prefixWord ++ tailWord_7514621).sum := by decide
  have hdescent : baseEnd_7514621 < baseStart_7514621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514625 : List Nat := [1, 2, 4, 1, 3, 2, 3, 1, 1, 2, 3]
def baseStart_7514625 : Nat := 118140960795 + 7514625 * 2 ^ 59
def prefixEnd_7514625 : Nat := 4983230072969 + 3 ^ 40 * 7514625 * 2
def baseEnd_7514625 : Nat := 3858614563292766728828375

theorem tailTrace_7514625 : CollatzResearch.WordTrace tailWord_7514625 prefixEnd_7514625 3858614563292766728828375 := by
  unfold tailWord_7514625
  simp only [CollatzResearch.WordTrace]
  refine ⟨274080890400804495618753329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182720593600536330412502219 274080890400804495618753329)
  ·
    refine ⟨205560667800603371714064997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274080890400804495618753329 205560667800603371714064997)
    ·
      refine ⟨38542625212613132196387187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205560667800603371714064997 38542625212613132196387187)
      ·
        refine ⟨57813937818919698294580781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38542625212613132196387187 57813937818919698294580781)
        ·
          refine ⟨21680226682094886860467793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57813937818919698294580781 21680226682094886860467793)
          ·
            refine ⟨16260170011571165145350845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21680226682094886860467793 16260170011571165145350845)
            ·
              refine ⟨6097563754339186929506567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16260170011571165145350845 6097563754339186929506567)
              ·
                refine ⟨9146345631508780394259851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6097563754339186929506567 9146345631508780394259851)
                ·
                  refine ⟨13719518447263170591389777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9146345631508780394259851 13719518447263170591389777)
                  ·
                    refine ⟨10289638835447377943542333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13719518447263170591389777 10289638835447377943542333)
                    ·
                      refine ⟨3858614563292766728828375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10289638835447377943542333 3858614563292766728828375)
                      ·
                        rfl

theorem cell23_7514625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_7514625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514625 prefixEnd_7514625 := by exact prefixLift 7514625
  have htrace : WordTrace (prefixWord ++ tailWord_7514625) baseStart_7514625 baseEnd_7514625 := by
    simpa [prefixWord, tailWord_7514625, baseEnd_7514625] using wordTrace_append hprefix tailTrace_7514625
  have hstable : (prefixWord ++ tailWord_7514625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514625).length < 2 ^ (prefixWord ++ tailWord_7514625).sum := by decide
  have hdescent : baseEnd_7514625 < baseStart_7514625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514648 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 3, 3, 2]
def baseStart_7514648 : Nat := 118140960795 + 7514648 * 2 ^ 59
def prefixEnd_7514648 : Nat := 4983230072969 + 3 ^ 40 * 7514648 * 2
def baseEnd_7514648 : Nat := 3858626373347820138840769

theorem tailTrace_7514648 : CollatzResearch.WordTrace tailWord_7514648 prefixEnd_7514648 3858626373347820138840769 := by
  unfold tailWord_7514648
  simp only [CollatzResearch.WordTrace]
  refine ⟨137040864639860585273420299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182721152853147447031227065 137040864639860585273420299)
  ·
    refine ⟨205561296959790877910130449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137040864639860585273420299 205561296959790877910130449)
    ·
      refine ⟨154170972719843158432597837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205561296959790877910130449 154170972719843158432597837)
      ·
        refine ⟨57814114769941184412224189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154170972719843158432597837 57814114769941184412224189)
        ·
          refine ⟨21680293038727944154584071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57814114769941184412224189 21680293038727944154584071)
          ·
            refine ⟨32520439558091916231876107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21680293038727944154584071 32520439558091916231876107)
            ·
              refine ⟨48780659337137874347814161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32520439558091916231876107 48780659337137874347814161)
              ·
                refine ⟨36585494502853405760860621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48780659337137874347814161 36585494502853405760860621)
                ·
                  refine ⟨13719560438570027160322733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36585494502853405760860621 13719560438570027160322733)
                  ·
                    refine ⟨5144835164463760185121025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13719560438570027160322733 5144835164463760185121025)
                    ·
                      refine ⟨3858626373347820138840769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5144835164463760185121025 3858626373347820138840769)
                      ·
                        rfl

theorem cell23_7514648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_7514648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514648 prefixEnd_7514648 := by exact prefixLift 7514648
  have htrace : WordTrace (prefixWord ++ tailWord_7514648) baseStart_7514648 baseEnd_7514648 := by
    simpa [prefixWord, tailWord_7514648, baseEnd_7514648] using wordTrace_append hprefix tailTrace_7514648
  have hstable : (prefixWord ++ tailWord_7514648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514648).length < 2 ^ (prefixWord ++ tailWord_7514648).sum := by decide
  have hdescent : baseEnd_7514648 < baseStart_7514648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514676 : List Nat := [2, 5, 1, 3, 2, 1, 2, 1, 1, 2, 3]
def baseStart_7514676 : Nat := 118140960795 + 7514676 * 2 ^ 59
def prefixEnd_7514676 : Nat := 4983230072969 + 3 ^ 40 * 7514676 * 2
def baseEnd_7514676 : Nat := 3858640750806146029290641

theorem tailTrace_7514676 : CollatzResearch.WordTrace tailWord_7514676 prefixEnd_7514676 3858640750806146029290641 := by
  unfold tailWord_7514676
  simp only [CollatzResearch.WordTrace]
  refine ⟨137041375261809865664429941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182721833682413154219239921 137041375261809865664429941)
  ·
    refine ⟨12847628930794674906040307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137041375261809865664429941 12847628930794674906040307)
    ·
      refine ⟨19271443396192012359060461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12847628930794674906040307 19271443396192012359060461)
      ·
        refine ⟨7226791273572004634647673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19271443396192012359060461 7226791273572004634647673)
        ·
          refine ⟨5420093455179003475985755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7226791273572004634647673 5420093455179003475985755)
          ·
            refine ⟨8130140182768505213978633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5420093455179003475985755 8130140182768505213978633)
            ·
              refine ⟨6097605137076378910483975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8130140182768505213978633 6097605137076378910483975)
              ·
                refine ⟨9146407705614568365725963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6097605137076378910483975 9146407705614568365725963)
                ·
                  refine ⟨13719611558421852548588945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9146407705614568365725963 13719611558421852548588945)
                  ·
                    refine ⟨10289708668816389411441709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13719611558421852548588945 10289708668816389411441709)
                    ·
                      refine ⟨3858640750806146029290641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10289708668816389411441709 3858640750806146029290641)
                      ·
                        rfl

theorem cell23_7514676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_7514676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514676 prefixEnd_7514676 := by exact prefixLift 7514676
  have htrace : WordTrace (prefixWord ++ tailWord_7514676) baseStart_7514676 baseEnd_7514676 := by
    simpa [prefixWord, tailWord_7514676, baseEnd_7514676] using wordTrace_append hprefix tailTrace_7514676
  have hstable : (prefixWord ++ tailWord_7514676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514676).length < 2 ^ (prefixWord ++ tailWord_7514676).sum := by decide
  have hdescent : baseEnd_7514676 < baseStart_7514676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514682 : List Nat := [3, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2]
def baseStart_7514682 : Nat := 118140960795 + 7514682 * 2 ^ 59
def prefixEnd_7514682 : Nat := 4983230072969 + 3 ^ 40 * 7514682 * 2
def baseEnd_7514682 : Nat := 3858643831690073005815613

theorem tailTrace_7514682 : CollatzResearch.WordTrace tailWord_7514682 prefixEnd_7514682 3858643831690073005815613 := by
  unfold tailWord_7514682
  simp only [CollatzResearch.WordTrace]
  refine ⟨68520742340399498588394575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182721979574398662902385533 68520742340399498588394575)
  ·
    refine ⟨102781113510599247882591863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68520742340399498588394575 102781113510599247882591863)
    ·
      refine ⟨154171670265898871823887795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102781113510599247882591863 154171670265898871823887795)
      ·
        refine ⟨231257505398848307735831693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154171670265898871823887795 231257505398848307735831693)
        ·
          refine ⟨86721564524568115400936885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231257505398848307735831693 86721564524568115400936885)
          ·
            refine ⟨8130146674178260818837833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86721564524568115400936885 8130146674178260818837833)
            ·
              refine ⟨6097610005633695614128375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8130146674178260818837833 6097610005633695614128375)
              ·
                refine ⟨9146415008450543421192563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6097610005633695614128375 9146415008450543421192563)
                ·
                  refine ⟨13719622512675815131788845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9146415008450543421192563 13719622512675815131788845)
                  ·
                    refine ⟨5144858442253430674420817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13719622512675815131788845 5144858442253430674420817)
                    ·
                      refine ⟨3858643831690073005815613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5144858442253430674420817 3858643831690073005815613)
                      ·
                        rfl

theorem cell23_7514682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2].length) (baseStart_7514682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514682 prefixEnd_7514682 := by exact prefixLift 7514682
  have htrace : WordTrace (prefixWord ++ tailWord_7514682) baseStart_7514682 baseEnd_7514682 := by
    simpa [prefixWord, tailWord_7514682, baseEnd_7514682] using wordTrace_append hprefix tailTrace_7514682
  have hstable : (prefixWord ++ tailWord_7514682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514682).length < 2 ^ (prefixWord ++ tailWord_7514682).sum := by decide
  have hdescent : baseEnd_7514682 < baseStart_7514682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514695 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 4, 2, 2]
def baseStart_7514695 : Nat := 118140960795 + 7514695 * 2 ^ 59
def prefixEnd_7514695 : Nat := 4983230072969 + 3 ^ 40 * 7514695 * 2
def baseEnd_7514695 : Nat := 3858650506938581454953053

theorem tailTrace_7514695 : CollatzResearch.WordTrace tailWord_7514695 prefixEnd_7514695 3858650506938581454953053 := by
  unfold tailWord_7514695
  simp only [CollatzResearch.WordTrace]
  refine ⟨274083443510550897573801539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182722295673700598382534359 274083443510550897573801539)
  ·
    refine ⟨411125165265826346360702309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274083443510550897573801539 411125165265826346360702309)
    ·
      refine ⟨77085968487342439942631683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 411125165265826346360702309 77085968487342439942631683)
      ·
        refine ⟨115628952731013659913947525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77085968487342439942631683 115628952731013659913947525)
        ·
          refine ⟨21680428637065061233865161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115628952731013659913947525 21680428637065061233865161)
          ·
            refine ⟨16260321477798795925398871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21680428637065061233865161 16260321477798795925398871)
            ·
              refine ⟨24390482216698193888098307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16260321477798795925398871 24390482216698193888098307)
              ·
                refine ⟨36585723325047290832147461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24390482216698193888098307 36585723325047290832147461)
                ·
                  refine ⟨6859823123446367031027649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36585723325047290832147461 6859823123446367031027649)
                  ·
                    refine ⟨5144867342584775273270737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6859823123446367031027649 5144867342584775273270737)
                    ·
                      refine ⟨3858650506938581454953053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5144867342584775273270737 3858650506938581454953053)
                      ·
                        rfl

theorem cell23_7514695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_7514695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514695 prefixEnd_7514695 := by exact prefixLift 7514695
  have htrace : WordTrace (prefixWord ++ tailWord_7514695) baseStart_7514695 baseEnd_7514695 := by
    simpa [prefixWord, tailWord_7514695, baseEnd_7514695] using wordTrace_append hprefix tailTrace_7514695
  have hstable : (prefixWord ++ tailWord_7514695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514695).length < 2 ^ (prefixWord ++ tailWord_7514695).sum := by decide
  have hdescent : baseEnd_7514695 < baseStart_7514695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514711 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 3]
def baseStart_7514711 : Nat := 118140960795 + 7514711 * 2 ^ 59
def prefixEnd_7514711 : Nat := 4983230072969 + 3 ^ 40 * 7514711 * 2
def baseEnd_7514711 : Nat := 3858658722629053392352979

theorem tailTrace_7514711 : CollatzResearch.WordTrace tailWord_7514711 prefixEnd_7514711 3858658722629053392352979 := by
  unfold tailWord_7514711
  simp only [CollatzResearch.WordTrace]
  refine ⟨274084027078492932306383987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182722684718995288204255991 274084027078492932306383987)
  ·
    refine ⟨411126040617739398459575981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274084027078492932306383987 411126040617739398459575981)
    ·
      refine ⟨154172265231652274422340993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411126040617739398459575981 154172265231652274422340993)
      ·
        refine ⟨115629198923739205816755745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154172265231652274422340993 115629198923739205816755745)
        ·
          refine ⟨86721899192804404362566809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115629198923739205816755745 86721899192804404362566809)
          ·
            refine ⟨65041424394603303271925107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86721899192804404362566809 65041424394603303271925107)
            ·
              refine ⟨97562136591904954907887661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65041424394603303271925107 97562136591904954907887661)
              ·
                refine ⟨36585801221964358090457873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97562136591904954907887661 36585801221964358090457873)
                ·
                  refine ⟨27439350916473268567843405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36585801221964358090457873 27439350916473268567843405)
                  ·
                    refine ⟨10289756593677475712941277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27439350916473268567843405 10289756593677475712941277)
                    ·
                      refine ⟨3858658722629053392352979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10289756593677475712941277 3858658722629053392352979)
                      ·
                        rfl

theorem cell23_7514711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_7514711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514711 prefixEnd_7514711 := by exact prefixLift 7514711
  have htrace : WordTrace (prefixWord ++ tailWord_7514711) baseStart_7514711 baseEnd_7514711 := by
    simpa [prefixWord, tailWord_7514711, baseEnd_7514711] using wordTrace_append hprefix tailTrace_7514711
  have hstable : (prefixWord ++ tailWord_7514711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514711).length < 2 ^ (prefixWord ++ tailWord_7514711).sum := by decide
  have hdescent : baseEnd_7514711 < baseStart_7514711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514744 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 1, 10]
def baseStart_7514744 : Nat := 118140960795 + 7514744 * 2 ^ 59
def prefixEnd_7514744 : Nat := 4983230072969 + 3 ^ 40 * 7514744 * 2
def baseEnd_7514744 : Nat := 1286225222496883921080109

theorem tailTrace_7514744 : CollatzResearch.WordTrace tailWord_7514744 prefixEnd_7514744 1286225222496883921080109 := by
  unfold tailWord_7514744
  simp only [CollatzResearch.WordTrace]
  refine ⟨137042615343686689471167643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182723487124915585961556857 137042615343686689471167643)
  ·
    refine ⟨205563923015530034206751465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137042615343686689471167643 205563923015530034206751465)
    ·
      refine ⟨154172942261647525655063599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205563923015530034206751465 154172942261647525655063599)
      ·
        refine ⟨231259413392471288482595399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154172942261647525655063599 231259413392471288482595399)
        ·
          refine ⟨346889120088706932723893099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231259413392471288482595399 346889120088706932723893099)
          ·
            refine ⟨520333680133060399085839649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346889120088706932723893099 520333680133060399085839649)
            ·
              refine ⟨390250260099795299314379737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520333680133060399085839649 390250260099795299314379737)
              ·
                refine ⟨292687695074846474485784803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390250260099795299314379737 292687695074846474485784803)
                ·
                  refine ⟨439031542612269711728677205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292687695074846474485784803 439031542612269711728677205)
                  ·
                    refine ⟨1286225222496883921080109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 439031542612269711728677205 1286225222496883921080109)
                    ·
                      rfl

theorem cell23_7514744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_7514744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514744 prefixEnd_7514744 := by exact prefixLift 7514744
  have htrace : WordTrace (prefixWord ++ tailWord_7514744) baseStart_7514744 baseEnd_7514744 := by
    simpa [prefixWord, tailWord_7514744, baseEnd_7514744] using wordTrace_append hprefix tailTrace_7514744
  have hstable : (prefixWord ++ tailWord_7514744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514744).length < 2 ^ (prefixWord ++ tailWord_7514744).sum := by decide
  have hdescent : baseEnd_7514744 < baseStart_7514744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514781 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_7514781 : Nat := 118140960795 + 7514781 * 2 ^ 59
def prefixEnd_7514781 : Nat := 4983230072969 + 3 ^ 40 * 7514781 * 2
def baseEnd_7514781 : Nat := 3858694666274868118477657

theorem tailTrace_7514781 : CollatzResearch.WordTrace tailWord_7514781 prefixEnd_7514781 3858694666274868118477657 := by
  unfold tailWord_7514781
  simp only [CollatzResearch.WordTrace]
  refine ⟨274086580188239334261432197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182724386792159556174288131 274086580188239334261432197)
  ·
    refine ⟨51391233785294875174018537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274086580188239334261432197 51391233785294875174018537)
    ·
      refine ⟨38543425338971156380513903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51391233785294875174018537 38543425338971156380513903)
      ·
        refine ⟨57815138008456734570770855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38543425338971156380513903 57815138008456734570770855)
        ·
          refine ⟨86722707012685101856156283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57815138008456734570770855 86722707012685101856156283)
          ·
            refine ⟨130084060519027652784234425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86722707012685101856156283 130084060519027652784234425)
            ·
              refine ⟨97563045389270739588175819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130084060519027652784234425 97563045389270739588175819)
              ·
                refine ⟨146344568083906109382263729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97563045389270739588175819 146344568083906109382263729)
                ·
                  refine ⟨109758426062929582036697797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146344568083906109382263729 109758426062929582036697797)
                  ·
                    refine ⟨20579704886799296631880837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109758426062929582036697797 20579704886799296631880837)
                    ·
                      refine ⟨3858694666274868118477657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20579704886799296631880837 3858694666274868118477657)
                      ·
                        rfl

theorem cell23_7514781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_7514781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514781 prefixEnd_7514781 := by exact prefixLift 7514781
  have htrace : WordTrace (prefixWord ++ tailWord_7514781) baseStart_7514781 baseEnd_7514781 := by
    simpa [prefixWord, tailWord_7514781, baseEnd_7514781] using wordTrace_append hprefix tailTrace_7514781
  have hstable : (prefixWord ++ tailWord_7514781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514781).length < 2 ^ (prefixWord ++ tailWord_7514781).sum := by decide
  have hdescent : baseEnd_7514781 < baseStart_7514781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514785 : List Nat := [1, 2, 3, 3, 3, 1, 2, 1, 2, 1, 4]
def baseStart_7514785 : Nat := 118140960795 + 7514785 * 2 ^ 59
def prefixEnd_7514785 : Nat := 4983230072969 + 3 ^ 40 * 7514785 * 2
def baseEnd_7514785 : Nat := 3858696720197486102827639

theorem tailTrace_7514785 : CollatzResearch.WordTrace tailWord_7514785 prefixEnd_7514785 3858696720197486102827639 := by
  unfold tailWord_7514785
  simp only [CollatzResearch.WordTrace]
  refine ⟨274086726080224842944577809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182724484053483228629718539 274086726080224842944577809)
  ·
    refine ⟨205565044560168632208433357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274086726080224842944577809 205565044560168632208433357)
    ·
      refine ⟨77086891710063237078162509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205565044560168632208433357 77086891710063237078162509)
      ·
        refine ⟨28907584391273713904310941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77086891710063237078162509 28907584391273713904310941)
        ·
          refine ⟨10840344146727642714116603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28907584391273713904310941 10840344146727642714116603)
          ·
            refine ⟨16260516220091464071174905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10840344146727642714116603 16260516220091464071174905)
            ·
              refine ⟨12195387165068598053381179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16260516220091464071174905 12195387165068598053381179)
              ·
                refine ⟨18293080747602897080071769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12195387165068598053381179 18293080747602897080071769)
                ·
                  refine ⟨13719810560702172810053827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18293080747602897080071769 13719810560702172810053827)
                  ·
                    refine ⟨20579715841053259215080741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13719810560702172810053827 20579715841053259215080741)
                    ·
                      refine ⟨3858696720197486102827639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20579715841053259215080741 3858696720197486102827639)
                      ·
                        rfl

theorem cell23_7514785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_7514785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514785 prefixEnd_7514785 := by exact prefixLift 7514785
  have htrace : WordTrace (prefixWord ++ tailWord_7514785) baseStart_7514785 baseEnd_7514785 := by
    simpa [prefixWord, tailWord_7514785, baseEnd_7514785] using wordTrace_append hprefix tailTrace_7514785
  have hstable : (prefixWord ++ tailWord_7514785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514785).length < 2 ^ (prefixWord ++ tailWord_7514785).sum := by decide
  have hdescent : baseEnd_7514785 < baseStart_7514785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514805 : List Nat := [1, 3, 3, 3, 1, 1, 2, 2, 2, 2, 3]
def baseStart_7514805 : Nat := 118140960795 + 7514805 * 2 ^ 59
def prefixEnd_7514805 : Nat := 4983230072969 + 3 ^ 40 * 7514805 * 2
def baseEnd_7514805 : Nat := 3858706989810576024577547

theorem tailTrace_7514805 : CollatzResearch.WordTrace tailWord_7514805 prefixEnd_7514805 3858706989810576024577547 := by
  unfold tailWord_7514805
  simp only [CollatzResearch.WordTrace]
  refine ⟨274087455540152386360305869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182724970360101590906870579 274087455540152386360305869)
  ·
    refine ⟨102782795827557144885114701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274087455540152386360305869 102782795827557144885114701)
    ·
      refine ⟨38543548435333929331918013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102782795827557144885114701 38543548435333929331918013)
      ·
        refine ⟨14453830663250223499469255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38543548435333929331918013 14453830663250223499469255)
        ·
          refine ⟨21680745994875335249203883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14453830663250223499469255 21680745994875335249203883)
          ·
            refine ⟨32521118992313002873805825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21680745994875335249203883 32521118992313002873805825)
            ·
              refine ⟨24390839244234752155354369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32521118992313002873805825 24390839244234752155354369)
              ·
                refine ⟨18293129433176064116515777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24390839244234752155354369 18293129433176064116515777)
                ·
                  refine ⟨13719847074882048087386833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18293129433176064116515777 13719847074882048087386833)
                  ·
                    refine ⟨10289885306161536065540125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13719847074882048087386833 10289885306161536065540125)
                    ·
                      refine ⟨3858706989810576024577547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10289885306161536065540125 3858706989810576024577547)
                      ·
                        rfl

theorem cell23_7514805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_7514805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514805 prefixEnd_7514805 := by exact prefixLift 7514805
  have htrace : WordTrace (prefixWord ++ tailWord_7514805) baseStart_7514805 baseEnd_7514805 := by
    simpa [prefixWord, tailWord_7514805, baseEnd_7514805] using wordTrace_append hprefix tailTrace_7514805
  have hstable : (prefixWord ++ tailWord_7514805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514805).length < 2 ^ (prefixWord ++ tailWord_7514805).sum := by decide
  have hdescent : baseEnd_7514805 < baseStart_7514805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514852 : List Nat := [2, 3, 1, 1, 1, 4, 1, 5, 1, 1, 3]
def baseStart_7514852 : Nat := 118140960795 + 7514852 * 2 ^ 59
def prefixEnd_7514852 : Nat := 4983230072969 + 3 ^ 40 * 7514852 * 2
def baseEnd_7514852 : Nat := 3858731123401337340689831

theorem tailTrace_7514852 : CollatzResearch.WordTrace tailWord_7514852 prefixEnd_7514852 3858731123401337340689831 := by
  unfold tailWord_7514852
  simp only [CollatzResearch.WordTrace]
  refine ⟨137044584885491056693633405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182726113180654742258177873 137044584885491056693633405)
  ·
    refine ⟨51391719332059146260112527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137044584885491056693633405 51391719332059146260112527)
    ·
      refine ⟨77087578998088719390168791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51391719332059146260112527 77087578998088719390168791)
      ·
        refine ⟨115631368497133079085253187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77087578998088719390168791 115631368497133079085253187)
        ·
          refine ⟨173447052745699618627879781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115631368497133079085253187 173447052745699618627879781)
          ·
            refine ⟨32521322389818678492727459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173447052745699618627879781 32521322389818678492727459)
            ·
              refine ⟨48781983584728017739091189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32521322389818678492727459 48781983584728017739091189)
              ·
                refine ⟨4573310961068251663039799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48781983584728017739091189 4573310961068251663039799)
                ·
                  refine ⟨6859966441602377494559699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4573310961068251663039799 6859966441602377494559699)
                  ·
                    refine ⟨10289949662403566241839549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6859966441602377494559699 10289949662403566241839549)
                    ·
                      refine ⟨3858731123401337340689831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10289949662403566241839549 3858731123401337340689831)
                      ·
                        rfl

theorem cell23_7514852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 1, 1, 3].length) (baseStart_7514852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514852 prefixEnd_7514852 := by exact prefixLift 7514852
  have htrace : WordTrace (prefixWord ++ tailWord_7514852) baseStart_7514852 baseEnd_7514852 := by
    simpa [prefixWord, tailWord_7514852, baseEnd_7514852] using wordTrace_append hprefix tailTrace_7514852
  have hstable : (prefixWord ++ tailWord_7514852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514852).length < 2 ^ (prefixWord ++ tailWord_7514852).sum := by decide
  have hdescent : baseEnd_7514852 < baseStart_7514852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514871 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 6]
def baseStart_7514871 : Nat := 118140960795 + 7514871 * 2 ^ 59
def prefixEnd_7514871 : Nat := 4983230072969 + 3 ^ 40 * 7514871 * 2
def baseEnd_7514871 : Nat := 3858740879533772766352243

theorem tailTrace_7514871 : CollatzResearch.WordTrace tailWord_7514871 prefixEnd_7514871 3858740879533772766352243 := by
  unfold tailWord_7514871
  simp only [CollatzResearch.WordTrace]
  refine ⟨274089862757913279632208467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182726575171942186421472311 274089862757913279632208467)
  ·
    refine ⟨411134794136869919448312701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274089862757913279632208467 411134794136869919448312701)
    ·
      refine ⟨154175547801326219793117263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411134794136869919448312701 154175547801326219793117263)
      ·
        refine ⟨231263321701989329689675895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154175547801326219793117263 231263321701989329689675895)
        ·
          refine ⟨346894982552983994534513843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231263321701989329689675895 346894982552983994534513843)
          ·
            refine ⟨520342473829475991801770765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346894982552983994534513843 520342473829475991801770765)
            ·
              refine ⟨195128427686053496925664037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 520342473829475991801770765 195128427686053496925664037)
              ·
                refine ⟨36586580191135030673562007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195128427686053496925664037 36586580191135030673562007)
                ·
                  refine ⟨54879870286702546010343011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36586580191135030673562007 54879870286702546010343011)
                  ·
                    refine ⟨82319805430053819015514517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54879870286702546010343011 82319805430053819015514517)
                    ·
                      refine ⟨3858740879533772766352243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82319805430053819015514517 3858740879533772766352243)
                      ·
                        rfl

theorem cell23_7514871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_7514871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514871 prefixEnd_7514871 := by exact prefixLift 7514871
  have htrace : WordTrace (prefixWord ++ tailWord_7514871) baseStart_7514871 baseEnd_7514871 := by
    simpa [prefixWord, tailWord_7514871, baseEnd_7514871] using wordTrace_append hprefix tailTrace_7514871
  have hstable : (prefixWord ++ tailWord_7514871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514871).length < 2 ^ (prefixWord ++ tailWord_7514871).sum := by decide
  have hdescent : baseEnd_7514871 < baseStart_7514871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514881 : List Nat := [1, 2, 4, 1, 1, 1, 1, 12]
def baseStart_7514881 : Nat := 118140960795 + 7514881 * 2 ^ 59
def prefixEnd_7514881 : Nat := 4983230072969 + 3 ^ 40 * 7514881 * 2
def baseEnd_7514881 : Nat := 142916519049641397304711

theorem tailTrace_7514881 : CollatzResearch.WordTrace tailWord_7514881 prefixEnd_7514881 142916519049641397304711 := by
  unfold tailWord_7514881
  simp only [CollatzResearch.WordTrace]
  refine ⟨274090227487877051340072497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182726818325251367560048331 274090227487877051340072497)
  ·
    refine ⟨205567670615907788505054373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274090227487877051340072497 205567670615907788505054373)
    ·
      refine ⟨38543938240482710344697695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205567670615907788505054373 38543938240482710344697695)
      ·
        refine ⟨57815907360724065517046543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38543938240482710344697695 57815907360724065517046543)
        ·
          refine ⟨86723861041086098275569815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57815907360724065517046543 86723861041086098275569815)
          ·
            refine ⟨130085791561629147413354723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86723861041086098275569815 130085791561629147413354723)
            ·
              refine ⟨195128687342443721120032085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130085791561629147413354723 195128687342443721120032085)
              ·
                refine ⟨142916519049641397304711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 195128687342443721120032085 142916519049641397304711)
                ·
                  rfl

theorem cell23_7514881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 12].length) (baseStart_7514881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514881 prefixEnd_7514881 := by exact prefixLift 7514881
  have htrace : WordTrace (prefixWord ++ tailWord_7514881) baseStart_7514881 baseEnd_7514881 := by
    simpa [prefixWord, tailWord_7514881, baseEnd_7514881] using wordTrace_append hprefix tailTrace_7514881
  have hstable : (prefixWord ++ tailWord_7514881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514881).length < 2 ^ (prefixWord ++ tailWord_7514881).sum := by decide
  have hdescent : baseEnd_7514881 < baseStart_7514881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514888 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 1, 1, 6]
def baseStart_7514888 : Nat := 118140960795 + 7514888 * 2 ^ 59
def prefixEnd_7514888 : Nat := 4983230072969 + 3 ^ 40 * 7514888 * 2
def baseEnd_7514888 : Nat := 3858749608704899199839665

theorem tailTrace_7514888 : CollatzResearch.WordTrace tailWord_7514888 prefixEnd_7514888 3858749608704899199839665 := by
  unfold tailWord_7514888
  simp only [CollatzResearch.WordTrace]
  refine ⟨137045241399425845767788659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182726988532567794357051545 137045241399425845767788659)
  ·
    refine ⟨205567862099138768651682989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137045241399425845767788659 205567862099138768651682989)
    ·
      refine ⟨77087948287177038244381121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205567862099138768651682989 77087948287177038244381121)
      ·
        refine ⟨57815961215382778683285841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77087948287177038244381121 57815961215382778683285841)
        ·
          refine ⟨43361970911537084012464381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57815961215382778683285841 43361970911537084012464381)
          ·
            refine ⟨16260739091826406504674143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43361970911537084012464381 16260739091826406504674143)
            ·
              refine ⟨24391108637739609757011215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16260739091826406504674143 24391108637739609757011215)
              ·
                refine ⟨36586662956609414635516823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24391108637739609757011215 36586662956609414635516823)
                ·
                  refine ⟨54879994434914121953275235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36586662956609414635516823 54879994434914121953275235)
                  ·
                    refine ⟨82319991652371182929912853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54879994434914121953275235 82319991652371182929912853)
                    ·
                      refine ⟨3858749608704899199839665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82319991652371182929912853 3858749608704899199839665)
                      ·
                        rfl

theorem cell23_7514888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_7514888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514888 prefixEnd_7514888 := by exact prefixLift 7514888
  have htrace : WordTrace (prefixWord ++ tailWord_7514888) baseStart_7514888 baseEnd_7514888 := by
    simpa [prefixWord, tailWord_7514888, baseEnd_7514888] using wordTrace_append hprefix tailTrace_7514888
  have hstable : (prefixWord ++ tailWord_7514888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514888).length < 2 ^ (prefixWord ++ tailWord_7514888).sum := by decide
  have hdescent : baseEnd_7514888 < baseStart_7514888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514895 : List Nat := [1, 1, 2, 1, 1, 1, 8, 2, 1, 2, 3]
def baseStart_7514895 : Nat := 118140960795 + 7514895 * 2 ^ 59
def prefixEnd_7514895 : Nat := 4983230072969 + 3 ^ 40 * 7514895 * 2
def baseEnd_7514895 : Nat := 3858753203069480672452133

theorem tailTrace_7514895 : CollatzResearch.WordTrace tailWord_7514895 prefixEnd_7514895 3858753203069480672452133 := by
  unfold tailWord_7514895
  simp only [CollatzResearch.WordTrace]
  refine ⟨274090738109826331731082139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182727158739884221154054759 274090738109826331731082139)
  ·
    refine ⟨411136107164739497596623209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274090738109826331731082139 411136107164739497596623209)
    ·
      refine ⟨308352080373554623197467407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411136107164739497596623209 308352080373554623197467407)
      ·
        refine ⟨462528120560331934796201111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308352080373554623197467407 462528120560331934796201111)
        ·
          refine ⟨693792180840497902194301667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462528120560331934796201111 693792180840497902194301667)
          ·
            refine ⟨1040688271260746853291452501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693792180840497902194301667 1040688271260746853291452501)
            ·
              refine ⟨12195565678836877187009209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1040688271260746853291452501 12195565678836877187009209)
              ·
                refine ⟨9146674259127657890256907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12195565678836877187009209 9146674259127657890256907)
                ·
                  refine ⟨13720011388691486835385361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9146674259127657890256907 13720011388691486835385361)
                  ·
                    refine ⟨10290008541518615126539021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13720011388691486835385361 10290008541518615126539021)
                    ·
                      refine ⟨3858753203069480672452133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10290008541518615126539021 3858753203069480672452133)
                      ·
                        rfl

theorem cell23_7514895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 2, 3].length) (baseStart_7514895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514895 prefixEnd_7514895 := by exact prefixLift 7514895
  have htrace : WordTrace (prefixWord ++ tailWord_7514895) baseStart_7514895 baseEnd_7514895 := by
    simpa [prefixWord, tailWord_7514895, baseEnd_7514895] using wordTrace_append hprefix tailTrace_7514895
  have hstable : (prefixWord ++ tailWord_7514895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514895).length < 2 ^ (prefixWord ++ tailWord_7514895).sum := by decide
  have hdescent : baseEnd_7514895 < baseStart_7514895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514926 : List Nat := [4, 1, 3, 2, 1, 3, 1, 1, 3, 2, 2]
def baseStart_7514926 : Nat := 118140960795 + 7514926 * 2 ^ 59
def prefixEnd_7514926 : Nat := 4983230072969 + 3 ^ 40 * 7514926 * 2
def baseEnd_7514926 : Nat := 3858769120969770051164491

theorem tailTrace_7514926 : CollatzResearch.WordTrace tailWord_7514926 prefixEnd_7514926 3858769120969770051164491 := by
  unfold tailWord_7514926
  simp only [CollatzResearch.WordTrace]
  refine ⟨34261483596589253003182579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182727912515142682683640421 34261483596589253003182579)
  ·
    refine ⟨51392225394883879504773869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34261483596589253003182579 51392225394883879504773869)
    ·
      refine ⟨19272084523081454814290201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51392225394883879504773869 19272084523081454814290201)
      ·
        refine ⟨14454063392311091110717651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19272084523081454814290201 14454063392311091110717651)
        ·
          refine ⟨21681095088466636666076477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14454063392311091110717651 21681095088466636666076477)
          ·
            refine ⟨8130410658174988749778679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21681095088466636666076477 8130410658174988749778679)
            ·
              refine ⟨12195615987262483124668019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8130410658174988749778679 12195615987262483124668019)
              ·
                refine ⟨18293423980893724687002029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12195615987262483124668019 18293423980893724687002029)
                ·
                  refine ⟨6860033992835146757625761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18293423980893724687002029 6860033992835146757625761)
                  ·
                    refine ⟨5145025494626360068219321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6860033992835146757625761 5145025494626360068219321)
                    ·
                      refine ⟨3858769120969770051164491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5145025494626360068219321 3858769120969770051164491)
                      ·
                        rfl

theorem cell23_7514926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_7514926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514926 prefixEnd_7514926 := by exact prefixLift 7514926
  have htrace : WordTrace (prefixWord ++ tailWord_7514926) baseStart_7514926 baseEnd_7514926 := by
    simpa [prefixWord, tailWord_7514926, baseEnd_7514926] using wordTrace_append hprefix tailTrace_7514926
  have hstable : (prefixWord ++ tailWord_7514926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514926).length < 2 ^ (prefixWord ++ tailWord_7514926).sum := by decide
  have hdescent : baseEnd_7514926 < baseStart_7514926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514935 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 3, 3, 2]
def baseStart_7514935 : Nat := 118140960795 + 7514935 * 2 ^ 59
def prefixEnd_7514935 : Nat := 4983230072969 + 3 ^ 40 * 7514935 * 2
def baseEnd_7514935 : Nat := 3858773742295660515951949

theorem tailTrace_7514935 : CollatzResearch.WordTrace tailWord_7514935 prefixEnd_7514935 3858773742295660515951949 := by
  unfold tailWord_7514935
  simp only [CollatzResearch.WordTrace]
  refine ⟨274092197029681418562538259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182728131353120945708358839 274092197029681418562538259)
  ·
    refine ⟨411138295544522127843807389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274092197029681418562538259 411138295544522127843807389)
    ·
      refine ⟨154176860829195797941427771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411138295544522127843807389 154176860829195797941427771)
      ·
        refine ⟨231265291243793696912141657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154176860829195797941427771 231265291243793696912141657)
        ·
          refine ⟨173448968432845272684106243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231265291243793696912141657 173448968432845272684106243)
          ·
            refine ⟨260173452649267909026159365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173448968432845272684106243 260173452649267909026159365)
            ·
              refine ⟨48782522371737732942404881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260173452649267909026159365 48782522371737732942404881)
              ·
                refine ⟨36586891778803299706803661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48782522371737732942404881 36586891778803299706803661)
                ·
                  refine ⟨13720084417051237390051373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36586891778803299706803661 13720084417051237390051373)
                  ·
                    refine ⟨5145031656394214021269265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13720084417051237390051373 5145031656394214021269265)
                    ·
                      refine ⟨3858773742295660515951949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5145031656394214021269265 3858773742295660515951949)
                      ·
                        rfl

theorem cell23_7514935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 3, 2].length) (baseStart_7514935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514935 prefixEnd_7514935 := by exact prefixLift 7514935
  have htrace : WordTrace (prefixWord ++ tailWord_7514935) baseStart_7514935 baseEnd_7514935 := by
    simpa [prefixWord, tailWord_7514935, baseEnd_7514935] using wordTrace_append hprefix tailTrace_7514935
  have hstable : (prefixWord ++ tailWord_7514935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514935).length < 2 ^ (prefixWord ++ tailWord_7514935).sum := by decide
  have hdescent : baseEnd_7514935 < baseStart_7514935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514968 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 4, 4, 3]
def baseStart_7514968 : Nat := 118140960795 + 7514968 * 2 ^ 59
def prefixEnd_7514968 : Nat := 4983230072969 + 3 ^ 40 * 7514968 * 2
def baseEnd_7514968 : Nat := 3858790687157258886839297

theorem tailTrace_7514968 : CollatzResearch.WordTrace tailWord_7514968 prefixEnd_7514968 3858790687157258886839297 := by
  unfold tailWord_7514968
  simp only [CollatzResearch.WordTrace]
  refine ⟨137046700319280932599244779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182728933759041243465659705 137046700319280932599244779)
  ·
    refine ⟨205570050478921398898867169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137046700319280932599244779 205570050478921398898867169)
    ·
      refine ⟨154177537859191049174150377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205570050478921398898867169 154177537859191049174150377)
      ·
        refine ⟨115633153394393286880612783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154177537859191049174150377 115633153394393286880612783)
        ·
          refine ⟨173449730091589930320919175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115633153394393286880612783 173449730091589930320919175)
          ·
            refine ⟨260174595137384895481378763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173449730091589930320919175 260174595137384895481378763)
            ·
              refine ⟨390261892706077343222068145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260174595137384895481378763 390261892706077343222068145)
              ·
                refine ⟨292696419529558007416551109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390261892706077343222068145 292696419529558007416551109)
                ·
                  refine ⟨54880578661792126390603333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 292696419529558007416551109 54880578661792126390603333)
                  ·
                    refine ⟨10290108499086023698238125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54880578661792126390603333 10290108499086023698238125)
                    ·
                      refine ⟨3858790687157258886839297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10290108499086023698238125 3858790687157258886839297)
                      ·
                        rfl

theorem cell23_7514968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_7514968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514968 prefixEnd_7514968 := by exact prefixLift 7514968
  have htrace : WordTrace (prefixWord ++ tailWord_7514968) baseStart_7514968 baseEnd_7514968 := by
    simpa [prefixWord, tailWord_7514968, baseEnd_7514968] using wordTrace_append hprefix tailTrace_7514968
  have hstable : (prefixWord ++ tailWord_7514968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514968).length < 2 ^ (prefixWord ++ tailWord_7514968).sum := by decide
  have hdescent : baseEnd_7514968 < baseStart_7514968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514969 : List Nat := [1, 2, 1, 2, 2, 5, 3, 1, 1, 3, 2]
def baseStart_7514969 : Nat := 118140960795 + 7514969 * 2 ^ 59
def prefixEnd_7514969 : Nat := 4983230072969 + 3 ^ 40 * 7514969 * 2
def baseEnd_7514969 : Nat := 3858791200637913382926793

theorem tailTrace_7514969 : CollatzResearch.WordTrace tailWord_7514969 prefixEnd_7514969 3858791200637913382926793 := by
  unfold tailWord_7514969
  simp only [CollatzResearch.WordTrace]
  refine ⟨274093437111558242369275961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182728958074372161579517307 274093437111558242369275961)
  ·
    refine ⟨205570077833668681776956971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274093437111558242369275961 205570077833668681776956971)
    ·
      refine ⟨308355116750503022665435457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205570077833668681776956971 308355116750503022665435457)
      ·
        refine ⟨231266337562877266999076593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308355116750503022665435457 231266337562877266999076593)
        ·
          refine ⟨173449753172157950249307445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231266337562877266999076593 173449753172157950249307445)
          ·
            refine ⟨16260914359889807835872573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173449753172157950249307445 16260914359889807835872573)
            ·
              refine ⟨6097842884958677938452215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16260914359889807835872573 6097842884958677938452215)
              ·
                refine ⟨9146764327438016907678323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6097842884958677938452215 9146764327438016907678323)
                ·
                  refine ⟨13720146491157025361517485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9146764327438016907678323 13720146491157025361517485)
                  ·
                    refine ⟨5145054934183884510569057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13720146491157025361517485 5145054934183884510569057)
                    ·
                      refine ⟨3858791200637913382926793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5145054934183884510569057 3858791200637913382926793)
                      ·
                        rfl

theorem cell23_7514969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 1, 3, 2].length) (baseStart_7514969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514969 prefixEnd_7514969 := by exact prefixLift 7514969
  have htrace : WordTrace (prefixWord ++ tailWord_7514969) baseStart_7514969 baseEnd_7514969 := by
    simpa [prefixWord, tailWord_7514969, baseEnd_7514969] using wordTrace_append hprefix tailTrace_7514969
  have hstable : (prefixWord ++ tailWord_7514969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514969).length < 2 ^ (prefixWord ++ tailWord_7514969).sum := by decide
  have hdescent : baseEnd_7514969 < baseStart_7514969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7514988 : List Nat := [2, 2, 1, 1, 4, 1, 2, 3, 7]
def baseStart_7514988 : Nat := 118140960795 + 7514988 * 2 ^ 59
def prefixEnd_7514988 : Nat := 4983230072969 + 3 ^ 40 * 7514988 * 2
def baseEnd_7514988 : Nat := 428755661863372089843245

theorem tailTrace_7514988 : CollatzResearch.WordTrace tailWord_7514988 prefixEnd_7514988 428755661863372089843245 := by
  unfold tailWord_7514988
  simp only [CollatzResearch.WordTrace]
  refine ⟨137047065049244704307108809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182729420065659605742811745 137047065049244704307108809)
  ·
    refine ⟨102785298786933528230331607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137047065049244704307108809 102785298786933528230331607)
    ·
      refine ⟨154177948180400292345497411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102785298786933528230331607 154177948180400292345497411)
      ·
        refine ⟨231266922270600438518246117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154177948180400292345497411 231266922270600438518246117)
        ·
          refine ⟨43362547925737582222171147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231266922270600438518246117 43362547925737582222171147)
          ·
            refine ⟨65043821888606373333256721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43362547925737582222171147 65043821888606373333256721)
            ·
              refine ⟨48782866416454779999942541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65043821888606373333256721 48782866416454779999942541)
              ·
                refine ⟨18293574906170542499978453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48782866416454779999942541 18293574906170542499978453)
                ·
                  refine ⟨428755661863372089843245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18293574906170542499978453 428755661863372089843245)
                  ·
                    rfl

theorem cell23_7514988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 7].length) (baseStart_7514988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7514988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7514988 prefixEnd_7514988 := by exact prefixLift 7514988
  have htrace : WordTrace (prefixWord ++ tailWord_7514988) baseStart_7514988 baseEnd_7514988 := by
    simpa [prefixWord, tailWord_7514988, baseEnd_7514988] using wordTrace_append hprefix tailTrace_7514988
  have hstable : (prefixWord ++ tailWord_7514988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7514988).length < 2 ^ (prefixWord ++ tailWord_7514988).sum := by decide
  have hdescent : baseEnd_7514988 < baseStart_7514988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7514988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515055 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 1, 6, 2]
def baseStart_7515055 : Nat := 118140960795 + 7515055 * 2 ^ 59
def prefixEnd_7515055 : Nat := 4983230072969 + 3 ^ 40 * 7515055 * 2
def baseEnd_7515055 : Nat := 3858835359974200046451397

theorem tailTrace_7515055 : CollatzResearch.WordTrace tailWord_7515055 prefixEnd_7515055 3858835359974200046451397 := by
  unfold tailWord_7515055
  simp only [CollatzResearch.WordTrace]
  refine ⟨274096573789246679056906619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182731049192831119371271079 274096573789246679056906619)
  ·
    refine ⟨411144860683870018585359929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274096573789246679056906619 411144860683870018585359929)
    ·
      refine ⟨308358645512902513939019947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411144860683870018585359929 308358645512902513939019947)
      ·
        refine ⟨462537968269353770908529921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308358645512902513939019947 462537968269353770908529921)
        ·
          refine ⟨346903476202015328181397441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462537968269353770908529921 346903476202015328181397441)
          ·
            refine ⟨260177607151511496136048081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346903476202015328181397441 260177607151511496136048081)
            ·
              refine ⟨195133205363633622102036061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260177607151511496136048081 195133205363633622102036061)
              ·
                refine ⟨73174952011362608288263523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195133205363633622102036061 73174952011362608288263523)
                ·
                  refine ⟨109762428017043912432395285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73174952011362608288263523 109762428017043912432395285)
                  ·
                    refine ⟨5145113813298933395268529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109762428017043912432395285 5145113813298933395268529)
                    ·
                      refine ⟨3858835359974200046451397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5145113813298933395268529 3858835359974200046451397)
                      ·
                        rfl

theorem cell23_7515055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 6, 2].length) (baseStart_7515055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515055 prefixEnd_7515055 := by exact prefixLift 7515055
  have htrace : WordTrace (prefixWord ++ tailWord_7515055) baseStart_7515055 baseEnd_7515055 := by
    simpa [prefixWord, tailWord_7515055, baseEnd_7515055] using wordTrace_append hprefix tailTrace_7515055
  have hstable : (prefixWord ++ tailWord_7515055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515055).length < 2 ^ (prefixWord ++ tailWord_7515055).sum := by decide
  have hdescent : baseEnd_7515055 < baseStart_7515055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515092 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 4, 2, 3]
def baseStart_7515092 : Nat := 118140960795 + 7515092 * 2 ^ 59
def prefixEnd_7515092 : Nat := 4983230072969 + 3 ^ 40 * 7515092 * 2
def baseEnd_7515092 : Nat := 3858854358758416401688727

theorem tailTrace_7515092 : CollatzResearch.WordTrace tailWord_7515092 prefixEnd_7515092 3858854358758416401688727 := by
  unfold tailWord_7515092
  simp only [CollatzResearch.WordTrace]
  refine ⟨137048961645056317188001765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182731948860075089584002353 137048961645056317188001765)
  ·
    refine ⟨25696680308448059472750331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137048961645056317188001765 25696680308448059472750331)
    ·
      refine ⟨38545020462672089209125497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25696680308448059472750331 38545020462672089209125497)
      ·
        refine ⟨28908765347004066906844123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38545020462672089209125497 28908765347004066906844123)
        ·
          refine ⟨43363148020506100360266185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28908765347004066906844123 43363148020506100360266185)
          ·
            refine ⟨32522361015379575270199639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43363148020506100360266185 32522361015379575270199639)
            ·
              refine ⟨48783541523069362905299459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32522361015379575270199639 48783541523069362905299459)
              ·
                refine ⟨73175312284604044357949189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48783541523069362905299459 73175312284604044357949189)
                ·
                  refine ⟨13720371053363258317115473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73175312284604044357949189 13720371053363258317115473)
                  ·
                    refine ⟨10290278290022443737836605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13720371053363258317115473 10290278290022443737836605)
                    ·
                      refine ⟨3858854358758416401688727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10290278290022443737836605 3858854358758416401688727)
                      ·
                        rfl

theorem cell23_7515092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_7515092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515092 prefixEnd_7515092 := by exact prefixLift 7515092
  have htrace : WordTrace (prefixWord ++ tailWord_7515092) baseStart_7515092 baseEnd_7515092 := by
    simpa [prefixWord, tailWord_7515092, baseEnd_7515092] using wordTrace_append hprefix tailTrace_7515092
  have hstable : (prefixWord ++ tailWord_7515092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515092).length < 2 ^ (prefixWord ++ tailWord_7515092).sum := by decide
  have hdescent : baseEnd_7515092 < baseStart_7515092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515112 : List Nat := [2, 1, 4, 1, 1, 1, 6, 1, 6]
def baseStart_7515112 : Nat := 118140960795 + 7515112 * 2 ^ 59
def prefixEnd_7515112 : Nat := 4983230072969 + 3 ^ 40 * 7515112 * 2
def baseEnd_7515112 : Nat := 428762736485722924826515

theorem tailTrace_7515112 : CollatzResearch.WordTrace tailWord_7515112 prefixEnd_7515112 428762736485722924826515 := by
  unfold tailWord_7515112
  simp only [CollatzResearch.WordTrace]
  refine ⟨137049326375020088895865795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182732435166693451861154393 137049326375020088895865795)
  ·
    refine ⟨205573989562530133343798693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137049326375020088895865795 205573989562530133343798693)
    ·
      refine ⟨38545123042974400001962255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205573989562530133343798693 38545123042974400001962255)
      ·
        refine ⟨57817684564461600002943383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38545123042974400001962255 57817684564461600002943383)
        ·
          refine ⟨86726526846692400004415075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57817684564461600002943383 86726526846692400004415075)
          ·
            refine ⟨130089790270038600006622613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86726526846692400004415075 130089790270038600006622613)
            ·
              refine ⟨6097958918908059375310435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130089790270038600006622613 6097958918908059375310435)
              ·
                refine ⟨9146938378362089062965653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6097958918908059375310435 9146938378362089062965653)
                ·
                  refine ⟨428762736485722924826515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9146938378362089062965653 428762736485722924826515)
                  ·
                    rfl

theorem cell23_7515112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 6].length) (baseStart_7515112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515112 prefixEnd_7515112 := by exact prefixLift 7515112
  have htrace : WordTrace (prefixWord ++ tailWord_7515112) baseStart_7515112 baseEnd_7515112 := by
    simpa [prefixWord, tailWord_7515112, baseEnd_7515112] using wordTrace_append hprefix tailTrace_7515112
  have hstable : (prefixWord ++ tailWord_7515112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515112).length < 2 ^ (prefixWord ++ tailWord_7515112).sum := by decide
  have hdescent : baseEnd_7515112 < baseStart_7515112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515172 : List Nat := [2, 3, 1, 4, 1, 1, 1, 3, 1, 6]
def baseStart_7515172 : Nat := 118140960795 + 7515172 * 2 ^ 59
def prefixEnd_7515172 : Nat := 4983230072969 + 3 ^ 40 * 7515172 * 2
def baseEnd_7515172 : Nat := 1286298479070258696229453

theorem tailTrace_7515172 : CollatzResearch.WordTrace tailWord_7515172 prefixEnd_7515172 1286298479070258696229453 := by
  unfold tailWord_7515172
  simp only [CollatzResearch.WordTrace]
  refine ⟨137050420564911404019457885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182733894086548538692610513 137050420564911404019457885)
  ·
    refine ⟨51393907711841776507296707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137050420564911404019457885 51393907711841776507296707)
    ·
      refine ⟨77090861567762664760945061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51393907711841776507296707 77090861567762664760945061)
      ·
        refine ⟨14454536543955499642677199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77090861567762664760945061 14454536543955499642677199)
        ·
          refine ⟨21681804815933249464015799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14454536543955499642677199 21681804815933249464015799)
          ·
            refine ⟨32522707223899874196023699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21681804815933249464015799 32522707223899874196023699)
            ·
              refine ⟨48784060835849811294035549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32522707223899874196023699 48784060835849811294035549)
              ·
                refine ⟨18294022813443679235263331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48784060835849811294035549 18294022813443679235263331)
                ·
                  refine ⟨27441034220165518852894997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18294022813443679235263331 27441034220165518852894997)
                  ·
                    refine ⟨1286298479070258696229453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27441034220165518852894997 1286298479070258696229453)
                    ·
                      rfl

theorem cell23_7515172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_7515172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515172 prefixEnd_7515172 := by exact prefixLift 7515172
  have htrace : WordTrace (prefixWord ++ tailWord_7515172) baseStart_7515172 baseEnd_7515172 := by
    simpa [prefixWord, tailWord_7515172, baseEnd_7515172] using wordTrace_append hprefix tailTrace_7515172
  have hstable : (prefixWord ++ tailWord_7515172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515172).length < 2 ^ (prefixWord ++ tailWord_7515172).sum := by decide
  have hdescent : baseEnd_7515172 < baseStart_7515172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515179 : List Nat := [1, 1, 1, 1, 2, 1, 7, 2, 3, 2, 2]
def baseStart_7515179 : Nat := 118140960795 + 7515179 * 2 ^ 59
def prefixEnd_7515179 : Nat := 4983230072969 + 3 ^ 40 * 7515179 * 2
def baseEnd_7515179 : Nat := 3858899031575357561300827

theorem tailTrace_7515179 : CollatzResearch.WordTrace tailWord_7515179 prefixEnd_7515179 3858899031575357561300827 := by
  unfold tailWord_7515179
  simp only [CollatzResearch.WordTrace]
  refine ⟨274101096440797448234420591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182734064293864965489613727 274101096440797448234420591)
  ·
    refine ⟨411151644661196172351630887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274101096440797448234420591 411151644661196172351630887)
    ·
      refine ⟨616727466991794258527446331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411151644661196172351630887 616727466991794258527446331)
      ·
        refine ⟨925091200487691387791169497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616727466991794258527446331 925091200487691387791169497)
        ·
          refine ⟨693818400365768540843377123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 925091200487691387791169497 693818400365768540843377123)
          ·
            refine ⟨1040727600548652811265065685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693818400365768540843377123 1040727600548652811265065685)
            ·
              refine ⟨24392053137859050264024977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1040727600548652811265065685 24392053137859050264024977)
              ·
                refine ⟨18294039853394287698018733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24392053137859050264024977 18294039853394287698018733)
                ·
                  refine ⟨6860264945022857886757025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18294039853394287698018733 6860264945022857886757025)
                  ·
                    refine ⟨5145198708767143415067769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6860264945022857886757025 5145198708767143415067769)
                    ·
                      refine ⟨3858899031575357561300827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5145198708767143415067769 3858899031575357561300827)
                      ·
                        rfl

theorem cell23_7515179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 2, 2].length) (baseStart_7515179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515179 prefixEnd_7515179 := by exact prefixLift 7515179
  have htrace : WordTrace (prefixWord ++ tailWord_7515179) baseStart_7515179 baseEnd_7515179 := by
    simpa [prefixWord, tailWord_7515179, baseEnd_7515179] using wordTrace_append hprefix tailTrace_7515179
  have hstable : (prefixWord ++ tailWord_7515179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515179).length < 2 ^ (prefixWord ++ tailWord_7515179).sum := by decide
  have hdescent : baseEnd_7515179 < baseStart_7515179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515192 : List Nat := [2, 1, 2, 1, 5, 1, 2, 2, 1, 2, 4]
def baseStart_7515192 : Nat := 118140960795 + 7515192 * 2 ^ 59
def prefixEnd_7515192 : Nat := 4983230072969 + 3 ^ 40 * 7515192 * 2
def baseEnd_7515192 : Nat := 3858905706823866010438267

theorem tailTrace_7515192 : CollatzResearch.WordTrace tailWord_7515192 prefixEnd_7515192 3858905706823866010438267 := by
  unfold tailWord_7515192
  simp only [CollatzResearch.WordTrace]
  refine ⟨137050785294875175727321915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182734380393166900969762553 137050785294875175727321915)
  ·
    refine ⟨205576177942312763590982873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137050785294875175727321915 205576177942312763590982873)
    ·
      refine ⟨154182133456734572693237155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205576177942312763590982873 154182133456734572693237155)
      ·
        refine ⟨231273200185101859039855733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154182133456734572693237155 231273200185101859039855733)
        ·
          refine ⟨21681862517353299284986475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 231273200185101859039855733 21681862517353299284986475)
          ·
            refine ⟨32522793776029948927479713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21681862517353299284986475 32522793776029948927479713)
            ·
              refine ⟨24392095332022461695609785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32522793776029948927479713 24392095332022461695609785)
              ·
                refine ⟨18294071499016846271707339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24392095332022461695609785 18294071499016846271707339)
                ·
                  refine ⟨27441107248525269407561009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18294071499016846271707339 27441107248525269407561009)
                  ·
                    refine ⟨20580830436393952055670757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27441107248525269407561009 20580830436393952055670757)
                    ·
                      refine ⟨3858905706823866010438267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20580830436393952055670757 3858905706823866010438267)
                      ·
                        rfl

theorem cell23_7515192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_7515192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515192 prefixEnd_7515192 := by exact prefixLift 7515192
  have htrace : WordTrace (prefixWord ++ tailWord_7515192) baseStart_7515192 baseEnd_7515192 := by
    simpa [prefixWord, tailWord_7515192, baseEnd_7515192] using wordTrace_append hprefix tailTrace_7515192
  have hstable : (prefixWord ++ tailWord_7515192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515192).length < 2 ^ (prefixWord ++ tailWord_7515192).sum := by decide
  have hdescent : baseEnd_7515192 < baseStart_7515192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515196 : List Nat := [2, 2, 2, 2, 2, 4, 2, 1, 1, 1, 4]
def baseStart_7515196 : Nat := 118140960795 + 7515196 * 2 ^ 59
def prefixEnd_7515196 : Nat := 4983230072969 + 3 ^ 40 * 7515196 * 2
def baseEnd_7515196 : Nat := 3858907760746483994788249

theorem tailTrace_7515196 : CollatzResearch.WordTrace tailWord_7515196 prefixEnd_7515196 3858907760746483994788249 := by
  unfold tailWord_7515196
  simp only [CollatzResearch.WordTrace]
  refine ⟨137050858240867930068894721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182734477654490573425192961 137050858240867930068894721)
  ·
    refine ⟨102788143680650947551671041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137050858240867930068894721 102788143680650947551671041)
    ·
      refine ⟨77091107760488210663753281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102788143680650947551671041 77091107760488210663753281)
      ·
        refine ⟨57818330820366157997814961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77091107760488210663753281 57818330820366157997814961)
        ·
          refine ⟨43363748115274618498361221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57818330820366157997814961 43363748115274618498361221)
          ·
            refine ⟨8130702771613990968442729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43363748115274618498361221 8130702771613990968442729)
            ·
              refine ⟨6098027078710493226332047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8130702771613990968442729 6098027078710493226332047)
              ·
                refine ⟨9147040618065739839498071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6098027078710493226332047 9147040618065739839498071)
                ·
                  refine ⟨13720560927098609759247107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9147040618065739839498071 13720560927098609759247107)
                  ·
                    refine ⟨20580841390647914638870661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13720560927098609759247107 20580841390647914638870661)
                    ·
                      refine ⟨3858907760746483994788249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20580841390647914638870661 3858907760746483994788249)
                      ·
                        rfl

theorem cell23_7515196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_7515196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515196 prefixEnd_7515196 := by exact prefixLift 7515196
  have htrace : WordTrace (prefixWord ++ tailWord_7515196) baseStart_7515196 baseEnd_7515196 := by
    simpa [prefixWord, tailWord_7515196, baseEnd_7515196] using wordTrace_append hprefix tailTrace_7515196
  have hstable : (prefixWord ++ tailWord_7515196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515196).length < 2 ^ (prefixWord ++ tailWord_7515196).sum := by decide
  have hdescent : baseEnd_7515196 < baseStart_7515196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515206 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_7515206 : Nat := 118140960795 + 7515206 * 2 ^ 59
def prefixEnd_7515206 : Nat := 4983230072969 + 3 ^ 40 * 7515206 * 2
def baseEnd_7515206 : Nat := 1286304298517676318554401

theorem tailTrace_7515206 : CollatzResearch.WordTrace tailWord_7515206 prefixEnd_7515206 1286304298517676318554401 := by
  unfold tailWord_7515206
  simp only [CollatzResearch.WordTrace]
  refine ⟨8565690037865613495176671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 182734720807799754563768981 8565690037865613495176671)
  ·
    refine ⟨12848535056798420242765007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8565690037865613495176671 12848535056798420242765007)
    ·
      refine ⟨19272802585197630364147511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12848535056798420242765007 19272802585197630364147511)
      ·
        refine ⟨28909203877796445546221267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19272802585197630364147511 28909203877796445546221267)
        ·
          refine ⟨43363805816694668319331901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28909203877796445546221267 43363805816694668319331901)
          ·
            refine ⟨16261427181260500619749463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43363805816694668319331901 16261427181260500619749463)
            ·
              refine ⟨24392140771890750929624195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16261427181260500619749463 24392140771890750929624195)
              ·
                refine ⟨36588211157836126394436293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24392140771890750929624195 36588211157836126394436293)
                ·
                  refine ⟨6860289592094273698956805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36588211157836126394436293 6860289592094273698956805)
                  ·
                    refine ⟨1286304298517676318554401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6860289592094273698956805 1286304298517676318554401)
                    ·
                      rfl

theorem cell23_7515206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_7515206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515206 prefixEnd_7515206 := by exact prefixLift 7515206
  have htrace : WordTrace (prefixWord ++ tailWord_7515206) baseStart_7515206 baseEnd_7515206 := by
    simpa [prefixWord, tailWord_7515206, baseEnd_7515206] using wordTrace_append hprefix tailTrace_7515206
  have hstable : (prefixWord ++ tailWord_7515206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515206).length < 2 ^ (prefixWord ++ tailWord_7515206).sum := by decide
  have hdescent : baseEnd_7515206 < baseStart_7515206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515213 : List Nat := [1, 6, 1, 1, 1, 3, 2, 1, 3, 2, 2]
def baseStart_7515213 : Nat := 118140960795 + 7515213 * 2 ^ 59
def prefixEnd_7515213 : Nat := 4983230072969 + 3 ^ 40 * 7515213 * 2
def baseEnd_7515213 : Nat := 3858916489917610428275671

theorem tailTrace_7515213 : CollatzResearch.WordTrace tailWord_7515213 prefixEnd_7515213 3858916489917610428275671 := by
  unfold tailWord_7515213
  simp only [CollatzResearch.WordTrace]
  refine ⟨274102336522674272041158293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182734891015116181360772195 274102336522674272041158293)
  ·
    refine ⟨12848547024500356501929295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 274102336522674272041158293 12848547024500356501929295)
    ·
      refine ⟨19272820536750534752893943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12848547024500356501929295 19272820536750534752893943)
      ·
        refine ⟨28909230805125802129340915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19272820536750534752893943 28909230805125802129340915)
        ·
          refine ⟨43363846207688703194011373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28909230805125802129340915 43363846207688703194011373)
          ·
            refine ⟨16261442327883263697754265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43363846207688703194011373 16261442327883263697754265)
            ·
              refine ⟨12196081745912447773315699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16261442327883263697754265 12196081745912447773315699)
              ·
                refine ⟨18294122618868671659973549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12196081745912447773315699 18294122618868671659973549)
                ·
                  refine ⟨6860295982075751872490081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18294122618868671659973549 6860295982075751872490081)
                  ·
                    refine ⟨5145221986556813904367561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6860295982075751872490081 5145221986556813904367561)
                    ·
                      refine ⟨3858916489917610428275671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5145221986556813904367561 3858916489917610428275671)
                      ·
                        rfl

theorem cell23_7515213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_7515213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515213 prefixEnd_7515213 := by exact prefixLift 7515213
  have htrace : WordTrace (prefixWord ++ tailWord_7515213) baseStart_7515213 baseEnd_7515213 := by
    simpa [prefixWord, tailWord_7515213, baseEnd_7515213] using wordTrace_append hprefix tailTrace_7515213
  have hstable : (prefixWord ++ tailWord_7515213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515213).length < 2 ^ (prefixWord ++ tailWord_7515213).sum := by decide
  have hdescent : baseEnd_7515213 < baseStart_7515213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515230 : List Nat := [4, 4, 1, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_7515230 : Nat := 118140960795 + 7515230 * 2 ^ 59
def prefixEnd_7515230 : Nat := 4983230072969 + 3 ^ 40 * 7515230 * 2
def baseEnd_7515230 : Nat := 3858925219088736861763093

theorem tailTrace_7515230 : CollatzResearch.WordTrace tailWord_7515230 prefixEnd_7515230 3858925219088736861763093 := by
  unfold tailWord_7515230
  simp only [CollatzResearch.WordTrace]
  refine ⟨34262869570451585493065893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182735304375741789296351429 34262869570451585493065893)
  ·
    refine ⟨6424288044459672279949855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34262869570451585493065893 6424288044459672279949855)
    ·
      refine ⟨9636432066689508419924783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6424288044459672279949855 9636432066689508419924783)
      ·
        refine ⟨14454648100034262629887175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9636432066689508419924783 14454648100034262629887175)
        ·
          refine ⟨21681972150051393944830763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14454648100034262629887175 21681972150051393944830763)
          ·
            refine ⟨32522958225077090917246145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21681972150051393944830763 32522958225077090917246145)
            ·
              refine ⟨24392218668807818187934609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32522958225077090917246145 24392218668807818187934609)
              ·
                refine ⟨18294164001605863640950957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24392218668807818187934609 18294164001605863640950957)
                ·
                  refine ⟨6860311500602198865356609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18294164001605863640950957 6860311500602198865356609)
                  ·
                    refine ⟨5145233625451649149017457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6860311500602198865356609 5145233625451649149017457)
                    ·
                      refine ⟨3858925219088736861763093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5145233625451649149017457 3858925219088736861763093)
                      ·
                        rfl

theorem cell23_7515230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_7515230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515230 prefixEnd_7515230 := by exact prefixLift 7515230
  have htrace : WordTrace (prefixWord ++ tailWord_7515230) baseStart_7515230 baseEnd_7515230 := by
    simpa [prefixWord, tailWord_7515230, baseEnd_7515230] using wordTrace_append hprefix tailTrace_7515230
  have hstable : (prefixWord ++ tailWord_7515230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515230).length < 2 ^ (prefixWord ++ tailWord_7515230).sum := by decide
  have hdescent : baseEnd_7515230 < baseStart_7515230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515242 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_7515242 : Nat := 118140960795 + 7515242 * 2 ^ 59
def prefixEnd_7515242 : Nat := 4983230072969 + 3 ^ 40 * 7515242 * 2
def baseEnd_7515242 : Nat := 3858931380856590814813037

theorem tailTrace_7515242 : CollatzResearch.WordTrace tailWord_7515242 prefixEnd_7515242 3858931380856590814813037 := by
  unfold tailWord_7515242
  simp only [CollatzResearch.WordTrace]
  refine ⟨68525848559892302498490995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182735596159712806662642653 68525848559892302498490995)
  ·
    refine ⟨102788772839838453747736493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68525848559892302498490995 102788772839838453747736493)
    ·
      refine ⟨38545789814939420155401185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102788772839838453747736493 38545789814939420155401185)
      ·
        refine ⟨28909342361204565116550889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38545789814939420155401185 28909342361204565116550889)
        ·
          refine ⟨21682006770903423837413167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28909342361204565116550889 21682006770903423837413167)
          ·
            refine ⟨32523010156355135756119751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21682006770903423837413167 32523010156355135756119751)
            ·
              refine ⟨48784515234532703634179627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32523010156355135756119751 48784515234532703634179627)
              ·
                refine ⟨73176772851799055451269441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48784515234532703634179627 73176772851799055451269441)
                ·
                  refine ⟨54882579638849291588452081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73176772851799055451269441 54882579638849291588452081)
                  ·
                    refine ⟨41161934729136968691339061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54882579638849291588452081 41161934729136968691339061)
                    ·
                      refine ⟨3858931380856590814813037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41161934729136968691339061 3858931380856590814813037)
                      ·
                        rfl

theorem cell23_7515242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_7515242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515242 prefixEnd_7515242 := by exact prefixLift 7515242
  have htrace : WordTrace (prefixWord ++ tailWord_7515242) baseStart_7515242 baseEnd_7515242 := by
    simpa [prefixWord, tailWord_7515242, baseEnd_7515242] using wordTrace_append hprefix tailTrace_7515242
  have hstable : (prefixWord ++ tailWord_7515242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515242).length < 2 ^ (prefixWord ++ tailWord_7515242).sum := by decide
  have hdescent : baseEnd_7515242 < baseStart_7515242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515326 : List Nat := [4, 2, 1, 1, 3, 2, 1, 4, 5]
def baseStart_7515326 : Nat := 118140960795 + 7515326 * 2 ^ 59
def prefixEnd_7515326 : Nat := 4983230072969 + 3 ^ 40 * 7515326 * 2
def baseEnd_7515326 : Nat := 428774945914618720684739

theorem tailTrace_7515326 : CollatzResearch.WordTrace tailWord_7515326 prefixEnd_7515326 428774945914618720684739 := by
  unfold tailWord_7515326
  simp only [CollatzResearch.WordTrace]
  refine ⟨34263307246408111542502729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182737638647509928226681221 34263307246408111542502729)
  ·
    refine ⟨25697480434806083656877047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34263307246408111542502729 25697480434806083656877047)
    ·
      refine ⟨38546220652209125485315571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25697480434806083656877047 38546220652209125485315571)
      ·
        refine ⟨57819330978313688227973357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38546220652209125485315571 57819330978313688227973357)
        ·
          refine ⟨21682249116867633085490009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57819330978313688227973357 21682249116867633085490009)
          ·
            refine ⟨16261686837650724814117507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21682249116867633085490009 16261686837650724814117507)
            ·
              refine ⟨24392530256476087221176261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16261686837650724814117507 24392530256476087221176261)
              ·
                refine ⟨4573599423089266353970549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24392530256476087221176261 4573599423089266353970549)
                ·
                  refine ⟨428774945914618720684739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4573599423089266353970549 428774945914618720684739)
                  ·
                    rfl

theorem cell23_7515326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_7515326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515326 prefixEnd_7515326 := by exact prefixLift 7515326
  have htrace : WordTrace (prefixWord ++ tailWord_7515326) baseStart_7515326 baseEnd_7515326 := by
    simpa [prefixWord, tailWord_7515326, baseEnd_7515326] using wordTrace_append hprefix tailTrace_7515326
  have hstable : (prefixWord ++ tailWord_7515326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515326).length < 2 ^ (prefixWord ++ tailWord_7515326).sum := by decide
  have hdescent : baseEnd_7515326 < baseStart_7515326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515359 : List Nat := [1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 4]
def baseStart_7515359 : Nat := 118140960795 + 7515359 * 2 ^ 59
def prefixEnd_7515359 : Nat := 4983230072969 + 3 ^ 40 * 7515359 * 2
def baseEnd_7515359 : Nat := 3858991458093166857049999

theorem tailTrace_7515359 : CollatzResearch.WordTrace tailWord_7515359 prefixEnd_7515359 3858991458093166857049999 := by
  unfold tailWord_7515359
  simp only [CollatzResearch.WordTrace]
  refine ⟨274107661580145338975973131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182738441053430225983982087 274107661580145338975973131)
  ·
    refine ⟨411161492370218008463959697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274107661580145338975973131 411161492370218008463959697)
    ·
      refine ⟨308371119277663506347969773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411161492370218008463959697 308371119277663506347969773)
      ·
        refine ⟨115639169729123814880488665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308371119277663506347969773 115639169729123814880488665)
        ·
          refine ⟨86729377296842861160366499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115639169729123814880488665 86729377296842861160366499)
          ·
            refine ⟨130094065945264291740549749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86729377296842861160366499 130094065945264291740549749)
            ·
              refine ⟨12196318682368527350676539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130094065945264291740549749 12196318682368527350676539)
              ·
                refine ⟨18294478023552791026014809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12196318682368527350676539 18294478023552791026014809)
                ·
                  refine ⟨13720858517664593269511107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18294478023552791026014809 13720858517664593269511107)
                  ·
                    refine ⟨20581287776496889904266661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13720858517664593269511107 20581287776496889904266661)
                    ·
                      refine ⟨3858991458093166857049999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20581287776496889904266661 3858991458093166857049999)
                      ·
                        rfl

theorem cell23_7515359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_7515359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515359 prefixEnd_7515359 := by exact prefixLift 7515359
  have htrace : WordTrace (prefixWord ++ tailWord_7515359) baseStart_7515359 baseEnd_7515359 := by
    simpa [prefixWord, tailWord_7515359, baseEnd_7515359] using wordTrace_append hprefix tailTrace_7515359
  have hstable : (prefixWord ++ tailWord_7515359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515359).length < 2 ^ (prefixWord ++ tailWord_7515359).sum := by decide
  have hdescent : baseEnd_7515359 < baseStart_7515359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515372 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 6]
def baseStart_7515372 : Nat := 118140960795 + 7515372 * 2 ^ 59
def prefixEnd_7515372 : Nat := 4983230072969 + 3 ^ 40 * 7515372 * 2
def baseEnd_7515372 : Nat := 3858998133341675306187439

theorem tailTrace_7515372 : CollatzResearch.WordTrace tailWord_7515372 prefixEnd_7515372 3858998133341675306187439 := by
  unfold tailWord_7515372
  simp only [CollatzResearch.WordTrace]
  refine ⟨137054067864549121098098185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182738757152732161464130913 137054067864549121098098185)
  ·
    refine ⟨102790550898411840823573639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137054067864549121098098185 102790550898411840823573639)
    ·
      refine ⟨154185826347617761235360459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102790550898411840823573639 154185826347617761235360459)
      ·
        refine ⟨231278739521426641853040689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154185826347617761235360459 231278739521426641853040689)
        ·
          refine ⟨173459054641069981389780517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231278739521426641853040689 173459054641069981389780517)
          ·
            refine ⟨32523572745200621510583847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173459054641069981389780517 32523572745200621510583847)
            ·
              refine ⟨48785359117800932265875771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32523572745200621510583847 48785359117800932265875771)
              ·
                refine ⟨73178038676701398398813657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48785359117800932265875771 73178038676701398398813657)
                ·
                  refine ⟨54883529007526048799110243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73178038676701398398813657 54883529007526048799110243)
                  ·
                    refine ⟨82325293511289073198665365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54883529007526048799110243 82325293511289073198665365)
                    ·
                      refine ⟨3858998133341675306187439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82325293511289073198665365 3858998133341675306187439)
                      ·
                        rfl

theorem cell23_7515372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_7515372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515372 prefixEnd_7515372 := by exact prefixLift 7515372
  have htrace : WordTrace (prefixWord ++ tailWord_7515372) baseStart_7515372 baseEnd_7515372 := by
    simpa [prefixWord, tailWord_7515372, baseEnd_7515372] using wordTrace_append hprefix tailTrace_7515372
  have hstable : (prefixWord ++ tailWord_7515372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515372).length < 2 ^ (prefixWord ++ tailWord_7515372).sum := by decide
  have hdescent : baseEnd_7515372 < baseStart_7515372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515386 : List Nat := [3, 1, 1, 1, 1, 4, 1, 6, 1, 4]
def baseStart_7515386 : Nat := 118140960795 + 7515386 * 2 ^ 59
def prefixEnd_7515386 : Nat := 4983230072969 + 3 ^ 40 * 7515386 * 2
def baseEnd_7515386 : Nat := 1286335107356946083804125

theorem tailTrace_7515386 : CollatzResearch.WordTrace tailWord_7515386 prefixEnd_7515386 1286335107356946083804125 := by
  unfold tailWord_7515386
  simp only [CollatzResearch.WordTrace]
  refine ⟨68527161587761880646801503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182739097567365015058137341 68527161587761880646801503)
  ·
    refine ⟨102790742381642820970202255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68527161587761880646801503 102790742381642820970202255)
    ·
      refine ⟨154186113572464231455303383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102790742381642820970202255 154186113572464231455303383)
      ·
        refine ⟨231279170358696347182955075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154186113572464231455303383 231279170358696347182955075)
        ·
          refine ⟨346918755538044520774432613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231279170358696347182955075 346918755538044520774432613)
          ·
            refine ⟨65047266663383347645206115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 346918755538044520774432613 65047266663383347645206115)
            ·
              refine ⟨97570899995075021467809173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65047266663383347645206115 97570899995075021467809173)
              ·
                refine ⟨4573635937269141631303555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97570899995075021467809173 4573635937269141631303555)
                ·
                  refine ⟨6860453905903712446955333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4573635937269141631303555 6860453905903712446955333)
                  ·
                    refine ⟨1286335107356946083804125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6860453905903712446955333 1286335107356946083804125)
                    ·
                      rfl

theorem cell23_7515386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 1, 4].length) (baseStart_7515386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515386 prefixEnd_7515386 := by exact prefixLift 7515386
  have htrace : WordTrace (prefixWord ++ tailWord_7515386) baseStart_7515386 baseEnd_7515386 := by
    simpa [prefixWord, tailWord_7515386, baseEnd_7515386] using wordTrace_append hprefix tailTrace_7515386
  have hstable : (prefixWord ++ tailWord_7515386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515386).length < 2 ^ (prefixWord ++ tailWord_7515386).sum := by decide
  have hdescent : baseEnd_7515386 < baseStart_7515386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515402 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_7515402 : Nat := 118140960795 + 7515402 * 2 ^ 59
def prefixEnd_7515402 : Nat := 4983230072969 + 3 ^ 40 * 7515402 * 2
def baseEnd_7515402 : Nat := 3859013537761310188812301

theorem tailTrace_7515402 : CollatzResearch.WordTrace tailWord_7515402 prefixEnd_7515402 3859013537761310188812301 := by
  unfold tailWord_7515402
  simp only [CollatzResearch.WordTrace]
  refine ⟨68527307479747389329947115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182739486612659704879858973 68527307479747389329947115)
  ·
    refine ⟨102790961219621083994920673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68527307479747389329947115 102790961219621083994920673)
    ·
      refine ⟨77093220914715812996190505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102790961219621083994920673 77093220914715812996190505)
      ·
        refine ⟨57819915686036859747142879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77093220914715812996190505 57819915686036859747142879)
        ·
          refine ⟨86729873529055289620714319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57819915686036859747142879 86729873529055289620714319)
          ·
            refine ⟨130094810293582934431071479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86729873529055289620714319 130094810293582934431071479)
            ·
              refine ⟨195142215440374401646607219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130094810293582934431071479 195142215440374401646607219)
              ·
                refine ⟨292713323160561602469910829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195142215440374401646607219 292713323160561602469910829)
                ·
                  refine ⟨109767496185210600926216561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292713323160561602469910829 109767496185210600926216561)
                  ·
                    refine ⟨82325622138907950694662421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109767496185210600926216561 82325622138907950694662421)
                    ·
                      refine ⟨3859013537761310188812301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82325622138907950694662421 3859013537761310188812301)
                      ·
                        rfl

theorem cell23_7515402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_7515402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515402 prefixEnd_7515402 := by exact prefixLift 7515402
  have htrace : WordTrace (prefixWord ++ tailWord_7515402) baseStart_7515402 baseEnd_7515402 := by
    simpa [prefixWord, tailWord_7515402, baseEnd_7515402] using wordTrace_append hprefix tailTrace_7515402
  have hstable : (prefixWord ++ tailWord_7515402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515402).length < 2 ^ (prefixWord ++ tailWord_7515402).sum := by decide
  have hdescent : baseEnd_7515402 < baseStart_7515402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515437 : List Nat := [1, 5, 3, 1, 1, 2, 3, 2, 1, 4]
def baseStart_7515437 : Nat := 118140960795 + 7515437 * 2 ^ 59
def prefixEnd_7515437 : Nat := 4983230072969 + 3 ^ 40 * 7515437 * 2
def baseEnd_7515437 : Nat := 1286343836528072517291547

theorem tailTrace_7515437 : CollatzResearch.WordTrace tailWord_7515437 prefixEnd_7515437 1286343836528072517291547 := by
  unfold tailWord_7515437
  simp only [CollatzResearch.WordTrace]
  refine ⟨274110506473862758297312565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182740337649241838864875043 274110506473862758297312565)
  ·
    refine ⟨25697859981924633590373053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 274110506473862758297312565 25697859981924633590373053)
    ·
      refine ⟨9636697493221737596389895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25697859981924633590373053 9636697493221737596389895)
      ·
        refine ⟨14455046239832606394584843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9636697493221737596389895 14455046239832606394584843)
        ·
          refine ⟨21682569359748909591877265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14455046239832606394584843 21682569359748909591877265)
          ·
            refine ⟨16261927019811682193907949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21682569359748909591877265 16261927019811682193907949)
            ·
              refine ⟨6098222632429380822715481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16261927019811682193907949 6098222632429380822715481)
              ·
                refine ⟨4573666974322035617036611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6098222632429380822715481 4573666974322035617036611)
                ·
                  refine ⟨6860500461483053425554917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4573666974322035617036611 6860500461483053425554917)
                  ·
                    refine ⟨1286343836528072517291547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6860500461483053425554917 1286343836528072517291547)
                    ·
                      rfl

theorem cell23_7515437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_7515437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515437 prefixEnd_7515437 := by exact prefixLift 7515437
  have htrace : WordTrace (prefixWord ++ tailWord_7515437) baseStart_7515437 baseEnd_7515437 := by
    simpa [prefixWord, tailWord_7515437, baseEnd_7515437] using wordTrace_append hprefix tailTrace_7515437
  have hstable : (prefixWord ++ tailWord_7515437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515437).length < 2 ^ (prefixWord ++ tailWord_7515437).sum := by decide
  have hdescent : baseEnd_7515437 < baseStart_7515437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515443 : List Nat := [1, 1, 1, 2, 5, 4, 1, 1, 3, 1, 3]
def baseStart_7515443 : Nat := 118140960795 + 7515443 * 2 ^ 59
def prefixEnd_7515443 : Nat := 4983230072969 + 3 ^ 40 * 7515443 * 2
def baseEnd_7515443 : Nat := 3859034590468144528399613

theorem tailTrace_7515443 : CollatzResearch.WordTrace tailWord_7515443 prefixEnd_7515443 3859034590468144528399613 := by
  unfold tailWord_7515443
  simp only [CollatzResearch.WordTrace]
  refine ⟨274110725311841021322030983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182740483541227347548020655 274110725311841021322030983)
  ·
    refine ⟨411166087967761531983046475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274110725311841021322030983 411166087967761531983046475)
    ·
      refine ⟨616749131951642297974569713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411166087967761531983046475 616749131951642297974569713)
      ·
        refine ⟨462561848963731723480927285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616749131951642297974569713 462561848963731723480927285)
        ·
          refine ⟨43365173340349849076336933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 462561848963731723480927285 43365173340349849076336933)
          ·
            refine ⟨8130970001315596701813175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43365173340349849076336933 8130970001315596701813175)
            ·
              refine ⟨12196455001973395052719763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8130970001315596701813175 12196455001973395052719763)
              ·
                refine ⟨18294682502960092579079645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12196455001973395052719763 18294682502960092579079645)
                ·
                  refine ⟨6860505938610034717154867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18294682502960092579079645 6860505938610034717154867)
                  ·
                    refine ⟨10290758907915052075732301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6860505938610034717154867 10290758907915052075732301)
                    ·
                      refine ⟨3859034590468144528399613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10290758907915052075732301 3859034590468144528399613)
                      ·
                        rfl

theorem cell23_7515443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 1, 3].length) (baseStart_7515443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515443 prefixEnd_7515443 := by exact prefixLift 7515443
  have htrace : WordTrace (prefixWord ++ tailWord_7515443) baseStart_7515443 baseEnd_7515443 := by
    simpa [prefixWord, tailWord_7515443, baseEnd_7515443] using wordTrace_append hprefix tailTrace_7515443
  have hstable : (prefixWord ++ tailWord_7515443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515443).length < 2 ^ (prefixWord ++ tailWord_7515443).sum := by decide
  have hdescent : baseEnd_7515443 < baseStart_7515443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515472 : List Nat := [2, 1, 1, 1, 1, 5, 1, 11]
def baseStart_7515472 : Nat := 118140960795 + 7515472 * 2 ^ 59
def prefixEnd_7515472 : Nat := 4983230072969 + 3 ^ 40 * 7515472 * 2
def baseEnd_7515472 : Nat := 142927758570634256108777

theorem tailTrace_7515472 : CollatzResearch.WordTrace tailWord_7515472 prefixEnd_7515472 142927758570634256108777 := by
  unfold tailWord_7515472
  simp only [CollatzResearch.WordTrace]
  refine ⟨137055891514367979637418335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182741188685823972849891113 137055891514367979637418335)
  ·
    refine ⟨205583837271551969456127503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137055891514367979637418335 205583837271551969456127503)
    ·
      refine ⟨308375755907327954184191255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205583837271551969456127503 308375755907327954184191255)
      ·
        refine ⟨462563633860991931276286883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308375755907327954184191255 462563633860991931276286883)
        ·
          refine ⟨693845450791487896914430325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462563633860991931276286883 693845450791487896914430325)
          ·
            refine ⟨65048011011701990335727843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 693845450791487896914430325 65048011011701990335727843)
            ·
              refine ⟨97572016517552985503591765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65048011011701990335727843 97572016517552985503591765)
              ·
                refine ⟨142927758570634256108777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 97572016517552985503591765 142927758570634256108777)
                ·
                  rfl

theorem cell23_7515472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 11].length) (baseStart_7515472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515472 prefixEnd_7515472 := by exact prefixLift 7515472
  have htrace : WordTrace (prefixWord ++ tailWord_7515472) baseStart_7515472 baseEnd_7515472 := by
    simpa [prefixWord, tailWord_7515472, baseEnd_7515472] using wordTrace_append hprefix tailTrace_7515472
  have hstable : (prefixWord ++ tailWord_7515472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515472).length < 2 ^ (prefixWord ++ tailWord_7515472).sum := by decide
  have hdescent : baseEnd_7515472 < baseStart_7515472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515479 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 4]
def baseStart_7515479 : Nat := 118140960795 + 7515479 * 2 ^ 59
def prefixEnd_7515479 : Nat := 4983230072969 + 3 ^ 40 * 7515479 * 2
def baseEnd_7515479 : Nat := 3859053075771706387549447

theorem tailTrace_7515479 : CollatzResearch.WordTrace tailWord_7515479 prefixEnd_7515479 3859053075771706387549447 := by
  unfold tailWord_7515479
  simp only [CollatzResearch.WordTrace]
  refine ⟨274112038339710599470341491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182741358893140399646894327 274112038339710599470341491)
  ·
    refine ⟨411168057509565899205512237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274112038339710599470341491 411168057509565899205512237)
    ·
      refine ⟨154188021566087212202067089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411168057509565899205512237 154188021566087212202067089)
      ·
        refine ⟨115641016174565409151550317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154188021566087212202067089 115641016174565409151550317)
        ·
          refine ⟨43365381065462028431831369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115641016174565409151550317 43365381065462028431831369)
          ·
            refine ⟨32524035799096521323873527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43365381065462028431831369 32524035799096521323873527)
            ·
              refine ⟨48786053698644781985810291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32524035799096521323873527 48786053698644781985810291)
              ·
                refine ⟨73179080547967172978715437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48786053698644781985810291 73179080547967172978715437)
                ·
                  refine ⟨27442155205487689867018289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73179080547967172978715437 27442155205487689867018289)
                  ·
                    refine ⟨20581616404115767400263717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27442155205487689867018289 20581616404115767400263717)
                    ·
                      refine ⟨3859053075771706387549447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20581616404115767400263717 3859053075771706387549447)
                      ·
                        rfl

theorem cell23_7515479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_7515479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515479 prefixEnd_7515479 := by exact prefixLift 7515479
  have htrace : WordTrace (prefixWord ++ tailWord_7515479) baseStart_7515479 baseEnd_7515479 := by
    simpa [prefixWord, tailWord_7515479, baseEnd_7515479] using wordTrace_append hprefix tailTrace_7515479
  have hstable : (prefixWord ++ tailWord_7515479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515479).length < 2 ^ (prefixWord ++ tailWord_7515479).sum := by decide
  have hdescent : baseEnd_7515479 < baseStart_7515479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515516 : List Nat := [2, 2, 2, 1, 1, 1, 6, 1, 1, 3, 3]
def baseStart_7515516 : Nat := 118140960795 + 7515516 * 2 ^ 59
def prefixEnd_7515516 : Nat := 4983230072969 + 3 ^ 40 * 7515516 * 2
def baseEnd_7515516 : Nat := 3859072074555922742786777

theorem tailTrace_7515516 : CollatzResearch.WordTrace tailWord_7515516 prefixEnd_7515516 3859072074555922742786777 := by
  unfold tailWord_7515516
  simp only [CollatzResearch.WordTrace]
  refine ⟨137056693920288277394719201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182742258560384369859625601 137056693920288277394719201)
  ·
    refine ⟨102792520440216208046039401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137056693920288277394719201 102792520440216208046039401)
    ·
      refine ⟨77094390330162156034529551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102792520440216208046039401 77094390330162156034529551)
      ·
        refine ⟨115641585495243234051794327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77094390330162156034529551 115641585495243234051794327)
        ·
          refine ⟨173462378242864851077691491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115641585495243234051794327 173462378242864851077691491)
          ·
            refine ⟨260193567364297276616537237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173462378242864851077691491 260193567364297276616537237)
            ·
              refine ⟨12196573470201434841400183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 260193567364297276616537237 12196573470201434841400183)
              ·
                refine ⟨18294860205302152262100275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12196573470201434841400183 18294860205302152262100275)
                ·
                  refine ⟨27442290307953228393150413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18294860205302152262100275 27442290307953228393150413)
                  ·
                    refine ⟨10290858865482460647431405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27442290307953228393150413 10290858865482460647431405)
                    ·
                      refine ⟨3859072074555922742786777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10290858865482460647431405 3859072074555922742786777)
                      ·
                        rfl

theorem cell23_7515516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_7515516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515516 prefixEnd_7515516 := by exact prefixLift 7515516
  have htrace : WordTrace (prefixWord ++ tailWord_7515516) baseStart_7515516 baseEnd_7515516 := by
    simpa [prefixWord, tailWord_7515516, baseEnd_7515516] using wordTrace_append hprefix tailTrace_7515516
  have hstable : (prefixWord ++ tailWord_7515516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515516).length < 2 ^ (prefixWord ++ tailWord_7515516).sum := by decide
  have hdescent : baseEnd_7515516 < baseStart_7515516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515534 : List Nat := [4, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2]
def baseStart_7515534 : Nat := 118140960795 + 7515534 * 2 ^ 59
def prefixEnd_7515534 : Nat := 4983230072969 + 3 ^ 40 * 7515534 * 2
def baseEnd_7515534 : Nat := 3859081317207703672361695

theorem tailTrace_7515534 : CollatzResearch.WordTrace tailWord_7515534 prefixEnd_7515534 3859081317207703672361695 := by
  unfold tailWord_7515534
  simp only [CollatzResearch.WordTrace]
  refine ⟨34264255544313917982949207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182742696236340895909062437 34264255544313917982949207)
  ·
    refine ⟨51396383316470876974423811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34264255544313917982949207 51396383316470876974423811)
    ·
      refine ⟨77094574974706315461635717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51396383316470876974423811 77094574974706315461635717)
      ·
        refine ⟨14455232807757434149056697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77094574974706315461635717 14455232807757434149056697)
        ·
          refine ⟨10841424605818075611792523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14455232807757434149056697 10841424605818075611792523)
          ·
            refine ⟨16262136908727113417688785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10841424605818075611792523 16262136908727113417688785)
            ·
              refine ⟨12196602681545335063266589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16262136908727113417688785 12196602681545335063266589)
              ·
                refine ⟨4573726005579500648724971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12196602681545335063266589 4573726005579500648724971)
                ·
                  refine ⟨6860589008369250973087457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4573726005579500648724971 6860589008369250973087457)
                  ·
                    refine ⟨5145441756276938229815593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6860589008369250973087457 5145441756276938229815593)
                    ·
                      refine ⟨3859081317207703672361695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5145441756276938229815593 3859081317207703672361695)
                      ·
                        rfl

theorem cell23_7515534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_7515534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515534 prefixEnd_7515534 := by exact prefixLift 7515534
  have htrace : WordTrace (prefixWord ++ tailWord_7515534) baseStart_7515534 baseEnd_7515534 := by
    simpa [prefixWord, tailWord_7515534, baseEnd_7515534] using wordTrace_append hprefix tailTrace_7515534
  have hstable : (prefixWord ++ tailWord_7515534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515534).length < 2 ^ (prefixWord ++ tailWord_7515534).sum := by decide
  have hdescent : baseEnd_7515534 < baseStart_7515534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515613 : List Nat := [1, 4, 3, 1, 1, 4, 1, 1, 7]
def baseStart_7515613 : Nat := 118140960795 + 7515613 * 2 ^ 59
def prefixEnd_7515613 : Nat := 4983230072969 + 3 ^ 40 * 7515613 * 2
def baseEnd_7515613 : Nat := 428791320242156540363759

theorem tailTrace_7515613 : CollatzResearch.WordTrace tailWord_7515613 prefixEnd_7515613 428791320242156540363759 := by
  unfold tailWord_7515613
  simp only [CollatzResearch.WordTrace]
  refine ⟨274116925721225140355719493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182744617147483426903812995 274116925721225140355719493)
  ·
    refine ⟨51396923572729713816697405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274116925721225140355719493 51396923572729713816697405)
    ·
      refine ⟨19273846339773642681261527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51396923572729713816697405 19273846339773642681261527)
      ·
        refine ⟨28910769509660464021892291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19273846339773642681261527 28910769509660464021892291)
        ·
          refine ⟨43366154264490696032838437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28910769509660464021892291 43366154264490696032838437)
          ·
            refine ⟨8131153924592005506157207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43366154264490696032838437 8131153924592005506157207)
            ·
              refine ⟨12196730886888008259235811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8131153924592005506157207 12196730886888008259235811)
              ·
                refine ⟨18295096330332012388853717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12196730886888008259235811 18295096330332012388853717)
                ·
                  refine ⟨428791320242156540363759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18295096330332012388853717 428791320242156540363759)
                  ·
                    rfl

theorem cell23_7515613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_7515613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515613 prefixEnd_7515613 := by exact prefixLift 7515613
  have htrace : WordTrace (prefixWord ++ tailWord_7515613) baseStart_7515613 baseEnd_7515613 := by
    simpa [prefixWord, tailWord_7515613, baseEnd_7515613] using wordTrace_append hprefix tailTrace_7515613
  have hstable : (prefixWord ++ tailWord_7515613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515613).length < 2 ^ (prefixWord ++ tailWord_7515613).sum := by decide
  have hdescent : baseEnd_7515613 < baseStart_7515613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515680 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 2, 4, 2]
def baseStart_7515680 : Nat := 118140960795 + 7515680 * 2 ^ 59
def prefixEnd_7515680 : Nat := 4983230072969 + 3 ^ 40 * 7515680 * 2
def baseEnd_7515680 : Nat := 3859156285383260101136023

theorem tailTrace_7515680 : CollatzResearch.WordTrace tailWord_7515680 prefixEnd_7515680 3859156285383260101136023 := by
  unfold tailWord_7515680
  simp only [CollatzResearch.WordTrace]
  refine ⟨137059684705991205399204247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182746246274654940532272329 137059684705991205399204247)
  ·
    refine ⟨205589527058986808098806371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137059684705991205399204247 205589527058986808098806371)
    ·
      refine ⟨308384290588480212148209557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205589527058986808098806371 308384290588480212148209557)
      ·
        refine ⟨14455513621335009944447323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 308384290588480212148209557 14455513621335009944447323)
        ·
          refine ⟨21683270432002514916670985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14455513621335009944447323 21683270432002514916670985)
          ·
            refine ⟨16262452824001886187503239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21683270432002514916670985 16262452824001886187503239)
            ·
              refine ⟨24393679236002829281254859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16262452824001886187503239 24393679236002829281254859)
              ·
                refine ⟨36590518854004243921882289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24393679236002829281254859 36590518854004243921882289)
                ·
                  refine ⟨27442889140503182941411717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36590518854004243921882289 27442889140503182941411717)
                  ·
                    refine ⟨5145541713844346801514697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27442889140503182941411717 5145541713844346801514697)
                    ·
                      refine ⟨3859156285383260101136023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5145541713844346801514697 3859156285383260101136023)
                      ·
                        rfl

theorem cell23_7515680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_7515680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515680 prefixEnd_7515680 := by exact prefixLift 7515680
  have htrace : WordTrace (prefixWord ++ tailWord_7515680) baseStart_7515680 baseEnd_7515680 := by
    simpa [prefixWord, tailWord_7515680, baseEnd_7515680] using wordTrace_append hprefix tailTrace_7515680
  have hstable : (prefixWord ++ tailWord_7515680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515680).length < 2 ^ (prefixWord ++ tailWord_7515680).sum := by decide
  have hdescent : baseEnd_7515680 < baseStart_7515680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515723 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 4, 3, 2]
def baseStart_7515723 : Nat := 118140960795 + 7515723 * 2 ^ 59
def prefixEnd_7515723 : Nat := 4983230072969 + 3 ^ 40 * 7515723 * 2
def baseEnd_7515723 : Nat := 3859178365051403432898325

theorem tailTrace_7515723 : CollatzResearch.WordTrace tailWord_7515723 prefixEnd_7515723 3859178365051403432898325 := by
  unfold tailWord_7515723
  simp only [CollatzResearch.WordTrace]
  refine ⟨274120937750826629142223823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182747291833884419428149215 274120937750826629142223823)
  ·
    refine ⟨411181406626239943713335735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274120937750826629142223823 411181406626239943713335735)
    ·
      refine ⟨616772109939359915570003603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411181406626239943713335735 616772109939359915570003603)
      ·
        refine ⟨925158164909039873355005405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616772109939359915570003603 925158164909039873355005405)
        ·
          refine ⟨346934311840889952508127027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 925158164909039873355005405 346934311840889952508127027)
          ·
            refine ⟨520401467761334928762190541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346934311840889952508127027 520401467761334928762190541)
            ·
              refine ⟨195150550410500598285821453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 520401467761334928762190541 195150550410500598285821453)
              ·
                refine ⟨73181456403937724357183045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195150550410500598285821453 73181456403937724357183045)
                ·
                  refine ⟨13721523075738323316971821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73181456403937724357183045 13721523075738323316971821)
                  ·
                    refine ⟨5145571153401871243864433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13721523075738323316971821 5145571153401871243864433)
                    ·
                      refine ⟨3859178365051403432898325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5145571153401871243864433 3859178365051403432898325)
                      ·
                        rfl

theorem cell23_7515723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 3, 2].length) (baseStart_7515723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515723 prefixEnd_7515723 := by exact prefixLift 7515723
  have htrace : WordTrace (prefixWord ++ tailWord_7515723) baseStart_7515723 baseEnd_7515723 := by
    simpa [prefixWord, tailWord_7515723, baseEnd_7515723] using wordTrace_append hprefix tailTrace_7515723
  have hstable : (prefixWord ++ tailWord_7515723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515723).length < 2 ^ (prefixWord ++ tailWord_7515723).sum := by decide
  have hdescent : baseEnd_7515723 < baseStart_7515723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515730 : List Nat := [3, 2, 2, 1, 2, 2, 1, 3, 3, 1, 3]
def baseStart_7515730 : Nat := 118140960795 + 7515730 * 2 ^ 59
def prefixEnd_7515730 : Nat := 4983230072969 + 3 ^ 40 * 7515730 * 2
def baseEnd_7515730 : Nat := 3859181959415984905510793

theorem tailTrace_7515730 : CollatzResearch.WordTrace tailWord_7515730 prefixEnd_7515730 3859181959415984905510793 := by
  unfold tailWord_7515730
  simp only [CollatzResearch.WordTrace]
  refine ⟨68530298265450317334432161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182747462041200846225152429 68530298265450317334432161)
  ·
    refine ⟨51397723699087738000824121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68530298265450317334432161 51397723699087738000824121)
    ·
      refine ⟨38548292774315803500618091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51397723699087738000824121 38548292774315803500618091)
      ·
        refine ⟨57822439161473705250927137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38548292774315803500618091 57822439161473705250927137)
        ·
          refine ⟨43366829371105278938195353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57822439161473705250927137 43366829371105278938195353)
          ·
            refine ⟨32525122028328959203646515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43366829371105278938195353 32525122028328959203646515)
            ·
              refine ⟨48787683042493438805469773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32525122028328959203646515 48787683042493438805469773)
              ·
                refine ⟨18295381140935039552051165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48787683042493438805469773 18295381140935039552051165)
                ·
                  refine ⟨6860767927850639832019187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18295381140935039552051165 6860767927850639832019187)
                  ·
                    refine ⟨10291151891775959748028781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6860767927850639832019187 10291151891775959748028781)
                    ·
                      refine ⟨3859181959415984905510793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10291151891775959748028781 3859181959415984905510793)
                      ·
                        rfl

theorem cell23_7515730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_7515730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515730 prefixEnd_7515730 := by exact prefixLift 7515730
  have htrace : WordTrace (prefixWord ++ tailWord_7515730) baseStart_7515730 baseEnd_7515730 := by
    simpa [prefixWord, tailWord_7515730, baseEnd_7515730] using wordTrace_append hprefix tailTrace_7515730
  have hstable : (prefixWord ++ tailWord_7515730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515730).length < 2 ^ (prefixWord ++ tailWord_7515730).sum := by decide
  have hdescent : baseEnd_7515730 < baseStart_7515730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515740 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 1, 5, 2]
def baseStart_7515740 : Nat := 118140960795 + 7515740 * 2 ^ 59
def prefixEnd_7515740 : Nat := 4983230072969 + 3 ^ 40 * 7515740 * 2
def baseEnd_7515740 : Nat := 3859187094222529866385747

theorem tailTrace_7515740 : CollatzResearch.WordTrace tailWord_7515740 prefixEnd_7515740 3859187094222529866385747 := by
  unfold tailWord_7515740
  simp only [CollatzResearch.WordTrace]
  refine ⟨137060778895882520522796337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182747705194510027363728449 137060778895882520522796337)
  ·
    refine ⟨102795584171911890392097253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137060778895882520522796337 102795584171911890392097253)
    ·
      refine ⟨19274172032233479448518235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102795584171911890392097253 19274172032233479448518235)
      ·
        refine ⟨28911258048350219172777353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19274172032233479448518235 28911258048350219172777353)
        ·
          refine ⟨21683443536262664379583015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28911258048350219172777353 21683443536262664379583015)
          ·
            refine ⟨32525165304393996569374523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21683443536262664379583015 32525165304393996569374523)
            ·
              refine ⟨48787747956590994854061785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32525165304393996569374523 48787747956590994854061785)
              ·
                refine ⟨36590810967443246140546339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48787747956590994854061785 36590810967443246140546339)
                ·
                  refine ⟨54886216451164869210819509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36590810967443246140546339 54886216451164869210819509)
                  ·
                    refine ⟨5145582792296706488514329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54886216451164869210819509 5145582792296706488514329)
                    ·
                      refine ⟨3859187094222529866385747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5145582792296706488514329 3859187094222529866385747)
                      ·
                        rfl

theorem cell23_7515740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_7515740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515740 prefixEnd_7515740 := by exact prefixLift 7515740
  have htrace : WordTrace (prefixWord ++ tailWord_7515740) baseStart_7515740 baseEnd_7515740 := by
    simpa [prefixWord, tailWord_7515740, baseEnd_7515740] using wordTrace_append hprefix tailTrace_7515740
  have hstable : (prefixWord ++ tailWord_7515740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515740).length < 2 ^ (prefixWord ++ tailWord_7515740).sum := by decide
  have hdescent : baseEnd_7515740 < baseStart_7515740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515753 : List Nat := [1, 2, 1, 1, 1, 4, 3, 4, 1, 1, 4]
def baseStart_7515753 : Nat := 118140960795 + 7515753 * 2 ^ 59
def prefixEnd_7515753 : Nat := 4983230072969 + 3 ^ 40 * 7515753 * 2
def baseEnd_7515753 : Nat := 3859193769471038315523187

theorem tailTrace_7515753 : CollatzResearch.WordTrace tailWord_7515753 prefixEnd_7515753 3859193769471038315523187 := by
  unfold tailWord_7515753
  simp only [CollatzResearch.WordTrace]
  refine ⟨274122031940717944265815913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182748021293811962843877275 274122031940717944265815913)
  ·
    refine ⟨205591523955538458199361935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274122031940717944265815913 205591523955538458199361935)
    ·
      refine ⟨308387285933307687299042903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205591523955538458199361935 308387285933307687299042903)
      ·
        refine ⟨462580928899961530948564355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308387285933307687299042903 462580928899961530948564355)
        ·
          refine ⟨693871393349942296422846533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462580928899961530948564355 693871393349942296422846533)
          ·
            refine ⟨130100886253114180579283725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 693871393349942296422846533 130100886253114180579283725)
            ·
              refine ⟨48787832344917817717231397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130100886253114180579283725 48787832344917817717231397)
              ·
                refine ⟨9147718564672090821980887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48787832344917817717231397 9147718564672090821980887)
                ·
                  refine ⟨13721577847008136232971331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9147718564672090821980887 13721577847008136232971331)
                  ·
                    refine ⟨20582366770512204349456997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13721577847008136232971331 20582366770512204349456997)
                    ·
                      refine ⟨3859193769471038315523187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20582366770512204349456997 3859193769471038315523187)
                      ·
                        rfl

theorem cell23_7515753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 1, 4].length) (baseStart_7515753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515753 prefixEnd_7515753 := by exact prefixLift 7515753
  have htrace : WordTrace (prefixWord ++ tailWord_7515753) baseStart_7515753 baseEnd_7515753 := by
    simpa [prefixWord, tailWord_7515753, baseEnd_7515753] using wordTrace_append hprefix tailTrace_7515753
  have hstable : (prefixWord ++ tailWord_7515753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515753).length < 2 ^ (prefixWord ++ tailWord_7515753).sum := by decide
  have hdescent : baseEnd_7515753 < baseStart_7515753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515756 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 5]
def baseStart_7515756 : Nat := 118140960795 + 7515756 * 2 ^ 59
def prefixEnd_7515756 : Nat := 4983230072969 + 3 ^ 40 * 7515756 * 2
def baseEnd_7515756 : Nat := 3859195309913001803785673

theorem tailTrace_7515756 : CollatzResearch.WordTrace tailWord_7515756 prefixEnd_7515756 3859195309913001803785673 := by
  unfold tailWord_7515756
  simp only [CollatzResearch.WordTrace]
  refine ⟨137061070679853537889087561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182748094239804717185450081 137061070679853537889087561)
  ·
    refine ⟨102795803009890153416815671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137061070679853537889087561 102795803009890153416815671)
    ·
      refine ⟨154193704514835230125223507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102795803009890153416815671 154193704514835230125223507)
      ·
        refine ⟨231290556772252845187835261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154193704514835230125223507 231290556772252845187835261)
        ·
          refine ⟨86733958789594816945438223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231290556772252845187835261 86733958789594816945438223)
          ·
            refine ⟨130100938184392225418157335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86733958789594816945438223 130100938184392225418157335)
            ·
              refine ⟨195151407276588338127236003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130100938184392225418157335 195151407276588338127236003)
              ·
                refine ⟨292727110914882507190854005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195151407276588338127236003 292727110914882507190854005)
                ·
                  refine ⟨27443166648270235049142563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 292727110914882507190854005 27443166648270235049142563)
                  ·
                    refine ⟨41164749972405352573713845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27443166648270235049142563 41164749972405352573713845)
                    ·
                      refine ⟨3859195309913001803785673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41164749972405352573713845 3859195309913001803785673)
                      ·
                        rfl

theorem cell23_7515756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_7515756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515756 prefixEnd_7515756 := by exact prefixLift 7515756
  have htrace : WordTrace (prefixWord ++ tailWord_7515756) baseStart_7515756 baseEnd_7515756 := by
    simpa [prefixWord, tailWord_7515756, baseEnd_7515756] using wordTrace_append hprefix tailTrace_7515756
  have hstable : (prefixWord ++ tailWord_7515756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515756).length < 2 ^ (prefixWord ++ tailWord_7515756).sum := by decide
  have hdescent : baseEnd_7515756 < baseStart_7515756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515773 : List Nat := [1, 4, 1, 1, 4, 1, 1, 3, 1, 1, 5]
def baseStart_7515773 : Nat := 118140960795 + 7515773 * 2 ^ 59
def prefixEnd_7515773 : Nat := 4983230072969 + 3 ^ 40 * 7515773 * 2
def baseEnd_7515773 : Nat := 3859204039084128237273095

theorem tailTrace_7515773 : CollatzResearch.WordTrace tailWord_7515773 prefixEnd_7515773 3859204039084128237273095 := by
  unfold tailWord_7515773
  simp only [CollatzResearch.WordTrace]
  refine ⟨274122761400645487681543973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182748507600430325121029315 274122761400645487681543973)
  ·
    refine ⟨51398017762621028940289495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274122761400645487681543973 51398017762621028940289495)
    ·
      refine ⟨77097026643931543410434243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51398017762621028940289495 77097026643931543410434243)
      ·
        refine ⟨115645539965897315115651365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77097026643931543410434243 115645539965897315115651365)
        ·
          refine ⟨21683538743605746584184631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115645539965897315115651365 21683538743605746584184631)
          ·
            refine ⟨32525308115408619876276947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21683538743605746584184631 32525308115408619876276947)
            ·
              refine ⟨48787962173112929814415421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32525308115408619876276947 48787962173112929814415421)
              ·
                refine ⟨18295485814917348680405783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48787962173112929814415421 18295485814917348680405783)
                ·
                  refine ⟨27443228722376023020608675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18295485814917348680405783 27443228722376023020608675)
                  ·
                    refine ⟨41164843083564034530913013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27443228722376023020608675 41164843083564034530913013)
                    ·
                      refine ⟨3859204039084128237273095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41164843083564034530913013 3859204039084128237273095)
                      ·
                        rfl

theorem cell23_7515773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_7515773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515773 prefixEnd_7515773 := by exact prefixLift 7515773
  have htrace : WordTrace (prefixWord ++ tailWord_7515773) baseStart_7515773 baseEnd_7515773 := by
    simpa [prefixWord, tailWord_7515773, baseEnd_7515773] using wordTrace_append hprefix tailTrace_7515773
  have hstable : (prefixWord ++ tailWord_7515773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515773).length < 2 ^ (prefixWord ++ tailWord_7515773).sum := by decide
  have hdescent : baseEnd_7515773 < baseStart_7515773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515804 : List Nat := [2, 2, 3, 2, 4, 1, 1, 2, 1, 1, 4]
def baseStart_7515804 : Nat := 118140960795 + 7515804 * 2 ^ 59
def prefixEnd_7515804 : Nat := 4983230072969 + 3 ^ 40 * 7515804 * 2
def baseEnd_7515804 : Nat := 3859219956984417615985453

theorem tailTrace_7515804 : CollatzResearch.WordTrace tailWord_7515804 prefixEnd_7515804 3859219956984417615985453 := by
  unfold tailWord_7515804
  simp only [CollatzResearch.WordTrace]
  refine ⟨137061946031766589987961233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182749261375688786650614977 137061946031766589987961233)
  ·
    refine ⟨102796459523824942490970925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137061946031766589987961233 102796459523824942490970925)
    ·
      refine ⟨38548672321434353434114097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102796459523824942490970925 38548672321434353434114097)
      ·
        refine ⟨28911504241075765075585573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38548672321434353434114097 28911504241075765075585573)
        ·
          refine ⟨5420907045201705951672295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28911504241075765075585573 5420907045201705951672295)
          ·
            refine ⟨8131360567802558927508443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5420907045201705951672295 8131360567802558927508443)
            ·
              refine ⟨12197040851703838391262665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8131360567802558927508443 12197040851703838391262665)
              ·
                refine ⟨9147780638777878793446999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12197040851703838391262665 9147780638777878793446999)
                ·
                  refine ⟨13721670958166818190170499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9147780638777878793446999 13721670958166818190170499)
                  ·
                    refine ⟨20582506437250227285255749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13721670958166818190170499 20582506437250227285255749)
                    ·
                      refine ⟨3859219956984417615985453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20582506437250227285255749 3859219956984417615985453)
                      ·
                        rfl

theorem cell23_7515804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_7515804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515804 prefixEnd_7515804 := by exact prefixLift 7515804
  have htrace : WordTrace (prefixWord ++ tailWord_7515804) baseStart_7515804 baseEnd_7515804 := by
    simpa [prefixWord, tailWord_7515804, baseEnd_7515804] using wordTrace_append hprefix tailTrace_7515804
  have hstable : (prefixWord ++ tailWord_7515804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515804).length < 2 ^ (prefixWord ++ tailWord_7515804).sum := by decide
  have hdescent : baseEnd_7515804 < baseStart_7515804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515807 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 3, 2, 3]
def baseStart_7515807 : Nat := 118140960795 + 7515807 * 2 ^ 59
def prefixEnd_7515807 : Nat := 4983230072969 + 3 ^ 40 * 7515807 * 2
def baseEnd_7515807 : Nat := 3859221497426381104247939

theorem tailTrace_7515807 : CollatzResearch.WordTrace tailWord_7515807 prefixEnd_7515807 3859221497426381104247939 := by
  unfold tailWord_7515807
  simp only [CollatzResearch.WordTrace]
  refine ⟨274124001482522311488281675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182749334321681540992187783 274124001482522311488281675)
  ·
    refine ⟨411186002223783467232422513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274124001482522311488281675 411186002223783467232422513)
    ·
      refine ⟨308389501667837600424316885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411186002223783467232422513 308389501667837600424316885)
      ·
        refine ⟨7227878945339943759944927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 308389501667837600424316885 7227878945339943759944927)
        ·
          refine ⟨10841818418009915639917391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7227878945339943759944927 10841818418009915639917391)
          ·
            refine ⟨16262727627014873459876087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10841818418009915639917391 16262727627014873459876087)
            ·
              refine ⟨24394091440522310189814131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16262727627014873459876087 24394091440522310189814131)
              ·
                refine ⟨36591137160783465284721197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24394091440522310189814131 36591137160783465284721197)
                ·
                  refine ⟨13721676435293799481770449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36591137160783465284721197 13721676435293799481770449)
                  ·
                    refine ⟨10291257326470349611327837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13721676435293799481770449 10291257326470349611327837)
                    ·
                      refine ⟨3859221497426381104247939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10291257326470349611327837 3859221497426381104247939)
                      ·
                        rfl

theorem cell23_7515807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_7515807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515807 prefixEnd_7515807 := by exact prefixLift 7515807
  have htrace : WordTrace (prefixWord ++ tailWord_7515807) baseStart_7515807 baseEnd_7515807 := by
    simpa [prefixWord, tailWord_7515807, baseEnd_7515807] using wordTrace_append hprefix tailTrace_7515807
  have hstable : (prefixWord ++ tailWord_7515807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515807).length < 2 ^ (prefixWord ++ tailWord_7515807).sum := by decide
  have hdescent : baseEnd_7515807 < baseStart_7515807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515837 : List Nat := [1, 4, 1, 2, 1, 2, 4, 2, 2, 1, 3]
def baseStart_7515837 : Nat := 118140960795 + 7515837 * 2 ^ 59
def prefixEnd_7515837 : Nat := 4983230072969 + 3 ^ 40 * 7515837 * 2
def baseEnd_7515837 : Nat := 3859236901846015986872801

theorem tailTrace_7515837 : CollatzResearch.WordTrace tailWord_7515837 prefixEnd_7515837 3859236901846015986872801 := by
  unfold tailWord_7515837
  simp only [CollatzResearch.WordTrace]
  refine ⟨274125095672413626611873765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182750063781609084407915843 274125095672413626611873765)
  ·
    refine ⟨51398455438577554989726331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274125095672413626611873765 51398455438577554989726331)
    ·
      refine ⟨77097683157866332484589497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51398455438577554989726331 77097683157866332484589497)
      ·
        refine ⟨57823262368399749363442123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77097683157866332484589497 57823262368399749363442123)
        ·
          refine ⟨86734893552599624045163185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57823262368399749363442123 86734893552599624045163185)
          ·
            refine ⟨65051170164449718033872389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86734893552599624045163185 65051170164449718033872389)
            ·
              refine ⟨12197094405834322131351073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65051170164449718033872389 12197094405834322131351073)
              ·
                refine ⟨9147820804375741598513305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12197094405834322131351073 9147820804375741598513305)
                ·
                  refine ⟨6860865603281806198884979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9147820804375741598513305 6860865603281806198884979)
                  ·
                    refine ⟨10291298404922709298327469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6860865603281806198884979 10291298404922709298327469)
                    ·
                      refine ⟨3859236901846015986872801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10291298404922709298327469 3859236901846015986872801)
                      ·
                        rfl

theorem cell23_7515837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_7515837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515837 prefixEnd_7515837 := by exact prefixLift 7515837
  have htrace : WordTrace (prefixWord ++ tailWord_7515837) baseStart_7515837 baseEnd_7515837 := by
    simpa [prefixWord, tailWord_7515837, baseEnd_7515837] using wordTrace_append hprefix tailTrace_7515837
  have hstable : (prefixWord ++ tailWord_7515837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515837).length < 2 ^ (prefixWord ++ tailWord_7515837).sum := by decide
  have hdescent : baseEnd_7515837 < baseStart_7515837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515838 : List Nat := [4, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2]
def baseStart_7515838 : Nat := 118140960795 + 7515838 * 2 ^ 59
def prefixEnd_7515838 : Nat := 4983230072969 + 3 ^ 40 * 7515838 * 2
def baseEnd_7515838 : Nat := 3859237415326670482960297

theorem tailTrace_7515838 : CollatzResearch.WordTrace tailWord_7515838 prefixEnd_7515838 3859237415326670482960297 := by
  unfold tailWord_7515838
  simp only [CollatzResearch.WordTrace]
  refine ⟨34265641518176250472832521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182750088096940002521773445 34265641518176250472832521)
  ·
    refine ⟨25699231138632187854624391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34265641518176250472832521 25699231138632187854624391)
    ·
      refine ⟨38548846707948281781936587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25699231138632187854624391 38548846707948281781936587)
      ·
        refine ⟨57823270061922422672904881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38548846707948281781936587 57823270061922422672904881)
        ·
          refine ⟨43367452546441817004678661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57823270061922422672904881 43367452546441817004678661)
          ·
            refine ⟨8131397352457840688377249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43367452546441817004678661 8131397352457840688377249)
            ·
              refine ⟨6098548014343380516282937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8131397352457840688377249 6098548014343380516282937)
              ·
                refine ⟨4573911010757535387212203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6098548014343380516282937 4573911010757535387212203)
                ·
                  refine ⟨6860866516136303080818305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4573911010757535387212203 6860866516136303080818305)
                  ·
                    refine ⟨5145649887102227310613729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6860866516136303080818305 5145649887102227310613729)
                    ·
                      refine ⟨3859237415326670482960297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5145649887102227310613729 3859237415326670482960297)
                      ·
                        rfl

theorem cell23_7515838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_7515838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515838 prefixEnd_7515838 := by exact prefixLift 7515838
  have htrace : WordTrace (prefixWord ++ tailWord_7515838) baseStart_7515838 baseEnd_7515838 := by
    simpa [prefixWord, tailWord_7515838, baseEnd_7515838] using wordTrace_append hprefix tailTrace_7515838
  have hstable : (prefixWord ++ tailWord_7515838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515838).length < 2 ^ (prefixWord ++ tailWord_7515838).sum := by decide
  have hdescent : baseEnd_7515838 < baseStart_7515838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515863 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 3]
def baseStart_7515863 : Nat := 118140960795 + 7515863 * 2 ^ 59
def prefixEnd_7515863 : Nat := 4983230072969 + 3 ^ 40 * 7515863 * 2
def baseEnd_7515863 : Nat := 3859250252343032885147681

theorem tailTrace_7515863 : CollatzResearch.WordTrace tailWord_7515863 prefixEnd_7515863 3859250252343032885147681 := by
  unfold tailWord_7515863
  simp only [CollatzResearch.WordTrace]
  refine ⟨274126043970319433052320243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182750695980212955368213495 274126043970319433052320243)
  ·
    refine ⟨411189065955479149578480365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274126043970319433052320243 411189065955479149578480365)
    ·
      refine ⟨154195899733304681091930137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411189065955479149578480365 154195899733304681091930137)
      ·
        refine ⟨115646924799978510818947603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154195899733304681091930137 115646924799978510818947603)
        ·
          refine ⟨173470387199967766228421405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115646924799978510818947603 173470387199967766228421405)
          ·
            refine ⟨65051395199987912335658027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173470387199967766228421405 65051395199987912335658027)
            ·
              refine ⟨97577092799981868503487041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65051395199987912335658027 97577092799981868503487041)
              ·
                refine ⟨73182819599986401377615281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97577092799981868503487041 73182819599986401377615281)
                ·
                  refine ⟨54887114699989801033211461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73182819599986401377615281 54887114699989801033211461)
                  ·
                    refine ⟨10291334006248087693727149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54887114699989801033211461 10291334006248087693727149)
                    ·
                      refine ⟨3859250252343032885147681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10291334006248087693727149 3859250252343032885147681)
                      ·
                        rfl

theorem cell23_7515863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_7515863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515863 prefixEnd_7515863 := by exact prefixLift 7515863
  have htrace : WordTrace (prefixWord ++ tailWord_7515863) baseStart_7515863 baseEnd_7515863 := by
    simpa [prefixWord, tailWord_7515863, baseEnd_7515863] using wordTrace_append hprefix tailTrace_7515863
  have hstable : (prefixWord ++ tailWord_7515863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515863).length < 2 ^ (prefixWord ++ tailWord_7515863).sum := by decide
  have hdescent : baseEnd_7515863 < baseStart_7515863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515877 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 4, 2, 2]
def baseStart_7515877 : Nat := 118140960795 + 7515877 * 2 ^ 59
def prefixEnd_7515877 : Nat := 4983230072969 + 3 ^ 40 * 7515877 * 2
def baseEnd_7515877 : Nat := 3859257441072195830372617

theorem tailTrace_7515877 : CollatzResearch.WordTrace tailWord_7515877 prefixEnd_7515877 3859257441072195830372617 := by
  unfold tailWord_7515877
  simp only [CollatzResearch.WordTrace]
  refine ⟨274126554592268713443329885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182751036394845808962219923 274126554592268713443329885)
  ·
    refine ⟨102797457972100767541248707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274126554592268713443329885 102797457972100767541248707)
    ·
      refine ⟨154196186958151151311873061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102797457972100767541248707 154196186958151151311873061)
      ·
        refine ⟨28911785054653340870976199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154196186958151151311873061 28911785054653340870976199)
        ·
          refine ⟨43367677581980011306464299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28911785054653340870976199 43367677581980011306464299)
          ·
            refine ⟨65051516372970016959696449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43367677581980011306464299 65051516372970016959696449)
            ·
              refine ⟨48788637279727512719772337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65051516372970016959696449 48788637279727512719772337)
              ·
                refine ⟨36591477959795634539829253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48788637279727512719772337 36591477959795634539829253)
                ·
                  refine ⟨6860902117461681476217985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36591477959795634539829253 6860902117461681476217985)
                  ·
                    refine ⟨5145676588096261107163489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6860902117461681476217985 5145676588096261107163489)
                    ·
                      refine ⟨3859257441072195830372617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5145676588096261107163489 3859257441072195830372617)
                      ·
                        rfl

theorem cell23_7515877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_7515877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515877 prefixEnd_7515877 := by exact prefixLift 7515877
  have htrace : WordTrace (prefixWord ++ tailWord_7515877) baseStart_7515877 baseEnd_7515877 := by
    simpa [prefixWord, tailWord_7515877, baseEnd_7515877] using wordTrace_append hprefix tailTrace_7515877
  have hstable : (prefixWord ++ tailWord_7515877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515877).length < 2 ^ (prefixWord ++ tailWord_7515877).sum := by decide
  have hdescent : baseEnd_7515877 < baseStart_7515877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515894 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2]
def baseStart_7515894 : Nat := 118140960795 + 7515894 * 2 ^ 59
def prefixEnd_7515894 : Nat := 4983230072969 + 3 ^ 40 * 7515894 * 2
def baseEnd_7515894 : Nat := 3859266170243322263860039

theorem tailTrace_7515894 : CollatzResearch.WordTrace tailWord_7515894 prefixEnd_7515894 3859266170243322263860039 := by
  unfold tailWord_7515894
  simp only [CollatzResearch.WordTrace]
  refine ⟨17132948414575445334168671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182751449755471416897799157 17132948414575445334168671)
  ·
    refine ⟨25699422621863168001253007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17132948414575445334168671 25699422621863168001253007)
    ·
      refine ⟨38549133932794752001879511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25699422621863168001253007 38549133932794752001879511)
      ·
        refine ⟨57823700899192128002819267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38549133932794752001879511 57823700899192128002819267)
        ·
          refine ⟨86735551348788192004228901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57823700899192128002819267 86735551348788192004228901)
          ·
            refine ⟨16262915877897786000792919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86735551348788192004228901 16262915877897786000792919)
            ·
              refine ⟨24394373816846679001189379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16262915877897786000792919 24394373816846679001189379)
              ·
                refine ⟨36591560725270018501784069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24394373816846679001189379 36591560725270018501784069)
                ·
                  refine ⟨6860917635988128469084513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36591560725270018501784069 6860917635988128469084513)
                  ·
                    refine ⟨5145688226991096351813385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6860917635988128469084513 5145688226991096351813385)
                    ·
                      refine ⟨3859266170243322263860039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5145688226991096351813385 3859266170243322263860039)
                      ·
                        rfl

theorem cell23_7515894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_7515894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515894 prefixEnd_7515894 := by exact prefixLift 7515894
  have htrace : WordTrace (prefixWord ++ tailWord_7515894) baseStart_7515894 baseEnd_7515894 := by
    simpa [prefixWord, tailWord_7515894, baseEnd_7515894] using wordTrace_append hprefix tailTrace_7515894
  have hstable : (prefixWord ++ tailWord_7515894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515894).length < 2 ^ (prefixWord ++ tailWord_7515894).sum := by decide
  have hdescent : baseEnd_7515894 < baseStart_7515894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515900 : List Nat := [2, 2, 2, 1, 3, 1, 1, 6, 5]
def baseStart_7515900 : Nat := 118140960795 + 7515900 * 2 ^ 59
def prefixEnd_7515900 : Nat := 4983230072969 + 3 ^ 40 * 7515900 * 2
def baseEnd_7515900 : Nat := 428807694569694360042779

theorem tailTrace_7515900 : CollatzResearch.WordTrace tailWord_7515900 prefixEnd_7515900 428807694569694360042779 := by
  unfold tailWord_7515900
  simp only [CollatzResearch.WordTrace]
  refine ⟨137063696735592694185708577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182751595647456925580944769 137063696735592694185708577)
  ·
    refine ⟨102797772551694520639281433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137063696735592694185708577 102797772551694520639281433)
    ·
      refine ⟨77098329413770890479461075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102797772551694520639281433 77098329413770890479461075)
      ·
        refine ⟨115647494120656335719191613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77098329413770890479461075 115647494120656335719191613)
        ·
          refine ⟨43367810295246125894696855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115647494120656335719191613 43367810295246125894696855)
          ·
            refine ⟨65051715442869188842045283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43367810295246125894696855 65051715442869188842045283)
            ·
              refine ⟨97577573164303783263067925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65051715442869188842045283 97577573164303783263067925)
              ·
                refine ⟨4573948742076739840456309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97577573164303783263067925 4573948742076739840456309)
                ·
                  refine ⟨428807694569694360042779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4573948742076739840456309 428807694569694360042779)
                  ·
                    rfl

theorem cell23_7515900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 5].length) (baseStart_7515900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515900 prefixEnd_7515900 := by exact prefixLift 7515900
  have htrace : WordTrace (prefixWord ++ tailWord_7515900) baseStart_7515900 baseEnd_7515900 := by
    simpa [prefixWord, tailWord_7515900, baseEnd_7515900] using wordTrace_append hprefix tailTrace_7515900
  have hstable : (prefixWord ++ tailWord_7515900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515900).length < 2 ^ (prefixWord ++ tailWord_7515900).sum := by decide
  have hdescent : baseEnd_7515900 < baseStart_7515900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7515911 : List Nat := [1, 1, 4, 4, 3, 1, 1, 1, 1, 4, 2]
def baseStart_7515911 : Nat := 118140960795 + 7515911 * 2 ^ 59
def prefixEnd_7515911 : Nat := 4983230072969 + 3 ^ 40 * 7515911 * 2
def baseEnd_7515911 : Nat := 3859274899414448697347461

theorem tailTrace_7515911 : CollatzResearch.WordTrace tailWord_7515911 prefixEnd_7515911 3859274899414448697347461 := by
  unfold tailWord_7515911
  simp only [CollatzResearch.WordTrace]
  refine ⟨274127794674145537250067587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182751863116097024833378391 274127794674145537250067587)
  ·
    refine ⟨411191692011218305875101381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274127794674145537250067587 411191692011218305875101381)
    ·
      refine ⟨77098442252103432351581509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 411191692011218305875101381 77098442252103432351581509)
      ·
        refine ⟨14455957922269393565921533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77098442252103432351581509 14455957922269393565921533)
        ·
          refine ⟨5420984220851022587220575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14455957922269393565921533 5420984220851022587220575)
          ·
            refine ⟨8131476331276533880830863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5420984220851022587220575 8131476331276533880830863)
            ·
              refine ⟨12197214496914800821246295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8131476331276533880830863 12197214496914800821246295)
              ·
                refine ⟨18295821745372201231869443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12197214496914800821246295 18295821745372201231869443)
                ·
                  refine ⟨27443732618058301847804165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18295821745372201231869443 27443732618058301847804165)
                  ·
                    refine ⟨5145699865885931596463281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27443732618058301847804165 5145699865885931596463281)
                    ·
                      refine ⟨3859274899414448697347461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5145699865885931596463281 3859274899414448697347461)
                      ·
                        rfl

theorem cell23_7515911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_7515911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7515911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7515911 prefixEnd_7515911 := by exact prefixLift 7515911
  have htrace : WordTrace (prefixWord ++ tailWord_7515911) baseStart_7515911 baseEnd_7515911 := by
    simpa [prefixWord, tailWord_7515911, baseEnd_7515911] using wordTrace_append hprefix tailTrace_7515911
  have hstable : (prefixWord ++ tailWord_7515911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7515911).length < 2 ^ (prefixWord ++ tailWord_7515911).sum := by decide
  have hdescent : baseEnd_7515911 < baseStart_7515911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7515911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516017 : List Nat := [1, 2, 2, 2, 1, 3, 2, 3, 3, 1, 3]
def baseStart_7516017 : Nat := 118140960795 + 7516017 * 2 ^ 59
def prefixEnd_7516017 : Nat := 4983230072969 + 3 ^ 40 * 7516017 * 2
def baseEnd_7516017 : Nat := 3859329328363825282621973

theorem tailTrace_7516017 : CollatzResearch.WordTrace tailWord_7516017 prefixEnd_7516017 3859329328363825282621973 := by
  unfold tailWord_7516017
  simp only [CollatzResearch.WordTrace]
  refine ⟨274131660811761517353426305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182754440541174344902284203 274131660811761517353426305)
  ·
    refine ⟨205598745608821138015069729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274131660811761517353426305 205598745608821138015069729)
    ·
      refine ⟨154199059206615853511302297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205598745608821138015069729 154199059206615853511302297)
      ·
        refine ⟨115649294404961890133476723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154199059206615853511302297 115649294404961890133476723)
        ·
          refine ⟨173473941607442835200215085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115649294404961890133476723 173473941607442835200215085)
          ·
            refine ⟨65052728102791063200080657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173473941607442835200215085 65052728102791063200080657)
            ·
              refine ⟨48789546077093297400060493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65052728102791063200080657 48789546077093297400060493)
              ·
                refine ⟨18296079778909986525022685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48789546077093297400060493 18296079778909986525022685)
                ·
                  refine ⟨6861029917091244946883507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18296079778909986525022685 6861029917091244946883507)
                  ·
                    refine ⟨10291544875636867420325261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6861029917091244946883507 10291544875636867420325261)
                    ·
                      refine ⟨3859329328363825282621973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10291544875636867420325261 3859329328363825282621973)
                      ·
                        rfl

theorem cell23_7516017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_7516017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516017 prefixEnd_7516017 := by exact prefixLift 7516017
  have htrace : WordTrace (prefixWord ++ tailWord_7516017) baseStart_7516017 baseEnd_7516017 := by
    simpa [prefixWord, tailWord_7516017, baseEnd_7516017] using wordTrace_append hprefix tailTrace_7516017
  have hstable : (prefixWord ++ tailWord_7516017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516017).length < 2 ^ (prefixWord ++ tailWord_7516017).sum := by decide
  have hdescent : baseEnd_7516017 < baseStart_7516017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516094 : List Nat := [4, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3]
def baseStart_7516094 : Nat := 118140960795 + 7516094 * 2 ^ 59
def prefixEnd_7516094 : Nat := 4983230072969 + 3 ^ 40 * 7516094 * 2
def baseEnd_7516094 : Nat := 3859368866374221481359119

theorem tailTrace_7516094 : CollatzResearch.WordTrace tailWord_7516094 prefixEnd_7516094 3859368866374221481359119 := by
  unfold tailWord_7516094
  simp only [CollatzResearch.WordTrace]
  refine ⟨34266808654060319937997417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182756312821655039669319557 34266808654060319937997417)
  ·
    refine ⟨25700106490545239953498063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34266808654060319937997417 25700106490545239953498063)
    ·
      refine ⟨38550159735817859930247095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25700106490545239953498063 38550159735817859930247095)
      ·
        refine ⟨57825239603726789895370643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38550159735817859930247095 57825239603726789895370643)
        ·
          refine ⟨86737859405590184843055965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57825239603726789895370643 86737859405590184843055965)
          ·
            refine ⟨32526697277096319316145987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86737859405590184843055965 32526697277096319316145987)
            ·
              refine ⟨48790045915644478974218981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32526697277096319316145987 48790045915644478974218981)
              ·
                refine ⟨9148133609183339807666059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48790045915644478974218981 9148133609183339807666059)
                ·
                  refine ⟨13722200413775009711499089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9148133609183339807666059 13722200413775009711499089)
                  ·
                    refine ⟨10291650310331257283624317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13722200413775009711499089 10291650310331257283624317)
                    ·
                      refine ⟨3859368866374221481359119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10291650310331257283624317 3859368866374221481359119)
                      ·
                        rfl

theorem cell23_7516094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_7516094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516094 prefixEnd_7516094 := by exact prefixLift 7516094
  have htrace : WordTrace (prefixWord ++ tailWord_7516094) baseStart_7516094 baseEnd_7516094 := by
    simpa [prefixWord, tailWord_7516094, baseEnd_7516094] using wordTrace_append hprefix tailTrace_7516094
  have hstable : (prefixWord ++ tailWord_7516094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516094).length < 2 ^ (prefixWord ++ tailWord_7516094).sum := by decide
  have hdescent : baseEnd_7516094 < baseStart_7516094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516107 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 6, 1, 3]
def baseStart_7516107 : Nat := 118140960795 + 7516107 * 2 ^ 59
def prefixEnd_7516107 : Nat := 4983230072969 + 3 ^ 40 * 7516107 * 2
def baseEnd_7516107 : Nat := 3859375541622729930496559

theorem tailTrace_7516107 : CollatzResearch.WordTrace tailWord_7516107 prefixEnd_7516107 3859375541622729930496559 := by
  unfold tailWord_7516107
  simp only [CollatzResearch.WordTrace]
  refine ⟨274134943381435462724202575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182756628920956975149468383 274134943381435462724202575)
  ·
    refine ⟨411202415072153194086303863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274134943381435462724202575 411202415072153194086303863)
    ·
      refine ⟨616803622608229791129455795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411202415072153194086303863 616803622608229791129455795)
      ·
        refine ⟨925205433912344686694183693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616803622608229791129455795 925205433912344686694183693)
        ·
          refine ⟨346952037717129257510318885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 925205433912344686694183693 346952037717129257510318885)
          ·
            refine ⟨65053507071961735783184791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 346952037717129257510318885 65053507071961735783184791)
            ·
              refine ⟨97580260607942603674777187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65053507071961735783184791 97580260607942603674777187)
              ·
                refine ⟨146370390911913905512165781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97580260607942603674777187 146370390911913905512165781)
                ·
                  refine ⟨6861112073995964320882771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146370390911913905512165781 6861112073995964320882771)
                  ·
                    refine ⟨10291668110993946481324157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6861112073995964320882771 10291668110993946481324157)
                    ·
                      refine ⟨3859375541622729930496559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10291668110993946481324157 3859375541622729930496559)
                      ·
                        rfl

theorem cell23_7516107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 1, 3].length) (baseStart_7516107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516107 prefixEnd_7516107 := by exact prefixLift 7516107
  have htrace : WordTrace (prefixWord ++ tailWord_7516107) baseStart_7516107 baseEnd_7516107 := by
    simpa [prefixWord, tailWord_7516107, baseEnd_7516107] using wordTrace_append hprefix tailTrace_7516107
  have hstable : (prefixWord ++ tailWord_7516107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516107).length < 2 ^ (prefixWord ++ tailWord_7516107).sum := by decide
  have hdescent : baseEnd_7516107 < baseStart_7516107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516108 : List Nat := [2, 2, 1, 4, 1, 2, 3, 3, 1, 2, 2]
def baseStart_7516108 : Nat := 118140960795 + 7516108 * 2 ^ 59
def prefixEnd_7516108 : Nat := 4983230072969 + 3 ^ 40 * 7516108 * 2
def baseEnd_7516108 : Nat := 3859376055103384426584055

theorem tailTrace_7516108 : CollatzResearch.WordTrace tailWord_7516108 prefixEnd_7516108 3859376055103384426584055 := by
  unfold tailWord_7516108
  simp only [CollatzResearch.WordTrace]
  refine ⟨137067489927215919947494489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182756653236287893263325985 137067489927215919947494489)
  ·
    refine ⟨102800617445411939960620867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137067489927215919947494489 102800617445411939960620867)
    ·
      refine ⟨154200926168117909940931301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102800617445411939960620867 154200926168117909940931301)
      ·
        refine ⟨28912673656522108113924619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154200926168117909940931301 28912673656522108113924619)
        ·
          refine ⟨43369010484783162170886929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28912673656522108113924619 43369010484783162170886929)
          ·
            refine ⟨32526757863587371628165197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43369010484783162170886929 32526757863587371628165197)
            ·
              refine ⟨12197534198845264360561949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32526757863587371628165197 12197534198845264360561949)
              ·
                refine ⟨4574075324566974135210731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12197534198845264360561949 4574075324566974135210731)
                ·
                  refine ⟨6861112986850461202816097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4574075324566974135210731 6861112986850461202816097)
                  ·
                    refine ⟨5145834740137845902112073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6861112986850461202816097 5145834740137845902112073)
                    ·
                      refine ⟨3859376055103384426584055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5145834740137845902112073 3859376055103384426584055)
                      ·
                        rfl

theorem cell23_7516108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_7516108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516108 prefixEnd_7516108 := by exact prefixLift 7516108
  have htrace : WordTrace (prefixWord ++ tailWord_7516108) baseStart_7516108 baseEnd_7516108 := by
    simpa [prefixWord, tailWord_7516108, baseEnd_7516108] using wordTrace_append hprefix tailTrace_7516108
  have hstable : (prefixWord ++ tailWord_7516108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516108).length < 2 ^ (prefixWord ++ tailWord_7516108).sum := by decide
  have hdescent : baseEnd_7516108 < baseStart_7516108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516114 : List Nat := [3, 2, 2, 3, 3, 1, 9]
def baseStart_7516114 : Nat := 118140960795 + 7516114 * 2 ^ 59
def prefixEnd_7516114 : Nat := 4983230072969 + 3 ^ 40 * 7516114 * 2
def baseEnd_7516114 : Nat := 47646655999843350655667

theorem tailTrace_7516114 : CollatzResearch.WordTrace tailWord_7516114 prefixEnd_7516114 47646655999843350655667 := by
  unfold tailWord_7516114
  simp only [CollatzResearch.WordTrace]
  refine ⟨68533799673102525729926849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182756799128273401946471597 68533799673102525729926849)
  ·
    refine ⟨51400349754826894297445137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68533799673102525729926849 51400349754826894297445137)
    ·
      refine ⟨38550262316120170723083853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51400349754826894297445137 38550262316120170723083853)
      ·
        refine ⟨14456348368545064021156445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38550262316120170723083853 14456348368545064021156445)
        ·
          refine ⟨5421130638204399007933667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14456348368545064021156445 5421130638204399007933667)
          ·
            refine ⟨8131695957306598511900501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5421130638204399007933667 8131695957306598511900501)
            ·
              refine ⟨47646655999843350655667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8131695957306598511900501 47646655999843350655667)
              ·
                rfl

theorem cell23_7516114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 9].length) (baseStart_7516114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516114 prefixEnd_7516114 := by exact prefixLift 7516114
  have htrace : WordTrace (prefixWord ++ tailWord_7516114) baseStart_7516114 baseEnd_7516114 := by
    simpa [prefixWord, tailWord_7516114, baseEnd_7516114] using wordTrace_append hprefix tailTrace_7516114
  have hstable : (prefixWord ++ tailWord_7516114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516114).length < 2 ^ (prefixWord ++ tailWord_7516114).sum := by decide
  have hdescent : baseEnd_7516114 < baseStart_7516114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516120 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 5]
def baseStart_7516120 : Nat := 118140960795 + 7516120 * 2 ^ 59
def prefixEnd_7516120 : Nat := 4983230072969 + 3 ^ 40 * 7516120 * 2
def baseEnd_7516120 : Nat := 3859382216871238379633999

theorem tailTrace_7516120 : CollatzResearch.WordTrace tailWord_7516120 prefixEnd_7516120 3859382216871238379633999 := by
  unfold tailWord_7516120
  simp only [CollatzResearch.WordTrace]
  refine ⟨137067708765194182972212907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182756945020258910629617209 137067708765194182972212907)
  ·
    refine ⟨205601563147791274458319361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137067708765194182972212907 205601563147791274458319361)
    ·
      refine ⟨154201172360843455843739521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205601563147791274458319361 154201172360843455843739521)
      ·
        refine ⟨115650879270632591882804641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154201172360843455843739521 115650879270632591882804641)
        ·
          refine ⟨86738159452974443912103481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115650879270632591882804641 86738159452974443912103481)
          ·
            refine ⟨65053619589730832934077611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86738159452974443912103481 65053619589730832934077611)
            ·
              refine ⟨97580429384596249401116417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65053619589730832934077611 97580429384596249401116417)
              ·
                refine ⟨73185322038447187050837313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97580429384596249401116417 73185322038447187050837313)
                ·
                  refine ⟨54888991528835390288127985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73185322038447187050837313 54888991528835390288127985)
                  ·
                    refine ⟨41166743646626542716095989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54888991528835390288127985 41166743646626542716095989)
                    ·
                      refine ⟨3859382216871238379633999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41166743646626542716095989 3859382216871238379633999)
                      ·
                        rfl

theorem cell23_7516120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_7516120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516120 prefixEnd_7516120 := by exact prefixLift 7516120
  have htrace : WordTrace (prefixWord ++ tailWord_7516120) baseStart_7516120 baseEnd_7516120 := by
    simpa [prefixWord, tailWord_7516120, baseEnd_7516120] using wordTrace_append hprefix tailTrace_7516120
  have hstable : (prefixWord ++ tailWord_7516120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516120).length < 2 ^ (prefixWord ++ tailWord_7516120).sum := by decide
  have hdescent : baseEnd_7516120 < baseStart_7516120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516125 : List Nat := [1, 4, 3, 1, 4, 1, 1, 1, 3, 2, 2]
def baseStart_7516125 : Nat := 118140960795 + 7516125 * 2 ^ 59
def prefixEnd_7516125 : Nat := 4983230072969 + 3 ^ 40 * 7516125 * 2
def baseEnd_7516125 : Nat := 3859384784274510860071477

theorem tailTrace_7516125 : CollatzResearch.WordTrace tailWord_7516125 prefixEnd_7516125 3859384784274510860071477 := by
  unfold tailWord_7516125
  simp only [CollatzResearch.WordTrace]
  refine ⟨274135599895370251798357829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182757066596913501198905219 274135599895370251798357829)
  ·
    refine ⟨51400424980381922212192093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274135599895370251798357829 51400424980381922212192093)
    ·
      refine ⟨19275159367643220829572035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51400424980381922212192093 19275159367643220829572035)
      ·
        refine ⟨28912739051464831244358053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19275159367643220829572035 28912739051464831244358053)
        ·
          refine ⟨5421138572149655858317135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28912739051464831244358053 5421138572149655858317135)
          ·
            refine ⟨8131707858224483787475703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5421138572149655858317135 8131707858224483787475703)
            ·
              refine ⟨12197561787336725681213555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8131707858224483787475703 12197561787336725681213555)
              ·
                refine ⟨18296342681005088521820333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12197561787336725681213555 18296342681005088521820333)
                ·
                  refine ⟨6861128505376908195682625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18296342681005088521820333 6861128505376908195682625)
                  ·
                    refine ⟨5145846379032681146761969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6861128505376908195682625 5145846379032681146761969)
                    ·
                      refine ⟨3859384784274510860071477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5145846379032681146761969 3859384784274510860071477)
                      ·
                        rfl

theorem cell23_7516125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_7516125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516125 prefixEnd_7516125 := by exact prefixLift 7516125
  have htrace : WordTrace (prefixWord ++ tailWord_7516125) baseStart_7516125 baseEnd_7516125 := by
    simpa [prefixWord, tailWord_7516125, baseEnd_7516125] using wordTrace_append hprefix tailTrace_7516125
  have hstable : (prefixWord ++ tailWord_7516125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516125).length < 2 ^ (prefixWord ++ tailWord_7516125).sum := by decide
  have hdescent : baseEnd_7516125 < baseStart_7516125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516140 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 2, 6]
def baseStart_7516140 : Nat := 118140960795 + 7516140 * 2 ^ 59
def prefixEnd_7516140 : Nat := 4983230072969 + 3 ^ 40 * 7516140 * 2
def baseEnd_7516140 : Nat := 1286464162161442767127969

theorem tailTrace_7516140 : CollatzResearch.WordTrace tailWord_7516140 prefixEnd_7516140 1286464162161442767127969 := by
  unfold tailWord_7516140
  simp only [CollatzResearch.WordTrace]
  refine ⟨137068073495157954680076937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182757431326877272906769249 137068073495157954680076937)
  ·
    refine ⟨102801055121368466010057703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137068073495157954680076937 102801055121368466010057703)
    ·
      refine ⟨154201582682052699015086555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102801055121368466010057703 154201582682052699015086555)
      ·
        refine ⟨231302374023079048522629833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154201582682052699015086555 231302374023079048522629833)
        ·
          refine ⟨173476780517309286391972375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231302374023079048522629833 173476780517309286391972375)
          ·
            refine ⟨260215170775963929587958563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173476780517309286391972375 260215170775963929587958563)
            ·
              refine ⟨390322756163945894381937845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260215170775963929587958563 390322756163945894381937845)
              ·
                refine ⟨36592758390369927598306673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 390322756163945894381937845 36592758390369927598306673)
                ·
                  refine ⟨27444568792777445698730005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36592758390369927598306673 27444568792777445698730005)
                  ·
                    refine ⟨1286464162161442767127969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27444568792777445698730005 1286464162161442767127969)
                    ·
                      rfl

theorem cell23_7516140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_7516140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516140 prefixEnd_7516140 := by exact prefixLift 7516140
  have htrace : WordTrace (prefixWord ++ tailWord_7516140) baseStart_7516140 baseEnd_7516140 := by
    simpa [prefixWord, tailWord_7516140, baseEnd_7516140] using wordTrace_append hprefix tailTrace_7516140
  have hstable : (prefixWord ++ tailWord_7516140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516140).length < 2 ^ (prefixWord ++ tailWord_7516140).sum := by decide
  have hdescent : baseEnd_7516140 < baseStart_7516140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516147 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 5, 4, 2]
def baseStart_7516147 : Nat := 118140960795 + 7516147 * 2 ^ 59
def prefixEnd_7516147 : Nat := 4983230072969 + 3 ^ 40 * 7516147 * 2
def baseEnd_7516147 : Nat := 3859396080848909773996375

theorem tailTrace_7516147 : CollatzResearch.WordTrace tailWord_7516147 prefixEnd_7516147 3859396080848909773996375 := by
  unfold tailWord_7516147
  simp only [CollatzResearch.WordTrace]
  refine ⟨274136402301290549555658695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182757601534193699703772463 274136402301290549555658695)
  ·
    refine ⟨411204603451935824333488043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274136402301290549555658695 411204603451935824333488043)
    ·
      refine ⟨616806905177903736500232065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411204603451935824333488043 616806905177903736500232065)
      ·
        refine ⟨462605178883427802375174049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616806905177903736500232065 462605178883427802375174049)
        ·
          refine ⟨346953884162570851781380537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462605178883427802375174049 346953884162570851781380537)
          ·
            refine ⟨260215413121928138836035403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346953884162570851781380537 260215413121928138836035403)
            ·
              refine ⟨390323119682892208254053105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260215413121928138836035403 390323119682892208254053105)
              ·
                refine ⟨292742339762169156190539829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390323119682892208254053105 292742339762169156190539829)
                ·
                  refine ⟨27444594352703358392863109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 292742339762169156190539829 27444594352703358392863109)
                  ·
                    refine ⟨5145861441131879698661833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27444594352703358392863109 5145861441131879698661833)
                    ·
                      refine ⟨3859396080848909773996375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5145861441131879698661833 3859396080848909773996375)
                      ·
                        rfl

theorem cell23_7516147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 4, 2].length) (baseStart_7516147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516147 prefixEnd_7516147 := by exact prefixLift 7516147
  have htrace : WordTrace (prefixWord ++ tailWord_7516147) baseStart_7516147 baseEnd_7516147 := by
    simpa [prefixWord, tailWord_7516147, baseEnd_7516147] using wordTrace_append hprefix tailTrace_7516147
  have hstable : (prefixWord ++ tailWord_7516147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516147).length < 2 ^ (prefixWord ++ tailWord_7516147).sum := by decide
  have hdescent : baseEnd_7516147 < baseStart_7516147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516160 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 4]
def baseStart_7516160 : Nat := 118140960795 + 7516160 * 2 ^ 59
def prefixEnd_7516160 : Nat := 4983230072969 + 3 ^ 40 * 7516160 * 2
def baseEnd_7516160 : Nat := 3859402756097418223133815

theorem tailTrace_7516160 : CollatzResearch.WordTrace tailWord_7516160 prefixEnd_7516160 3859402756097418223133815 := by
  unfold tailWord_7516160
  simp only [CollatzResearch.WordTrace]
  refine ⟨137068438225121726387940967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182757917633495635183921289 137068438225121726387940967)
  ·
    refine ⟨205602657337682589581911451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137068438225121726387940967 205602657337682589581911451)
    ·
      refine ⟨308403986006523884372867177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205602657337682589581911451 308403986006523884372867177)
      ·
        refine ⟨231302989504892913279650383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308403986006523884372867177 231302989504892913279650383)
        ·
          refine ⟨346954484257339369919475575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231302989504892913279650383 346954484257339369919475575)
          ·
            refine ⟨520431726386009054879213363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346954484257339369919475575 520431726386009054879213363)
            ·
              refine ⟨780647589579013582318820045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520431726386009054879213363 780647589579013582318820045)
              ·
                refine ⟨292742846092130093369557517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 780647589579013582318820045 292742846092130093369557517)
                ·
                  refine ⟨109778567284548785013584069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 292742846092130093369557517 109778567284548785013584069)
                  ·
                    refine ⟨20583481365852897190047013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109778567284548785013584069 20583481365852897190047013)
                    ·
                      refine ⟨3859402756097418223133815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20583481365852897190047013 3859402756097418223133815)
                      ·
                        rfl

theorem cell23_7516160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_7516160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516160 prefixEnd_7516160 := by exact prefixLift 7516160
  have htrace : WordTrace (prefixWord ++ tailWord_7516160) baseStart_7516160 baseEnd_7516160 := by
    simpa [prefixWord, tailWord_7516160, baseEnd_7516160] using wordTrace_append hprefix tailTrace_7516160
  have hstable : (prefixWord ++ tailWord_7516160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516160).length < 2 ^ (prefixWord ++ tailWord_7516160).sum := by decide
  have hdescent : baseEnd_7516160 < baseStart_7516160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516167 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 5]
def baseStart_7516167 : Nat := 118140960795 + 7516167 * 2 ^ 59
def prefixEnd_7516167 : Nat := 4983230072969 + 3 ^ 40 * 7516167 * 2
def baseEnd_7516167 : Nat := 3859406350461999695746283

theorem tailTrace_7516167 : CollatzResearch.WordTrace tailWord_7516167 prefixEnd_7516167 3859406350461999695746283 := by
  unfold tailWord_7516167
  simp only [CollatzResearch.WordTrace]
  refine ⟨274137131761218092971386755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182758087840812061980924503 274137131761218092971386755)
  ·
    refine ⟨411205697641827139457080133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274137131761218092971386755 411205697641827139457080133)
    ·
      refine ⟨77101068307842588648202525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 411205697641827139457080133 77101068307842588648202525)
      ·
        refine ⟨28912900615440970743075947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77101068307842588648202525 28912900615440970743075947)
        ·
          refine ⟨43369350923161456114613921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28912900615440970743075947 43369350923161456114613921)
          ·
            refine ⟨32527013192371092085960441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43369350923161456114613921 32527013192371092085960441)
            ·
              refine ⟨24395259894278319064470331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32527013192371092085960441 24395259894278319064470331)
              ·
                refine ⟨36592889841417478596705497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24395259894278319064470331 36592889841417478596705497)
                ·
                  refine ⟨27444667381063108947529123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36592889841417478596705497 27444667381063108947529123)
                  ·
                    refine ⟨41167001071594663421293685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27444667381063108947529123 41167001071594663421293685)
                    ·
                      refine ⟨3859406350461999695746283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41167001071594663421293685 3859406350461999695746283)
                      ·
                        rfl

theorem cell23_7516167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_7516167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516167 prefixEnd_7516167 := by exact prefixLift 7516167
  have htrace : WordTrace (prefixWord ++ tailWord_7516167) baseStart_7516167 baseEnd_7516167 := by
    simpa [prefixWord, tailWord_7516167, baseEnd_7516167] using wordTrace_append hprefix tailTrace_7516167
  have hstable : (prefixWord ++ tailWord_7516167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516167).length < 2 ^ (prefixWord ++ tailWord_7516167).sum := by decide
  have hdescent : baseEnd_7516167 < baseStart_7516167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516197 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 1, 5, 3]
def baseStart_7516197 : Nat := 118140960795 + 7516197 * 2 ^ 59
def prefixEnd_7516197 : Nat := 4983230072969 + 3 ^ 40 * 7516197 * 2
def baseEnd_7516197 : Nat := 3859421754881634578371145

theorem tailTrace_7516197 : CollatzResearch.WordTrace tailWord_7516197 prefixEnd_7516197 3859421754881634578371145 := by
  unfold tailWord_7516197
  simp only [CollatzResearch.WordTrace]
  refine ⟨274138225951109408094978845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182758817300739605396652563 274138225951109408094978845)
  ·
    refine ⟨102801834731666028035617067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274138225951109408094978845 102801834731666028035617067)
    ·
      refine ⟨154202752097499042053425601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102801834731666028035617067 154202752097499042053425601)
      ·
        refine ⟨115652064073124281540069201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154202752097499042053425601 115652064073124281540069201)
        ·
          refine ⟨86739048054843211155051901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115652064073124281540069201 86739048054843211155051901)
          ·
            refine ⟨32527143020566204183144463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86739048054843211155051901 32527143020566204183144463)
            ·
              refine ⟨48790714530849306274716695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32527143020566204183144463 48790714530849306274716695)
              ·
                refine ⟨73186071796273959412075043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48790714530849306274716695 73186071796273959412075043)
                ·
                  refine ⟨109779107694410939118112565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73186071796273959412075043 109779107694410939118112565)
                  ·
                    refine ⟨10291791346351025542323053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109779107694410939118112565 10291791346351025542323053)
                    ·
                      refine ⟨3859421754881634578371145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10291791346351025542323053 3859421754881634578371145)
                      ·
                        rfl

theorem cell23_7516197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_7516197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516197 prefixEnd_7516197 := by exact prefixLift 7516197
  have htrace : WordTrace (prefixWord ++ tailWord_7516197) baseStart_7516197 baseEnd_7516197 := by
    simpa [prefixWord, tailWord_7516197, baseEnd_7516197] using wordTrace_append hprefix tailTrace_7516197
  have hstable : (prefixWord ++ tailWord_7516197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516197).length < 2 ^ (prefixWord ++ tailWord_7516197).sum := by decide
  have hdescent : baseEnd_7516197 < baseStart_7516197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516214 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_7516214 : Nat := 118140960795 + 7516214 * 2 ^ 59
def prefixEnd_7516214 : Nat := 4983230072969 + 3 ^ 40 * 7516214 * 2
def baseEnd_7516214 : Nat := 3859430484052761011858567

theorem tailTrace_7516214 : CollatzResearch.WordTrace tailWord_7516214 prefixEnd_7516214 3859430484052761011858567 := by
  unfold tailWord_7516214
  simp only [CollatzResearch.WordTrace]
  refine ⟨17133677874502988749896731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182759230661365213332231797 17133677874502988749896731)
  ·
    refine ⟨25700516811754483124845097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17133677874502988749896731 25700516811754483124845097)
    ·
      refine ⟨19275387608815862343633823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25700516811754483124845097 19275387608815862343633823)
      ·
        refine ⟨28913081413223793515450735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19275387608815862343633823 28913081413223793515450735)
        ·
          refine ⟨43369622119835690273176103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28913081413223793515450735 43369622119835690273176103)
          ·
            refine ⟨65054433179753535409764155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43369622119835690273176103 65054433179753535409764155)
            ·
              refine ⟨97581649769630303114646233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65054433179753535409764155 97581649769630303114646233)
              ·
                refine ⟨73186237327222727335984675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97581649769630303114646233 73186237327222727335984675)
                ·
                  refine ⟨109779355990834091003977013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73186237327222727335984675 109779355990834091003977013)
                  ·
                    refine ⟨10291814624140696031622845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109779355990834091003977013 10291814624140696031622845)
                    ·
                      refine ⟨3859430484052761011858567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10291814624140696031622845 3859430484052761011858567)
                      ·
                        rfl

theorem cell23_7516214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_7516214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516214 prefixEnd_7516214 := by exact prefixLift 7516214
  have htrace : WordTrace (prefixWord ++ tailWord_7516214) baseStart_7516214 baseEnd_7516214 := by
    simpa [prefixWord, tailWord_7516214, baseEnd_7516214] using wordTrace_append hprefix tailTrace_7516214
  have hstable : (prefixWord ++ tailWord_7516214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516214).length < 2 ^ (prefixWord ++ tailWord_7516214).sum := by decide
  have hdescent : baseEnd_7516214 < baseStart_7516214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516274 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 1, 4, 3]
def baseStart_7516274 : Nat := 118140960795 + 7516274 * 2 ^ 59
def prefixEnd_7516274 : Nat := 4983230072969 + 3 ^ 40 * 7516274 * 2
def baseEnd_7516274 : Nat := 3859461292892030777108291

theorem tailTrace_7516274 : CollatzResearch.WordTrace tailWord_7516274 prefixEnd_7516274 3859461292892030777108291 := by
  unfold tailWord_7516274
  simp only [CollatzResearch.WordTrace]
  refine ⟨68535258592957612561382969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182760689581220300163687917 68535258592957612561382969)
  ·
    refine ⟨51401443944718209421037227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68535258592957612561382969 51401443944718209421037227)
    ·
      refine ⟨77102165917077314131555841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51401443944718209421037227 77102165917077314131555841)
      ·
        refine ⟨57826624437807985598666881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77102165917077314131555841 57826624437807985598666881)
        ·
          refine ⟨43369968328355989199000161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57826624437807985598666881 43369968328355989199000161)
          ·
            refine ⟨32527476246266991899250121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43369968328355989199000161 32527476246266991899250121)
            ·
              refine ⟨24395607184700243924437591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32527476246266991899250121 24395607184700243924437591)
              ·
                refine ⟨36593410777050365886656387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24395607184700243924437591 36593410777050365886656387)
                ·
                  refine ⟨54890116165575548829984581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36593410777050365886656387 54890116165575548829984581)
                  ·
                    refine ⟨10291896781045415405622109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54890116165575548829984581 10291896781045415405622109)
                    ·
                      refine ⟨3859461292892030777108291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10291896781045415405622109 3859461292892030777108291)
                      ·
                        rfl

theorem cell23_7516274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_7516274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516274 prefixEnd_7516274 := by exact prefixLift 7516274
  have htrace : WordTrace (prefixWord ++ tailWord_7516274) baseStart_7516274 baseEnd_7516274 := by
    simpa [prefixWord, tailWord_7516274, baseEnd_7516274] using wordTrace_append hprefix tailTrace_7516274
  have hstable : (prefixWord ++ tailWord_7516274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516274).length < 2 ^ (prefixWord ++ tailWord_7516274).sum := by decide
  have hdescent : baseEnd_7516274 < baseStart_7516274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516307 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 3, 5]
def baseStart_7516307 : Nat := 118140960795 + 7516307 * 2 ^ 59
def prefixEnd_7516307 : Nat := 4983230072969 + 3 ^ 40 * 7516307 * 2
def baseEnd_7516307 : Nat := 1286492745917876382665213

theorem tailTrace_7516307 : CollatzResearch.WordTrace tailWord_7516307 prefixEnd_7516307 1286492745917876382665213 := by
  unfold tailWord_7516307
  simp only [CollatzResearch.WordTrace]
  refine ⟨274142237980710896881483175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182761491987140597920988783 274142237980710896881483175)
  ·
    refine ⟨411213356971066345322224763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274142237980710896881483175 411213356971066345322224763)
    ·
      refine ⟨616820035456599517983337145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411213356971066345322224763 616820035456599517983337145)
      ·
        refine ⟨462615026592449638487502859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616820035456599517983337145 462615026592449638487502859)
        ·
          refine ⟨693922539888674457731254289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462615026592449638487502859 693922539888674457731254289)
          ·
            refine ⟨520441904916505843298440717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 693922539888674457731254289 520441904916505843298440717)
            ·
              refine ⟨195165714343689691236915269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 520441904916505843298440717 195165714343689691236915269)
              ·
                refine ⟨36593571439441817106921613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195165714343689691236915269 36593571439441817106921613)
                ·
                  refine ⟨13722589289790681415095605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36593571439441817106921613 13722589289790681415095605)
                  ·
                    refine ⟨1286492745917876382665213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13722589289790681415095605 1286492745917876382665213)
                    ·
                      rfl

theorem cell23_7516307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 5].length) (baseStart_7516307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516307 prefixEnd_7516307 := by exact prefixLift 7516307
  have htrace : WordTrace (prefixWord ++ tailWord_7516307) baseStart_7516307 baseEnd_7516307 := by
    simpa [prefixWord, tailWord_7516307, baseEnd_7516307] using wordTrace_append hprefix tailTrace_7516307
  have hstable : (prefixWord ++ tailWord_7516307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516307).length < 2 ^ (prefixWord ++ tailWord_7516307).sum := by decide
  have hdescent : baseEnd_7516307 < baseStart_7516307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516338 : List Nat := [3, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3]
def baseStart_7516338 : Nat := 118140960795 + 7516338 * 2 ^ 59
def prefixEnd_7516338 : Nat := 4983230072969 + 3 ^ 40 * 7516338 * 2
def baseEnd_7516338 : Nat := 3859494155653918526707997

theorem tailTrace_7516338 : CollatzResearch.WordTrace tailWord_7516338 prefixEnd_7516338 3859494155653918526707997 := by
  unfold tailWord_7516338
  simp only [CollatzResearch.WordTrace]
  refine ⟨68535842160899647293965417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182762245762399059450574445 68535842160899647293965417)
  ·
    refine ⟨51401881620674735470474063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68535842160899647293965417 51401881620674735470474063)
    ·
      refine ⟨77102822431012103205711095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51401881620674735470474063 77102822431012103205711095)
      ·
        refine ⟨115654233646518154808566643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77102822431012103205711095 115654233646518154808566643)
        ·
          refine ⟨173481350469777232212849965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115654233646518154808566643 173481350469777232212849965)
          ·
            refine ⟨65055506426166462079818737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173481350469777232212849965 65055506426166462079818737)
            ·
              refine ⟨48791629819624846559864053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65055506426166462079818737 48791629819624846559864053)
              ·
                refine ⟨4574215295589829364987255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48791629819624846559864053 4574215295589829364987255)
                ·
                  refine ⟨6861322943384744047480883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4574215295589829364987255 6861322943384744047480883)
                  ·
                    refine ⟨10291984415077116071221325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6861322943384744047480883 10291984415077116071221325)
                    ·
                      refine ⟨3859494155653918526707997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10291984415077116071221325 3859494155653918526707997)
                      ·
                        rfl

theorem cell23_7516338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3].length) (baseStart_7516338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516338 prefixEnd_7516338 := by exact prefixLift 7516338
  have htrace : WordTrace (prefixWord ++ tailWord_7516338) baseStart_7516338 baseEnd_7516338 := by
    simpa [prefixWord, tailWord_7516338, baseEnd_7516338] using wordTrace_append hprefix tailTrace_7516338
  have hstable : (prefixWord ++ tailWord_7516338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516338).length < 2 ^ (prefixWord ++ tailWord_7516338).sum := by decide
  have hdescent : baseEnd_7516338 < baseStart_7516338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516357 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 3, 1, 6]
def baseStart_7516357 : Nat := 118140960795 + 7516357 * 2 ^ 59
def prefixEnd_7516357 : Nat := 4983230072969 + 3 ^ 40 * 7516357 * 2
def baseEnd_7516357 : Nat := 3859503911786353952370409

theorem tailTrace_7516357 : CollatzResearch.WordTrace tailWord_7516357 prefixEnd_7516357 3859503911786353952370409 := by
  unfold tailWord_7516357
  simp only [CollatzResearch.WordTrace]
  refine ⟨274144061630529755420803325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182762707753686503613868883 274144061630529755420803325)
  ·
    refine ⟨102804023111448658282801247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274144061630529755420803325 102804023111448658282801247)
    ·
      refine ⟨154206034667172987424201871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102804023111448658282801247 154206034667172987424201871)
      ·
        refine ⟨231309052000759481136302807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154206034667172987424201871 231309052000759481136302807)
        ·
          refine ⟨346963578001139221704454211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231309052000759481136302807 346963578001139221704454211)
          ·
            refine ⟨520445367001708832556681317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346963578001139221704454211 520445367001708832556681317)
            ·
              refine ⟨97583506312820406104377747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 520445367001708832556681317 97583506312820406104377747)
              ·
                refine ⟨146375259469230609156566621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97583506312820406104377747 146375259469230609156566621)
                ·
                  refine ⟨54890722300961478433712483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146375259469230609156566621 54890722300961478433712483)
                  ·
                    refine ⟨82336083451442217650568725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54890722300961478433712483 82336083451442217650568725)
                    ·
                      refine ⟨3859503911786353952370409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82336083451442217650568725 3859503911786353952370409)
                      ·
                        rfl

theorem cell23_7516357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_7516357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516357 prefixEnd_7516357 := by exact prefixLift 7516357
  have htrace : WordTrace (prefixWord ++ tailWord_7516357) baseStart_7516357 baseEnd_7516357 := by
    simpa [prefixWord, tailWord_7516357, baseEnd_7516357] using wordTrace_append hprefix tailTrace_7516357
  have hstable : (prefixWord ++ tailWord_7516357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516357).length < 2 ^ (prefixWord ++ tailWord_7516357).sum := by decide
  have hdescent : baseEnd_7516357 < baseStart_7516357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516384 : List Nat := [2, 1, 1, 3, 1, 3, 5, 7]
def baseStart_7516384 : Nat := 118140960795 + 7516384 * 2 ^ 59
def prefixEnd_7516384 : Nat := 4983230072969 + 3 ^ 40 * 7516384 * 2
def baseEnd_7516384 : Nat := 142945102806075012841955

theorem tailTrace_7516384 : CollatzResearch.WordTrace tailWord_7516384 prefixEnd_7516384 142945102806075012841955 := by
  unfold tailWord_7516384
  simp only [CollatzResearch.WordTrace]
  refine ⟨137072523200715969516018103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182763364267621292688024137 137072523200715969516018103)
  ·
    refine ⟨205608784801073954274027155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137072523200715969516018103 205608784801073954274027155)
    ·
      refine ⟨308413177201610931411040733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205608784801073954274027155 308413177201610931411040733)
      ·
        refine ⟨115654941450604099279140275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308413177201610931411040733 115654941450604099279140275)
        ·
          refine ⟨173482412175906148918710413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115654941450604099279140275 173482412175906148918710413)
          ·
            refine ⟨65055904565964805844516405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173482412175906148918710413 65055904565964805844516405)
            ·
              refine ⟨6098991053059200547923413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65055904565964805844516405 6098991053059200547923413)
              ·
                refine ⟨142945102806075012841955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6098991053059200547923413 142945102806075012841955)
                ·
                  rfl

theorem cell23_7516384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 7].length) (baseStart_7516384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516384 prefixEnd_7516384 := by exact prefixLift 7516384
  have htrace : WordTrace (prefixWord ++ tailWord_7516384) baseStart_7516384 baseEnd_7516384 := by
    simpa [prefixWord, tailWord_7516384, baseEnd_7516384] using wordTrace_append hprefix tailTrace_7516384
  have hstable : (prefixWord ++ tailWord_7516384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516384).length < 2 ^ (prefixWord ++ tailWord_7516384).sum := by decide
  have hdescent : baseEnd_7516384 < baseStart_7516384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516391 : List Nat := [1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_7516391 : Nat := 118140960795 + 7516391 * 2 ^ 59
def prefixEnd_7516391 : Nat := 4983230072969 + 3 ^ 40 * 7516391 * 2
def baseEnd_7516391 : Nat := 3859521370128606819345253

theorem tailTrace_7516391 : CollatzResearch.WordTrace tailWord_7516391 prefixEnd_7516391 3859521370128606819345253 := by
  unfold tailWord_7516391
  simp only [CollatzResearch.WordTrace]
  refine ⟨274145301712406579227541027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182763534474937719485027351 274145301712406579227541027)
  ·
    refine ⟨411217952568609868841311541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274145301712406579227541027 411217952568609868841311541)
    ·
      refine ⟨38551683053307175203872957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 411217952568609868841311541 38551683053307175203872957)
      ·
        refine ⟨14456881144990190701452359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38551683053307175203872957 14456881144990190701452359)
        ·
          refine ⟨21685321717485286052178539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14456881144990190701452359 21685321717485286052178539)
          ·
            refine ⟨32527982576227929078267809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21685321717485286052178539 32527982576227929078267809)
            ·
              refine ⟨24395986932170946808700857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32527982576227929078267809 24395986932170946808700857)
              ·
                refine ⟨18296990199128210106525643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24395986932170946808700857 18296990199128210106525643)
                ·
                  refine ⟨27445485298692315159788465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18296990199128210106525643 27445485298692315159788465)
                  ·
                    refine ⟨20584113974019236369841349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27445485298692315159788465 20584113974019236369841349)
                    ·
                      refine ⟨3859521370128606819345253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20584113974019236369841349 3859521370128606819345253)
                      ·
                        rfl

theorem cell23_7516391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_7516391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516391 prefixEnd_7516391 := by exact prefixLift 7516391
  have htrace : WordTrace (prefixWord ++ tailWord_7516391) baseStart_7516391 baseEnd_7516391 := by
    simpa [prefixWord, tailWord_7516391, baseEnd_7516391] using wordTrace_append hprefix tailTrace_7516391
  have hstable : (prefixWord ++ tailWord_7516391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516391).length < 2 ^ (prefixWord ++ tailWord_7516391).sum := by decide
  have hdescent : baseEnd_7516391 < baseStart_7516391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516395 : List Nat := [1, 1, 1, 1, 2, 5, 4, 3, 1, 2, 2]
def baseStart_7516395 : Nat := 118140960795 + 7516395 * 2 ^ 59
def prefixEnd_7516395 : Nat := 4983230072969 + 3 ^ 40 * 7516395 * 2
def baseEnd_7516395 : Nat := 3859523424051224803695235

theorem tailTrace_7516395 : CollatzResearch.WordTrace tailWord_7516395 prefixEnd_7516395 3859523424051224803695235 := by
  unfold tailWord_7516395
  simp only [CollatzResearch.WordTrace]
  refine ⟨274145447604392087910686639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182763631736261391940457759 274145447604392087910686639)
  ·
    refine ⟨411218171406588131866029959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274145447604392087910686639 411218171406588131866029959)
    ·
      refine ⟨616827257109882197799044939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411218171406588131866029959 616827257109882197799044939)
      ·
        refine ⟨925240885664823296698567409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616827257109882197799044939 925240885664823296698567409)
        ·
          refine ⟨693930664248617472523925557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 925240885664823296698567409 693930664248617472523925557)
          ·
            refine ⟨65055999773307888049118021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 693930664248617472523925557 65055999773307888049118021)
            ·
              refine ⟨12197999957495229009209629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65055999773307888049118021 12197999957495229009209629)
              ·
                refine ⟨4574249984060710878453611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12197999957495229009209629 4574249984060710878453611)
                ·
                  refine ⟨6861374976091066317680417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4574249984060710878453611 6861374976091066317680417)
                  ·
                    refine ⟨5146031232068299738260313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6861374976091066317680417 5146031232068299738260313)
                    ·
                      refine ⟨3859523424051224803695235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5146031232068299738260313 3859523424051224803695235)
                      ·
                        rfl

theorem cell23_7516395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 3, 1, 2, 2].length) (baseStart_7516395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516395 prefixEnd_7516395 := by exact prefixLift 7516395
  have htrace : WordTrace (prefixWord ++ tailWord_7516395) baseStart_7516395 baseEnd_7516395 := by
    simpa [prefixWord, tailWord_7516395, baseEnd_7516395] using wordTrace_append hprefix tailTrace_7516395
  have hstable : (prefixWord ++ tailWord_7516395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516395).length < 2 ^ (prefixWord ++ tailWord_7516395).sum := by decide
  have hdescent : baseEnd_7516395 < baseStart_7516395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516407 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 7]
def baseStart_7516407 : Nat := 118140960795 + 7516407 * 2 ^ 59
def prefixEnd_7516407 : Nat := 4983230072969 + 3 ^ 40 * 7516407 * 2
def baseEnd_7516407 : Nat := 3859529585819078756745179

theorem tailTrace_7516407 : CollatzResearch.WordTrace tailWord_7516407 prefixEnd_7516407 3859529585819078756745179 := by
  unfold tailWord_7516407
  simp only [CollatzResearch.WordTrace]
  refine ⟨274145885280348613960123475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182763923520232409306748983 274145885280348613960123475)
  ·
    refine ⟨411218827920522920940185213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274145885280348613960123475 411218827920522920940185213)
    ·
      refine ⟨154207060470196095352569455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411218827920522920940185213 154207060470196095352569455)
      ·
        refine ⟨231310590705294143028854183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154207060470196095352569455 231310590705294143028854183)
        ·
          refine ⟨346965886057941214543281275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231310590705294143028854183 346965886057941214543281275)
          ·
            refine ⟨520448829086911821814921913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346965886057941214543281275 520448829086911821814921913)
            ·
              refine ⟨390336621815183866361191435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520448829086911821814921913 390336621815183866361191435)
              ·
                refine ⟨585504932722775799541787153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390336621815183866361191435 585504932722775799541787153)
                ·
                  refine ⟨439128699542081849656340365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585504932722775799541787153 439128699542081849656340365)
                  ·
                    refine ⟨164673262328280693621127637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 439128699542081849656340365 164673262328280693621127637)
                    ·
                      refine ⟨3859529585819078756745179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 164673262328280693621127637 3859529585819078756745179)
                      ·
                        rfl

theorem cell23_7516407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_7516407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516407 prefixEnd_7516407 := by exact prefixLift 7516407
  have htrace : WordTrace (prefixWord ++ tailWord_7516407) baseStart_7516407 baseEnd_7516407 := by
    simpa [prefixWord, tailWord_7516407, baseEnd_7516407] using wordTrace_append hprefix tailTrace_7516407
  have hstable : (prefixWord ++ tailWord_7516407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516407).length < 2 ^ (prefixWord ++ tailWord_7516407).sum := by decide
  have hdescent : baseEnd_7516407 < baseStart_7516407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516421 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 3, 3, 2]
def baseStart_7516421 : Nat := 118140960795 + 7516421 * 2 ^ 59
def prefixEnd_7516421 : Nat := 4983230072969 + 3 ^ 40 * 7516421 * 2
def baseEnd_7516421 : Nat := 3859536774548241701970115

theorem tailTrace_7516421 : CollatzResearch.WordTrace tailWord_7516421 prefixEnd_7516421 3859536774548241701970115 := by
  unfold tailWord_7516421
  simp only [CollatzResearch.WordTrace]
  refine ⟨274146395902297894351133117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182764263934865262900755411 274146395902297894351133117)
  ·
    refine ⟨102804898463361710381674919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274146395902297894351133117 102804898463361710381674919)
    ·
      refine ⟨154207347695042565572512379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102804898463361710381674919 154207347695042565572512379)
      ·
        refine ⟨231311021542563848358768569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154207347695042565572512379 231311021542563848358768569)
        ·
          refine ⟨173483266156922886269076427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231311021542563848358768569 173483266156922886269076427)
          ·
            refine ⟨260224899235384329403614641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173483266156922886269076427 260224899235384329403614641)
            ·
              refine ⟨195168674426538247052710981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260224899235384329403614641 195168674426538247052710981)
              ·
                refine ⟨36594126454975921322383309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195168674426538247052710981 36594126454975921322383309)
                ·
                  refine ⟨13722797420615970495893741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36594126454975921322383309 13722797420615970495893741)
                  ·
                    refine ⟨5146049032730988935960153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13722797420615970495893741 5146049032730988935960153)
                    ·
                      refine ⟨3859536774548241701970115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5146049032730988935960153 3859536774548241701970115)
                      ·
                        rfl

theorem cell23_7516421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 3, 2].length) (baseStart_7516421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516421 prefixEnd_7516421 := by exact prefixLift 7516421
  have htrace : WordTrace (prefixWord ++ tailWord_7516421) baseStart_7516421 baseEnd_7516421 := by
    simpa [prefixWord, tailWord_7516421, baseEnd_7516421] using wordTrace_append hprefix tailTrace_7516421
  have hstable : (prefixWord ++ tailWord_7516421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516421).length < 2 ^ (prefixWord ++ tailWord_7516421).sum := by decide
  have hdescent : baseEnd_7516421 < baseStart_7516421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516446 : List Nat := [4, 3, 2, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_7516446 : Nat := 118140960795 + 7516446 * 2 ^ 59
def prefixEnd_7516446 : Nat := 4983230072969 + 3 ^ 40 * 7516446 * 2
def baseEnd_7516446 : Nat := 3859549611564604104157501

theorem tailTrace_7516446 : CollatzResearch.WordTrace tailWord_7516446 prefixEnd_7516446 3859549611564604104157501 := by
  unfold tailWord_7516446
  simp only [CollatzResearch.WordTrace]
  refine ⟨34268413465900915452599149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182764871818138215747195461 34268413465900915452599149)
  ·
    refine ⟨12850655049712843294724681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34268413465900915452599149 12850655049712843294724681)
    ·
      refine ⟨9637991287284632471043511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12850655049712843294724681 9637991287284632471043511)
      ·
        refine ⟨14456986930926948706565267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9637991287284632471043511 14456986930926948706565267)
        ·
          refine ⟨21685480396390423059847901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14456986930926948706565267 21685480396390423059847901)
          ·
            refine ⟨8132055148646408647442963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21685480396390423059847901 8132055148646408647442963)
            ·
              refine ⟨12198082722969612971164445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8132055148646408647442963 12198082722969612971164445)
              ·
                refine ⟨4574281021113604864186667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12198082722969612971164445 4574281021113604864186667)
                ·
                  refine ⟨6861421531670407296280001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4574281021113604864186667 6861421531670407296280001)
                  ·
                    refine ⟨5146066148752805472210001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6861421531670407296280001 5146066148752805472210001)
                    ·
                      refine ⟨3859549611564604104157501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5146066148752805472210001 3859549611564604104157501)
                      ·
                        rfl

theorem cell23_7516446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_7516446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516446 prefixEnd_7516446 := by exact prefixLift 7516446
  have htrace : WordTrace (prefixWord ++ tailWord_7516446) baseStart_7516446 baseEnd_7516446 := by
    simpa [prefixWord, tailWord_7516446, baseEnd_7516446] using wordTrace_append hprefix tailTrace_7516446
  have hstable : (prefixWord ++ tailWord_7516446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516446).length < 2 ^ (prefixWord ++ tailWord_7516446).sum := by decide
  have hdescent : baseEnd_7516446 < baseStart_7516446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516451 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 3, 4, 2]
def baseStart_7516451 : Nat := 118140960795 + 7516451 * 2 ^ 59
def prefixEnd_7516451 : Nat := 4983230072969 + 3 ^ 40 * 7516451 * 2
def baseEnd_7516451 : Nat := 3859552178967876584594977

theorem tailTrace_7516451 : CollatzResearch.WordTrace tailWord_7516451 prefixEnd_7516451 3859552178967876584594977 := by
  unfold tailWord_7516451
  simp only [CollatzResearch.WordTrace]
  refine ⟨274147490092189209474725207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182764993394792806316483471 274147490092189209474725207)
  ·
    refine ⟨411221235138283814212087811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274147490092189209474725207 411221235138283814212087811)
    ·
      refine ⟨616831852707425721318131717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411221235138283814212087811 616831852707425721318131717)
      ·
        refine ⟨115655972382642322747149697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 616831852707425721318131717 115655972382642322747149697)
        ·
          refine ⟨86741979286981742060362273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115655972382642322747149697 86741979286981742060362273)
          ·
            refine ⟨65056484465236306545271705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86741979286981742060362273 65056484465236306545271705)
            ·
              refine ⟨48792363348927229908953779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65056484465236306545271705 48792363348927229908953779)
              ·
                refine ⟨73188545023390844863430669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48792363348927229908953779 73188545023390844863430669)
                ·
                  refine ⟨27445704383771566823786501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73188545023390844863430669 27445704383771566823786501)
                  ·
                    refine ⟨5146069571957168779459969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27445704383771566823786501 5146069571957168779459969)
                    ·
                      refine ⟨3859552178967876584594977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5146069571957168779459969 3859552178967876584594977)
                      ·
                        rfl

theorem cell23_7516451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_7516451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516451 prefixEnd_7516451 := by exact prefixLift 7516451
  have htrace : WordTrace (prefixWord ++ tailWord_7516451) baseStart_7516451 baseEnd_7516451 := by
    simpa [prefixWord, tailWord_7516451, baseEnd_7516451] using wordTrace_append hprefix tailTrace_7516451
  have hstable : (prefixWord ++ tailWord_7516451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516451).length < 2 ^ (prefixWord ++ tailWord_7516451).sum := by decide
  have hdescent : baseEnd_7516451 < baseStart_7516451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516464 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 4]
def baseStart_7516464 : Nat := 118140960795 + 7516464 * 2 ^ 59
def prefixEnd_7516464 : Nat := 4983230072969 + 3 ^ 40 * 7516464 * 2
def baseEnd_7516464 : Nat := 3859558854216385033732417

theorem tailTrace_7516464 : CollatzResearch.WordTrace tailWord_7516464 prefixEnd_7516464 3859558854216385033732417 := by
  unfold tailWord_7516464
  simp only [CollatzResearch.WordTrace]
  refine ⟨137073982120571056347474223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182765309494094741796632297 137073982120571056347474223)
  ·
    refine ⟨205610973180856584521211335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137073982120571056347474223 205610973180856584521211335)
    ·
      refine ⟨308416459771284876781817003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205610973180856584521211335 308416459771284876781817003)
      ·
        refine ⟨462624689656927315172725505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308416459771284876781817003 462624689656927315172725505)
        ·
          refine ⟨346968517242695486379544129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462624689656927315172725505 346968517242695486379544129)
          ·
            refine ⟨260226387932021614784658097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346968517242695486379544129 260226387932021614784658097)
            ·
              refine ⟨195169790949016211088493573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260226387932021614784658097 195169790949016211088493573)
              ·
                refine ⟨36594335802940539579092545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195169790949016211088493573 36594335802940539579092545)
                ·
                  refine ⟨27445751852205404684319409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36594335802940539579092545 27445751852205404684319409)
                  ·
                    refine ⟨20584313889154053513239557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27445751852205404684319409 20584313889154053513239557)
                    ·
                      refine ⟨3859558854216385033732417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20584313889154053513239557 3859558854216385033732417)
                      ·
                        rfl

theorem cell23_7516464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 4].length) (baseStart_7516464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516464 prefixEnd_7516464 := by exact prefixLift 7516464
  have htrace : WordTrace (prefixWord ++ tailWord_7516464) baseStart_7516464 baseEnd_7516464 := by
    simpa [prefixWord, tailWord_7516464, baseEnd_7516464] using wordTrace_append hprefix tailTrace_7516464
  have hstable : (prefixWord ++ tailWord_7516464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516464).length < 2 ^ (prefixWord ++ tailWord_7516464).sum := by decide
  have hdescent : baseEnd_7516464 < baseStart_7516464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516558 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4]
def baseStart_7516558 : Nat := 118140960795 + 7516558 * 2 ^ 59
def prefixEnd_7516558 : Nat := 4983230072969 + 3 ^ 40 * 7516558 * 2
def baseEnd_7516558 : Nat := 3859607121397907665956985

theorem tailTrace_7516558 : CollatzResearch.WordTrace tailWord_7516558 prefixEnd_7516558 3859607121397907665956985 := by
  unfold tailWord_7516558
  simp only [CollatzResearch.WordTrace]
  refine ⟨34268924087850195843608791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182767595135201044499246885 34268924087850195843608791)
  ·
    refine ⟨51403386131775293765413187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34268924087850195843608791 51403386131775293765413187)
    ·
      refine ⟨77105079197662940648119781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51403386131775293765413187 77105079197662940648119781)
      ·
        refine ⟨14457202349561801371522459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77105079197662940648119781 14457202349561801371522459)
        ·
          refine ⟨21685803524342702057283689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14457202349561801371522459 21685803524342702057283689)
          ·
            refine ⟨16264352643257026542962767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21685803524342702057283689 16264352643257026542962767)
            ·
              refine ⟨24396528964885539814444151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16264352643257026542962767 24396528964885539814444151)
              ·
                refine ⟨36594793447328309721666227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24396528964885539814444151 36594793447328309721666227)
                ·
                  refine ⟨54892190170992464582499341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36594793447328309721666227 54892190170992464582499341)
                  ·
                    refine ⟨20584571314122174218437253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54892190170992464582499341 20584571314122174218437253)
                    ·
                      refine ⟨3859607121397907665956985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20584571314122174218437253 3859607121397907665956985)
                      ·
                        rfl

theorem cell23_7516558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_7516558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516558 prefixEnd_7516558 := by exact prefixLift 7516558
  have htrace : WordTrace (prefixWord ++ tailWord_7516558) baseStart_7516558 baseEnd_7516558 := by
    simpa [prefixWord, tailWord_7516558, baseEnd_7516558] using wordTrace_append hprefix tailTrace_7516558
  have hstable : (prefixWord ++ tailWord_7516558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516558).length < 2 ^ (prefixWord ++ tailWord_7516558).sum := by decide
  have hdescent : baseEnd_7516558 < baseStart_7516558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516578 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 4, 2, 3]
def baseStart_7516578 : Nat := 118140960795 + 7516578 * 2 ^ 59
def prefixEnd_7516578 : Nat := 4983230072969 + 3 ^ 40 * 7516578 * 2
def baseEnd_7516578 : Nat := 3859617391010997587706893

theorem tailTrace_7516578 : CollatzResearch.WordTrace tailWord_7516578 prefixEnd_7516578 3859617391010997587706893 := by
  unfold tailWord_7516578
  simp only [CollatzResearch.WordTrace]
  refine ⟨68538030540682277541149597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182768081441819406776398925 68538030540682277541149597)
  ·
    refine ⟨25701761452755854077931099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68538030540682277541149597 25701761452755854077931099)
    ·
      refine ⟨38552642179133781116896649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25701761452755854077931099 38552642179133781116896649)
      ·
        refine ⟨28914481634350335837672487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38552642179133781116896649 28914481634350335837672487)
        ·
          refine ⟨43371722451525503756508731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28914481634350335837672487 43371722451525503756508731)
          ·
            refine ⟨65057583677288255634763097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43371722451525503756508731 65057583677288255634763097)
            ·
              refine ⟨48793187757966191726072323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65057583677288255634763097 48793187757966191726072323)
              ·
                refine ⟨73189781636949287589108485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48793187757966191726072323 73189781636949287589108485)
                ·
                  refine ⟨13723084056927991422957841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73189781636949287589108485 13723084056927991422957841)
                  ·
                    refine ⟨10292313042695993567218381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13723084056927991422957841 10292313042695993567218381)
                    ·
                      refine ⟨3859617391010997587706893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10292313042695993567218381 3859617391010997587706893)
                      ·
                        rfl

theorem cell23_7516578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_7516578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516578 prefixEnd_7516578 := by exact prefixLift 7516578
  have htrace : WordTrace (prefixWord ++ tailWord_7516578) baseStart_7516578 baseEnd_7516578 := by
    simpa [prefixWord, tailWord_7516578, baseEnd_7516578] using wordTrace_append hprefix tailTrace_7516578
  have hstable : (prefixWord ++ tailWord_7516578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516578).length < 2 ^ (prefixWord ++ tailWord_7516578).sum := by decide
  have hdescent : baseEnd_7516578 < baseStart_7516578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516618 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 1, 5, 2]
def baseStart_7516618 : Nat := 118140960795 + 7516618 * 2 ^ 59
def prefixEnd_7516618 : Nat := 4983230072969 + 3 ^ 40 * 7516618 * 2
def baseEnd_7516618 : Nat := 3859637930237177431206709

theorem tailTrace_7516618 : CollatzResearch.WordTrace tailWord_7516618 prefixEnd_7516618 3859637930237177431206709 := by
  unfold tailWord_7516618
  simp only [CollatzResearch.WordTrace]
  refine ⟨68538395270646049249013627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182769054055056131330703005 68538395270646049249013627)
  ·
    refine ⟨102807592905969073873520441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68538395270646049249013627 102807592905969073873520441)
    ·
      refine ⟨77105694679476805405140331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102807592905969073873520441 77105694679476805405140331)
      ·
        refine ⟨115658542019215208107710497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77105694679476805405140331 115658542019215208107710497)
        ·
          refine ⟨86743906514411406080782873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115658542019215208107710497 86743906514411406080782873)
          ·
            refine ⟨65057929885808554560587155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86743906514411406080782873 65057929885808554560587155)
            ·
              refine ⟨97586894828712831840880733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65057929885808554560587155 97586894828712831840880733)
              ·
                refine ⟨36595085560767311940330275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97586894828712831840880733 36595085560767311940330275)
                ·
                  refine ⟨54892628341150967910495413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36595085560767311940330275 54892628341150967910495413)
                  ·
                    refine ⟨5146183906982903241608945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54892628341150967910495413 5146183906982903241608945)
                    ·
                      refine ⟨3859637930237177431206709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5146183906982903241608945 3859637930237177431206709)
                      ·
                        rfl

theorem cell23_7516618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_7516618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516618 prefixEnd_7516618 := by exact prefixLift 7516618
  have htrace : WordTrace (prefixWord ++ tailWord_7516618) baseStart_7516618 baseEnd_7516618 := by
    simpa [prefixWord, tailWord_7516618, baseEnd_7516618] using wordTrace_append hprefix tailTrace_7516618
  have hstable : (prefixWord ++ tailWord_7516618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516618).length < 2 ^ (prefixWord ++ tailWord_7516618).sum := by decide
  have hdescent : baseEnd_7516618 < baseStart_7516618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516631 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 4]
def baseStart_7516631 : Nat := 118140960795 + 7516631 * 2 ^ 59
def prefixEnd_7516631 : Nat := 4983230072969 + 3 ^ 40 * 7516631 * 2
def baseEnd_7516631 : Nat := 3859644605485685880344149

theorem tailTrace_7516631 : CollatzResearch.WordTrace tailWord_7516631 prefixEnd_7516631 3859644605485685880344149 := by
  unfold tailWord_7516631
  simp only [CollatzResearch.WordTrace]
  refine ⟨274154055231537100216277747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182769370154358066810851831 274154055231537100216277747)
  ·
    refine ⟨411231082847305650324416621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274154055231537100216277747 411231082847305650324416621)
    ·
      refine ⟨154211656067739618871656233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411231082847305650324416621 154211656067739618871656233)
      ·
        refine ⟨115658742050804714153742175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154211656067739618871656233 115658742050804714153742175)
        ·
          refine ⟨173488113076207071230613263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115658742050804714153742175 173488113076207071230613263)
          ·
            refine ⟨260232169614310606845919895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173488113076207071230613263 260232169614310606845919895)
            ·
              refine ⟨390348254421465910268879843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260232169614310606845919895 390348254421465910268879843)
              ·
                refine ⟨585522381632198865403319765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390348254421465910268879843 585522381632198865403319765)
                ·
                  refine ⟨13723180819504660907890307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 585522381632198865403319765 13723180819504660907890307)
                  ·
                    refine ⟨20584771229256991361835461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13723180819504660907890307 20584771229256991361835461)
                    ·
                      refine ⟨3859644605485685880344149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20584771229256991361835461 3859644605485685880344149)
                      ·
                        rfl

theorem cell23_7516631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_7516631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516631 prefixEnd_7516631 := by exact prefixLift 7516631
  have htrace : WordTrace (prefixWord ++ tailWord_7516631) baseStart_7516631 baseEnd_7516631 := by
    simpa [prefixWord, tailWord_7516631, baseEnd_7516631] using wordTrace_append hprefix tailTrace_7516631
  have hstable : (prefixWord ++ tailWord_7516631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516631).length < 2 ^ (prefixWord ++ tailWord_7516631).sum := by decide
  have hdescent : baseEnd_7516631 < baseStart_7516631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516651 : List Nat := [1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 5]
def baseStart_7516651 : Nat := 118140960795 + 7516651 * 2 ^ 59
def prefixEnd_7516651 : Nat := 4983230072969 + 3 ^ 40 * 7516651 * 2
def baseEnd_7516651 : Nat := 3859654875098775802094057

theorem tailTrace_7516651 : CollatzResearch.WordTrace tailWord_7516651 prefixEnd_7516651 3859654875098775802094057 := by
  unfold tailWord_7516651
  simp only [CollatzResearch.WordTrace]
  refine ⟨274154784691464643632005807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182769856460976429088003871 274154784691464643632005807)
  ·
    refine ⟨411232177037196965448008711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274154784691464643632005807 411232177037196965448008711)
    ·
      refine ⟨616848265555795448172013067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411232177037196965448008711 616848265555795448172013067)
      ·
        refine ⟨925272398333693172258019601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616848265555795448172013067 925272398333693172258019601)
        ·
          refine ⟨693954298750269879193514701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 925272398333693172258019601 693954298750269879193514701)
          ·
            refine ⟨260232862031351204697568013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 693954298750269879193514701 260232862031351204697568013)
            ·
              refine ⟨97587323261756701761588005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260232862031351204697568013 97587323261756701761588005)
              ·
                refine ⟨18297623111579381580297751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97587323261756701761588005 18297623111579381580297751)
                ·
                  refine ⟨27446434667369072370446627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18297623111579381580297751 27446434667369072370446627)
                  ·
                    refine ⟨41169652001053608555669941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27446434667369072370446627 41169652001053608555669941)
                    ·
                      refine ⟨3859654875098775802094057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41169652001053608555669941 3859654875098775802094057)
                      ·
                        rfl

theorem cell23_7516651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 5].length) (baseStart_7516651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516651 prefixEnd_7516651 := by exact prefixLift 7516651
  have htrace : WordTrace (prefixWord ++ tailWord_7516651) baseStart_7516651 baseEnd_7516651 := by
    simpa [prefixWord, tailWord_7516651, baseEnd_7516651] using wordTrace_append hprefix tailTrace_7516651
  have hstable : (prefixWord ++ tailWord_7516651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516651).length < 2 ^ (prefixWord ++ tailWord_7516651).sum := by decide
  have hdescent : baseEnd_7516651 < baseStart_7516651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516665 : List Nat := [1, 2, 1, 3, 1, 2, 2, 4, 3, 2, 2]
def baseStart_7516665 : Nat := 118140960795 + 7516665 * 2 ^ 59
def prefixEnd_7516665 : Nat := 4983230072969 + 3 ^ 40 * 7516665 * 2
def baseEnd_7516665 : Nat := 3859662063827938747318993

theorem tailTrace_7516665 : CollatzResearch.WordTrace tailWord_7516665 prefixEnd_7516665 3859662063827938747318993 := by
  unfold tailWord_7516665
  simp only [CollatzResearch.WordTrace]
  refine ⟨274155295313413924023015449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182770196875609282682010299 274155295313413924023015449)
  ·
    refine ⟨205616471485060443017261587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274155295313413924023015449 205616471485060443017261587)
    ·
      refine ⟨308424707227590664525892381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205616471485060443017261587 308424707227590664525892381)
      ·
        refine ⟨115659265210346499197209643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308424707227590664525892381 115659265210346499197209643)
        ·
          refine ⟨173488897815519748795814465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115659265210346499197209643 173488897815519748795814465)
          ·
            refine ⟨130116673361639811596860849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173488897815519748795814465 130116673361639811596860849)
            ·
              refine ⟨97587505021229858697645637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130116673361639811596860849 97587505021229858697645637)
              ·
                refine ⟨18297657191480598505808557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97587505021229858697645637 18297657191480598505808557)
                ·
                  refine ⟨6861621446805224439678209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18297657191480598505808557 6861621446805224439678209)
                  ·
                    refine ⟨5146216085103918329758657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6861621446805224439678209 5146216085103918329758657)
                    ·
                      refine ⟨3859662063827938747318993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5146216085103918329758657 3859662063827938747318993)
                      ·
                        rfl

theorem cell23_7516665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_7516665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516665 prefixEnd_7516665 := by exact prefixLift 7516665
  have htrace : WordTrace (prefixWord ++ tailWord_7516665) baseStart_7516665 baseEnd_7516665 := by
    simpa [prefixWord, tailWord_7516665, baseEnd_7516665] using wordTrace_append hprefix tailTrace_7516665
  have hstable : (prefixWord ++ tailWord_7516665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516665).length < 2 ^ (prefixWord ++ tailWord_7516665).sum := by decide
  have hdescent : baseEnd_7516665 < baseStart_7516665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516692 : List Nat := [2, 4, 3, 1, 1, 1, 1, 4, 2, 4]
def baseStart_7516692 : Nat := 118140960795 + 7516692 * 2 ^ 59
def prefixEnd_7516692 : Nat := 4983230072969 + 3 ^ 40 * 7516692 * 2
def baseEnd_7516692 : Nat := 1286558642601870047227123

theorem tailTrace_7516692 : CollatzResearch.WordTrace tailWord_7516692 prefixEnd_7516692 1286558642601870047227123 := by
  unfold tailWord_7516692
  simp only [CollatzResearch.WordTrace]
  refine ⟨137078140042158053817124165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182770853389544071756165553 137078140042158053817124165)
  ·
    refine ⟨25702151257904635090710781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137078140042158053817124165 25702151257904635090710781)
    ·
      refine ⟨9638306721714238159016543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25702151257904635090710781 9638306721714238159016543)
      ·
        refine ⟨14457460082571357238524815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9638306721714238159016543 14457460082571357238524815)
        ·
          refine ⟨21686190123857035857787223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14457460082571357238524815 21686190123857035857787223)
          ·
            refine ⟨32529285185785553786680835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21686190123857035857787223 32529285185785553786680835)
            ·
              refine ⟨48793927778678330680021253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32529285185785553786680835 48793927778678330680021253)
              ·
                refine ⟨9148861458502187002503985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48793927778678330680021253 9148861458502187002503985)
                ·
                  refine ⟨6861646093876640251877989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9148861458502187002503985 6861646093876640251877989)
                  ·
                    refine ⟨1286558642601870047227123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6861646093876640251877989 1286558642601870047227123)
                    ·
                      rfl

theorem cell23_7516692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_7516692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516692 prefixEnd_7516692 := by exact prefixLift 7516692
  have htrace : WordTrace (prefixWord ++ tailWord_7516692) baseStart_7516692 baseEnd_7516692 := by
    simpa [prefixWord, tailWord_7516692, baseEnd_7516692] using wordTrace_append hprefix tailTrace_7516692
  have hstable : (prefixWord ++ tailWord_7516692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516692).length < 2 ^ (prefixWord ++ tailWord_7516692).sum := by decide
  have hdescent : baseEnd_7516692 < baseStart_7516692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516725 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 3, 3, 2]
def baseStart_7516725 : Nat := 118140960795 + 7516725 * 2 ^ 59
def prefixEnd_7516725 : Nat := 4983230072969 + 3 ^ 40 * 7516725 * 2
def baseEnd_7516725 : Nat := 3859692872667208512568717

theorem tailTrace_7516725 : CollatzResearch.WordTrace tailWord_7516725 prefixEnd_7516725 3859692872667208512568717 := by
  unfold tailWord_7516725
  simp only [CollatzResearch.WordTrace]
  refine ⟨274157483693196554270199629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182771655795464369513466419 274157483693196554270199629)
  ·
    refine ⟨102809056384948707851324861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274157483693196554270199629 102809056384948707851324861)
    ·
      refine ⟨38553396144355765444246823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102809056384948707851324861 38553396144355765444246823)
      ·
        refine ⟨57830094216533648166370235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38553396144355765444246823 57830094216533648166370235)
        ·
          refine ⟨86745141324800472249555353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57830094216533648166370235 86745141324800472249555353)
          ·
            refine ⟨65058855993600354187166515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86745141324800472249555353 65058855993600354187166515)
            ·
              refine ⟨97588283990400531280749773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65058855993600354187166515 97588283990400531280749773)
              ·
                refine ⟨36595606496400199230281165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97588283990400531280749773 36595606496400199230281165)
                ·
                  refine ⟨13723352436150074711355437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36595606496400199230281165 13723352436150074711355437)
                  ·
                    refine ⟨5146257163556278016758289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13723352436150074711355437 5146257163556278016758289)
                    ·
                      refine ⟨3859692872667208512568717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5146257163556278016758289 3859692872667208512568717)
                      ·
                        rfl

theorem cell23_7516725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_7516725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516725 prefixEnd_7516725 := by exact prefixLift 7516725
  have htrace : WordTrace (prefixWord ++ tailWord_7516725) baseStart_7516725 baseEnd_7516725 := by
    simpa [prefixWord, tailWord_7516725, baseEnd_7516725] using wordTrace_append hprefix tailTrace_7516725
  have hstable : (prefixWord ++ tailWord_7516725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516725).length < 2 ^ (prefixWord ++ tailWord_7516725).sum := by decide
  have hdescent : baseEnd_7516725 < baseStart_7516725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516749 : List Nat := [1, 6, 1, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_7516749 : Nat := 118140960795 + 7516749 * 2 ^ 59
def prefixEnd_7516749 : Nat := 4983230072969 + 3 ^ 40 * 7516749 * 2
def baseEnd_7516749 : Nat := 3859705196202916418668607

theorem tailTrace_7516749 : CollatzResearch.WordTrace tailWord_7516749 prefixEnd_7516749 3859705196202916418668607 := by
  unfold tailWord_7516749
  simp only [CollatzResearch.WordTrace]
  refine ⟨274158359045109606369073301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182772239363406404246048867 274158359045109606369073301)
  ·
    refine ⟨12851173080239512798550311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 274158359045109606369073301 12851173080239512798550311)
    ·
      refine ⟨19276759620359269197825467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12851173080239512798550311 19276759620359269197825467)
      ·
        refine ⟨28915139430538903796738201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19276759620359269197825467 28915139430538903796738201)
        ·
          refine ⟨21686354572904177847553651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28915139430538903796738201 21686354572904177847553651)
          ·
            refine ⟨32529531859356266771330477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21686354572904177847553651 32529531859356266771330477)
            ·
              refine ⟨12198574447258600039248929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32529531859356266771330477 12198574447258600039248929)
              ·
                refine ⟨9148930835443950029436697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12198574447258600039248929 9148930835443950029436697)
                ·
                  refine ⟨6861698126582962522077523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9148930835443950029436697 6861698126582962522077523)
                  ·
                    refine ⟨10292547189874443783116285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6861698126582962522077523 10292547189874443783116285)
                    ·
                      refine ⟨3859705196202916418668607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10292547189874443783116285 3859705196202916418668607)
                      ·
                        rfl

theorem cell23_7516749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_7516749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516749 prefixEnd_7516749 := by exact prefixLift 7516749
  have htrace : WordTrace (prefixWord ++ tailWord_7516749) baseStart_7516749 baseEnd_7516749 := by
    simpa [prefixWord, tailWord_7516749, baseEnd_7516749] using wordTrace_append hprefix tailTrace_7516749
  have hstable : (prefixWord ++ tailWord_7516749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516749).length < 2 ^ (prefixWord ++ tailWord_7516749).sum := by decide
  have hdescent : baseEnd_7516749 < baseStart_7516749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516768 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 4]
def baseStart_7516768 : Nat := 118140960795 + 7516768 * 2 ^ 59
def prefixEnd_7516768 : Nat := 4983230072969 + 3 ^ 40 * 7516768 * 2
def baseEnd_7516768 : Nat := 3859714952335351844331019

theorem tailTrace_7516768 : CollatzResearch.WordTrace tailWord_7516768 prefixEnd_7516768 3859714952335351844331019 := by
  unfold tailWord_7516768
  simp only [CollatzResearch.WordTrace]
  refine ⟨137079526016020386307007479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182772701354693848409343305 137079526016020386307007479)
  ·
    refine ⟨205619289024030579460511219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137079526016020386307007479 205619289024030579460511219)
    ·
      refine ⟨308428933536045869190766829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205619289024030579460511219 308428933536045869190766829)
      ·
        refine ⟨115660850076017200946537561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308428933536045869190766829 115660850076017200946537561)
        ·
          refine ⟨86745637557012900709903171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115660850076017200946537561 86745637557012900709903171)
          ·
            refine ⟨130118456335519351064854757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86745637557012900709903171 130118456335519351064854757)
            ·
              refine ⟨24397210562909878324660267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130118456335519351064854757 24397210562909878324660267)
              ·
                refine ⟨36595815844364817486990401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24397210562909878324660267 36595815844364817486990401)
                ·
                  refine ⟨27446861883273613115242801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36595815844364817486990401 27446861883273613115242801)
                  ·
                    refine ⟨20585146412455209836432101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27446861883273613115242801 20585146412455209836432101)
                    ·
                      refine ⟨3859714952335351844331019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20585146412455209836432101 3859714952335351844331019)
                      ·
                        rfl

theorem cell23_7516768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_7516768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516768 prefixEnd_7516768 := by exact prefixLift 7516768
  have htrace : WordTrace (prefixWord ++ tailWord_7516768) baseStart_7516768 baseEnd_7516768 := by
    simpa [prefixWord, tailWord_7516768, baseEnd_7516768] using wordTrace_append hprefix tailTrace_7516768
  have hstable : (prefixWord ++ tailWord_7516768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516768).length < 2 ^ (prefixWord ++ tailWord_7516768).sum := by decide
  have hdescent : baseEnd_7516768 < baseStart_7516768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516778 : List Nat := [3, 1, 3, 2, 1, 1, 1, 4, 7]
def baseStart_7516778 : Nat := 118140960795 + 7516778 * 2 ^ 59
def prefixEnd_7516778 : Nat := 4983230072969 + 3 ^ 40 * 7516778 * 2
def baseEnd_7516778 : Nat := 428857787460210756133997

theorem tailTrace_7516778 : CollatzResearch.WordTrace tailWord_7516778 prefixEnd_7516778 428857787460210756133997 := by
  unfold tailWord_7516778
  simp only [CollatzResearch.WordTrace]
  refine ⟨68539854190501136080469747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182772944508003029547919325 68539854190501136080469747)
  ·
    refine ⟨102809781285751704120704621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68539854190501136080469747 102809781285751704120704621)
    ·
      refine ⟨38553667982156889045264233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102809781285751704120704621 38553667982156889045264233)
      ·
        refine ⟨28915250986617666783948175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38553667982156889045264233 28915250986617666783948175)
        ·
          refine ⟨43372876479926500175922263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28915250986617666783948175 43372876479926500175922263)
          ·
            refine ⟨65059314719889750263883395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43372876479926500175922263 65059314719889750263883395)
            ·
              refine ⟨97588972079834625395825093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65059314719889750263883395 97588972079834625395825093)
              ·
                refine ⟨18297932264968992261717205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97588972079834625395825093 18297932264968992261717205)
                ·
                  refine ⟨428857787460210756133997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18297932264968992261717205 428857787460210756133997)
                  ·
                    rfl

theorem cell23_7516778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 7].length) (baseStart_7516778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516778 prefixEnd_7516778 := by exact prefixLift 7516778
  have htrace : WordTrace (prefixWord ++ tailWord_7516778) baseStart_7516778 baseEnd_7516778 := by
    simpa [prefixWord, tailWord_7516778, baseEnd_7516778] using wordTrace_append hprefix tailTrace_7516778
  have hstable : (prefixWord ++ tailWord_7516778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516778).length < 2 ^ (prefixWord ++ tailWord_7516778).sum := by decide
  have hdescent : baseEnd_7516778 < baseStart_7516778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516858 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6]
def baseStart_7516858 : Nat := 118140960795 + 7516858 * 2 ^ 59
def prefixEnd_7516858 : Nat := 4983230072969 + 3 ^ 40 * 7516858 * 2
def baseEnd_7516858 : Nat := 3859761165594256492205605

theorem tailTrace_7516858 : CollatzResearch.WordTrace tailWord_7516858 prefixEnd_7516858 3859761165594256492205605 := by
  unfold tailWord_7516858
  simp only [CollatzResearch.WordTrace]
  refine ⟨68540583650428679496197807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182774889734476478656527485 68540583650428679496197807)
  ·
    refine ⟨102810875475643019244296711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68540583650428679496197807 102810875475643019244296711)
    ·
      refine ⟨154216313213464528866445067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102810875475643019244296711 154216313213464528866445067)
      ·
        refine ⟨231324469820196793299667601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154216313213464528866445067 231324469820196793299667601)
        ·
          refine ⟨173493352365147594974750701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231324469820196793299667601 173493352365147594974750701)
          ·
            refine ⟨65060007136930348115531513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173493352365147594974750701 65060007136930348115531513)
            ·
              refine ⟨48795005352697761086648635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65060007136930348115531513 48795005352697761086648635)
              ·
                refine ⟨73192508029046641629972953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48795005352697761086648635 73192508029046641629972953)
                ·
                  refine ⟨54894381021784981222479715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73192508029046641629972953 54894381021784981222479715)
                  ·
                    refine ⟨82341571532677471833719573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54894381021784981222479715 82341571532677471833719573)
                    ·
                      refine ⟨3859761165594256492205605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82341571532677471833719573 3859761165594256492205605)
                      ·
                        rfl

theorem cell23_7516858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_7516858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516858 prefixEnd_7516858 := by exact prefixLift 7516858
  have htrace : WordTrace (prefixWord ++ tailWord_7516858) baseStart_7516858 baseEnd_7516858 := by
    simpa [prefixWord, tailWord_7516858, baseEnd_7516858] using wordTrace_append hprefix tailTrace_7516858
  have hstable : (prefixWord ++ tailWord_7516858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516858).length < 2 ^ (prefixWord ++ tailWord_7516858).sum := by decide
  have hdescent : baseEnd_7516858 < baseStart_7516858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516862 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2]
def baseStart_7516862 : Nat := 118140960795 + 7516862 * 2 ^ 59
def prefixEnd_7516862 : Nat := 4983230072969 + 3 ^ 40 * 7516862 * 2
def baseEnd_7516862 : Nat := 3859763219516874476555587

theorem tailTrace_7516862 : CollatzResearch.WordTrace tailWord_7516862 prefixEnd_7516862 3859763219516874476555587 := by
  unfold tailWord_7516862
  simp only [CollatzResearch.WordTrace]
  refine ⟨34270310061712528333492105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182774986995800151111957893 34270310061712528333492105)
  ·
    refine ⟨25702732546284396250119079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34270310061712528333492105 25702732546284396250119079)
    ·
      refine ⟨38554098819426594375178619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25702732546284396250119079 38554098819426594375178619)
      ·
        refine ⟨57831148229139891562767929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38554098819426594375178619 57831148229139891562767929)
        ·
          refine ⟨43373361171854918672075947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57831148229139891562767929 43373361171854918672075947)
          ·
            refine ⟨65060041757782378008113921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43373361171854918672075947 65060041757782378008113921)
            ·
              refine ⟨48795031318336783506085441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65060041757782378008113921 48795031318336783506085441)
              ·
                refine ⟨36596273488752587629564081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48795031318336783506085441 36596273488752587629564081)
                ·
                  refine ⟨27447205116564440722173061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36596273488752587629564081 27447205116564440722173061)
                  ·
                    refine ⟨5146350959355832635407449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27447205116564440722173061 5146350959355832635407449)
                    ·
                      refine ⟨3859763219516874476555587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5146350959355832635407449 3859763219516874476555587)
                      ·
                        rfl

theorem cell23_7516862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_7516862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516862 prefixEnd_7516862 := by exact prefixLift 7516862
  have htrace : WordTrace (prefixWord ++ tailWord_7516862) baseStart_7516862 baseEnd_7516862 := by
    simpa [prefixWord, tailWord_7516862, baseEnd_7516862] using wordTrace_append hprefix tailTrace_7516862
  have hstable : (prefixWord ++ tailWord_7516862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516862).length < 2 ^ (prefixWord ++ tailWord_7516862).sum := by decide
  have hdescent : baseEnd_7516862 < baseStart_7516862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516899 : List Nat := [1, 1, 1, 7, 1, 3, 1, 1, 2, 2, 3]
def baseStart_7516899 : Nat := 118140960795 + 7516899 * 2 ^ 59
def prefixEnd_7516899 : Nat := 4983230072969 + 3 ^ 40 * 7516899 * 2
def baseEnd_7516899 : Nat := 3859782218301090831792917

theorem tailTrace_7516899 : CollatzResearch.WordTrace tailWord_7516899 prefixEnd_7516899 3859782218301090831792917 := by
  unfold tailWord_7516899
  simp only [CollatzResearch.WordTrace]
  refine ⟨274163829994566181987033751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182775886663044121324689167 274163829994566181987033751)
  ·
    refine ⟨411245744991849272980550627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274163829994566181987033751 411245744991849272980550627)
    ·
      refine ⟨616868617487773909470825941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411245744991849272980550627 616868617487773909470825941)
      ·
        refine ⟨14457858222369701003222483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 616868617487773909470825941 14457858222369701003222483)
        ·
          refine ⟨21686787333554551504833725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14457858222369701003222483 21686787333554551504833725)
          ·
            refine ⟨8132545250082956814312647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21686787333554551504833725 8132545250082956814312647)
            ·
              refine ⟨12198817875124435221468971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8132545250082956814312647 12198817875124435221468971)
              ·
                refine ⟨18298226812686652832203457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12198817875124435221468971 18298226812686652832203457)
                ·
                  refine ⟨13723670109514989624152593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18298226812686652832203457 13723670109514989624152593)
                  ·
                    refine ⟨10292752582136242218114445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13723670109514989624152593 10292752582136242218114445)
                    ·
                      refine ⟨3859782218301090831792917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10292752582136242218114445 3859782218301090831792917)
                      ·
                        rfl

theorem cell23_7516899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_7516899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516899 prefixEnd_7516899 := by exact prefixLift 7516899
  have htrace : WordTrace (prefixWord ++ tailWord_7516899) baseStart_7516899 baseEnd_7516899 := by
    simpa [prefixWord, tailWord_7516899, baseEnd_7516899] using wordTrace_append hprefix tailTrace_7516899
  have hstable : (prefixWord ++ tailWord_7516899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516899).length < 2 ^ (prefixWord ++ tailWord_7516899).sum := by decide
  have hdescent : baseEnd_7516899 < baseStart_7516899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516908 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 5]
def baseStart_7516908 : Nat := 118140960795 + 7516908 * 2 ^ 59
def prefixEnd_7516908 : Nat := 4983230072969 + 3 ^ 40 * 7516908 * 2
def baseEnd_7516908 : Nat := 3859786839626981296580375

theorem tailTrace_7516908 : CollatzResearch.WordTrace tailWord_7516908 prefixEnd_7516908 3859786839626981296580375 := by
  unfold tailWord_7516908
  simp only [CollatzResearch.WordTrace]
  refine ⟨137082079125766788262055689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182776105501022384349407585 137082079125766788262055689)
  ·
    refine ⟨102811559344325091196541767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137082079125766788262055689 102811559344325091196541767)
    ·
      refine ⟨154217339016487636794812651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102811559344325091196541767 154217339016487636794812651)
      ·
        refine ⟨231326008524731455192218977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154217339016487636794812651 231326008524731455192218977)
        ·
          refine ⟨173494506393548591394164233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231326008524731455192218977 173494506393548591394164233)
          ·
            refine ⟨130120879795161443545623175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173494506393548591394164233 130120879795161443545623175)
            ·
              refine ⟨195181319692742165318434763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130120879795161443545623175 195181319692742165318434763)
              ·
                refine ⟨292771979539113247977652145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195181319692742165318434763 292771979539113247977652145)
                ·
                  refine ⟨219578984654334935983239109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292771979539113247977652145 219578984654334935983239109)
                  ·
                    refine ⟨41171059622687800496857333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 219578984654334935983239109 41171059622687800496857333)
                    ·
                      refine ⟨3859786839626981296580375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41171059622687800496857333 3859786839626981296580375)
                      ·
                        rfl

theorem cell23_7516908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_7516908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516908 prefixEnd_7516908 := by exact prefixLift 7516908
  have htrace : WordTrace (prefixWord ++ tailWord_7516908) baseStart_7516908 baseEnd_7516908 := by
    simpa [prefixWord, tailWord_7516908, baseEnd_7516908] using wordTrace_append hprefix tailTrace_7516908
  have hstable : (prefixWord ++ tailWord_7516908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516908).length < 2 ^ (prefixWord ++ tailWord_7516908).sum := by decide
  have hdescent : baseEnd_7516908 < baseStart_7516908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516922 : List Nat := [3, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2]
def baseStart_7516922 : Nat := 118140960795 + 7516922 * 2 ^ 59
def prefixEnd_7516922 : Nat := 4983230072969 + 3 ^ 40 * 7516922 * 2
def baseEnd_7516922 : Nat := 3859794028356144241805311

theorem tailTrace_7516922 : CollatzResearch.WordTrace tailWord_7516922 prefixEnd_7516922 3859794028356144241805311 := by
  unfold tailWord_7516922
  simp only [CollatzResearch.WordTrace]
  refine ⟨68541167218370714228780255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182776445915655237943414013 68541167218370714228780255)
  ·
    refine ⟨102811750827556071343170383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68541167218370714228780255 102811750827556071343170383)
    ·
      refine ⟨154217626241334107014755575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102811750827556071343170383 154217626241334107014755575)
      ·
        refine ⟨231326439362001160522133363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154217626241334107014755575 231326439362001160522133363)
        ·
          refine ⟨346989659043001740783200045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231326439362001160522133363 346989659043001740783200045)
          ·
            refine ⟨130121122141125652793700017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346989659043001740783200045 130121122141125652793700017)
            ·
              refine ⟨97590841605844239595275013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130121122141125652793700017 97590841605844239595275013)
              ·
                refine ⟨18298282801095794924114065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97590841605844239595275013 18298282801095794924114065)
                ·
                  refine ⟨13723712100821846193085549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18298282801095794924114065 13723712100821846193085549)
                  ·
                    refine ⟨5146392037808192322407081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13723712100821846193085549 5146392037808192322407081)
                    ·
                      refine ⟨3859794028356144241805311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5146392037808192322407081 3859794028356144241805311)
                      ·
                        rfl

theorem cell23_7516922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2].length) (baseStart_7516922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516922 prefixEnd_7516922 := by exact prefixLift 7516922
  have htrace : WordTrace (prefixWord ++ tailWord_7516922) baseStart_7516922 baseEnd_7516922 := by
    simpa [prefixWord, tailWord_7516922, baseEnd_7516922] using wordTrace_append hprefix tailTrace_7516922
  have hstable : (prefixWord ++ tailWord_7516922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516922).length < 2 ^ (prefixWord ++ tailWord_7516922).sum := by decide
  have hdescent : baseEnd_7516922 < baseStart_7516922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516945 : List Nat := [1, 2, 2, 1, 1, 3, 5, 1, 1, 6]
def baseStart_7516945 : Nat := 118140960795 + 7516945 * 2 ^ 59
def prefixEnd_7516945 : Nat := 4983230072969 + 3 ^ 40 * 7516945 * 2
def baseEnd_7516945 : Nat := 1286601946137065883939235

theorem tailTrace_7516945 : CollatzResearch.WordTrace tailWord_7516945 prefixEnd_7516945 1286601946137065883939235 := by
  unfold tailWord_7516945
  simp only [CollatzResearch.WordTrace]
  refine ⟨274165507752399531843208289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182777005168266354562138859 274165507752399531843208289)
  ·
    refine ⟨205624130814299648882406217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274165507752399531843208289 205624130814299648882406217)
    ·
      refine ⟨154218098110724736661804663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205624130814299648882406217 154218098110724736661804663)
      ·
        refine ⟨231327147166087104992706995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154218098110724736661804663 231327147166087104992706995)
        ·
          refine ⟨346990720749130657489060493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231327147166087104992706995 346990720749130657489060493)
          ·
            refine ⟨130121520280923996558397685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346990720749130657489060493 130121520280923996558397685)
            ·
              refine ⟨12198892526336624677349783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130121520280923996558397685 12198892526336624677349783)
              ·
                refine ⟨18298338789504937016024675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12198892526336624677349783 18298338789504937016024675)
                ·
                  refine ⟨27447508184257405524037013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18298338789504937016024675 27447508184257405524037013)
                  ·
                    refine ⟨1286601946137065883939235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27447508184257405524037013 1286601946137065883939235)
                    ·
                      rfl

theorem cell23_7516945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 6].length) (baseStart_7516945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516945 prefixEnd_7516945 := by exact prefixLift 7516945
  have htrace : WordTrace (prefixWord ++ tailWord_7516945) baseStart_7516945 baseEnd_7516945 := by
    simpa [prefixWord, tailWord_7516945, baseEnd_7516945] using wordTrace_append hprefix tailTrace_7516945
  have hstable : (prefixWord ++ tailWord_7516945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516945).length < 2 ^ (prefixWord ++ tailWord_7516945).sum := by decide
  have hdescent : baseEnd_7516945 < baseStart_7516945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516962 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 4, 4]
def baseStart_7516962 : Nat := 118140960795 + 7516962 * 2 ^ 59
def prefixEnd_7516962 : Nat := 4983230072969 + 3 ^ 40 * 7516962 * 2
def baseEnd_7516962 : Nat := 1286604855860774695101709

theorem tailTrace_7516962 : CollatzResearch.WordTrace tailWord_7516962 prefixEnd_7516962 1286604855860774695101709 := by
  unfold tailWord_7516962
  simp only [CollatzResearch.WordTrace]
  refine ⟨68541531948334485936644285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182777418528891962497718093 68541531948334485936644285)
  ·
    refine ⟨25703074480625432226241607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68541531948334485936644285 25703074480625432226241607)
    ·
      refine ⟨38554611720938148339362411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25703074480625432226241607 38554611720938148339362411)
      ·
        refine ⟨57831917581407222509043617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38554611720938148339362411 57831917581407222509043617)
        ·
          refine ⟨43373938186055416881782713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57831917581407222509043617 43373938186055416881782713)
          ·
            refine ⟨32530453639541562661337035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43373938186055416881782713 32530453639541562661337035)
            ·
              refine ⟨48795680459312343992005553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32530453639541562661337035 48795680459312343992005553)
              ·
                refine ⟨36596760344484257994004165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48795680459312343992005553 36596760344484257994004165)
                ·
                  refine ⟨6861892564590798373875781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36596760344484257994004165 6861892564590798373875781)
                  ·
                    refine ⟨1286604855860774695101709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6861892564590798373875781 1286604855860774695101709)
                    ·
                      rfl

theorem cell23_7516962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_7516962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516962 prefixEnd_7516962 := by exact prefixLift 7516962
  have htrace : WordTrace (prefixWord ++ tailWord_7516962) baseStart_7516962 baseEnd_7516962 := by
    simpa [prefixWord, tailWord_7516962, baseEnd_7516962] using wordTrace_append hprefix tailTrace_7516962
  have hstable : (prefixWord ++ tailWord_7516962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516962).length < 2 ^ (prefixWord ++ tailWord_7516962).sum := by decide
  have hdescent : baseEnd_7516962 < baseStart_7516962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516965 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 3, 2, 4]
def baseStart_7516965 : Nat := 118140960795 + 7516965 * 2 ^ 59
def prefixEnd_7516965 : Nat := 4983230072969 + 3 ^ 40 * 7516965 * 2
def baseEnd_7516965 : Nat := 3859816108024287573567613

theorem tailTrace_7516965 : CollatzResearch.WordTrace tailWord_7516965 prefixEnd_7516965 3859816108024287573567613 := by
  unfold tailWord_7516965
  simp only [CollatzResearch.WordTrace]
  refine ⟨274166237212327075258936349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182777491474884716839290899 274166237212327075258936349)
  ·
    refine ⟨102812338954622653222101131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274166237212327075258936349 102812338954622653222101131)
    ·
      refine ⟨154218508431933979833151697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102812338954622653222101131 154218508431933979833151697)
      ·
        refine ⟨115663881323950484874863773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154218508431933979833151697 115663881323950484874863773)
        ·
          refine ⟨43373955496481431828073915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115663881323950484874863773 43373955496481431828073915)
          ·
            refine ⟨65060933244722147742110873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43373955496481431828073915 65060933244722147742110873)
            ·
              refine ⟨48795699933541610806583155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65060933244722147742110873 48795699933541610806583155)
              ·
                refine ⟨73193549900312416209874733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48795699933541610806583155 73193549900312416209874733)
                ·
                  refine ⟨27447581212617156078703025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73193549900312416209874733 27447581212617156078703025)
                  ·
                    refine ⟨20585685909462867059027269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27447581212617156078703025 20585685909462867059027269)
                    ·
                      refine ⟨3859816108024287573567613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20585685909462867059027269 3859816108024287573567613)
                      ·
                        rfl

theorem cell23_7516965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_7516965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516965 prefixEnd_7516965 := by exact prefixLift 7516965
  have htrace : WordTrace (prefixWord ++ tailWord_7516965) baseStart_7516965 baseEnd_7516965 := by
    simpa [prefixWord, tailWord_7516965, baseEnd_7516965] using wordTrace_append hprefix tailTrace_7516965
  have hstable : (prefixWord ++ tailWord_7516965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516965).length < 2 ^ (prefixWord ++ tailWord_7516965).sum := by decide
  have hdescent : baseEnd_7516965 < baseStart_7516965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516972 : List Nat := [2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 3]
def baseStart_7516972 : Nat := 118140960795 + 7516972 * 2 ^ 59
def prefixEnd_7516972 : Nat := 4983230072969 + 3 ^ 40 * 7516972 * 2
def baseEnd_7516972 : Nat := 3859819702388869046180081

theorem tailTrace_7516972 : CollatzResearch.WordTrace tailWord_7516972 prefixEnd_7516972 3859819702388869046180081 := by
  unfold tailWord_7516972
  simp only [CollatzResearch.WordTrace]
  refine ⟨137083246261650857727220585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182777661682201143636294113 137083246261650857727220585)
  ·
    refine ⟨102812434696238143295415439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137083246261650857727220585 102812434696238143295415439)
    ·
      refine ⟨154218652044357214943123159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102812434696238143295415439 154218652044357214943123159)
      ·
        refine ⟨231327978066535822414684739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154218652044357214943123159 231327978066535822414684739)
        ·
          refine ⟨346991967099803733622027109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231327978066535822414684739 346991967099803733622027109)
          ·
            refine ⟨65060993831213200054130083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 346991967099803733622027109 65060993831213200054130083)
            ·
              refine ⟨97591490746819800081195125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65060993831213200054130083 97591490746819800081195125)
              ·
                refine ⟨9149202257514356257612043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97591490746819800081195125 9149202257514356257612043)
                ·
                  refine ⟨13723803386271534386418065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9149202257514356257612043 13723803386271534386418065)
                  ·
                    refine ⟨10292852539703650789813549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13723803386271534386418065 10292852539703650789813549)
                    ·
                      refine ⟨3859819702388869046180081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10292852539703650789813549 3859819702388869046180081)
                      ·
                        rfl

theorem cell23_7516972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 3].length) (baseStart_7516972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516972 prefixEnd_7516972 := by exact prefixLift 7516972
  have htrace : WordTrace (prefixWord ++ tailWord_7516972) baseStart_7516972 baseEnd_7516972 := by
    simpa [prefixWord, tailWord_7516972, baseEnd_7516972] using wordTrace_append hprefix tailTrace_7516972
  have hstable : (prefixWord ++ tailWord_7516972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516972).length < 2 ^ (prefixWord ++ tailWord_7516972).sum := by decide
  have hdescent : baseEnd_7516972 < baseStart_7516972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516973 : List Nat := [1, 5, 3, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_7516973 : Nat := 118140960795 + 7516973 * 2 ^ 59
def prefixEnd_7516973 : Nat := 4983230072969 + 3 ^ 40 * 7516973 * 2
def baseEnd_7516973 : Nat := 3859820215869523542267577

theorem tailTrace_7516973 : CollatzResearch.WordTrace tailWord_7516973 prefixEnd_7516973 3859820215869523542267577 := by
  unfold tailWord_7516973
  simp only [CollatzResearch.WordTrace]
  refine ⟨274166528996298092625227573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182777685997532061750151715 274166528996298092625227573)
  ·
    refine ⟨25703112093402946183615085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 274166528996298092625227573 25703112093402946183615085)
    ·
      refine ⟨9638667035026104818855657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25703112093402946183615085 9638667035026104818855657)
      ·
        refine ⟨7229000276269578614141743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9638667035026104818855657 7229000276269578614141743)
        ·
          refine ⟨10843500414404367921212615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7229000276269578614141743 10843500414404367921212615)
          ·
            refine ⟨16265250621606551881818923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10843500414404367921212615 16265250621606551881818923)
            ·
              refine ⟨24397875932409827822728385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16265250621606551881818923 24397875932409827822728385)
              ·
                refine ⟨18298406949307370867046289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24397875932409827822728385 18298406949307370867046289)
                ·
                  refine ⟨13723805211980528150284717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18298406949307370867046289 13723805211980528150284717)
                  ·
                    refine ⟨5146426954492698056356769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13723805211980528150284717 5146426954492698056356769)
                    ·
                      refine ⟨3859820215869523542267577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5146426954492698056356769 3859820215869523542267577)
                      ·
                        rfl

theorem cell23_7516973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_7516973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516973 prefixEnd_7516973 := by exact prefixLift 7516973
  have htrace : WordTrace (prefixWord ++ tailWord_7516973) baseStart_7516973 baseEnd_7516973 := by
    simpa [prefixWord, tailWord_7516973, baseEnd_7516973] using wordTrace_append hprefix tailTrace_7516973
  have hstable : (prefixWord ++ tailWord_7516973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516973).length < 2 ^ (prefixWord ++ tailWord_7516973).sum := by decide
  have hdescent : baseEnd_7516973 < baseStart_7516973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7516980 : List Nat := [2, 5, 1, 1, 3, 1, 3, 2, 1, 1, 3]
def baseStart_7516980 : Nat := 118140960795 + 7516980 * 2 ^ 59
def prefixEnd_7516980 : Nat := 4983230072969 + 3 ^ 40 * 7516980 * 2
def baseEnd_7516980 : Nat := 3859823810234105014880045

theorem tailTrace_7516980 : CollatzResearch.WordTrace tailWord_7516980 prefixEnd_7516980 3859823810234105014880045 := by
  unfold tailWord_7516980
  simp only [CollatzResearch.WordTrace]
  refine ⟨137083392153636366410366197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182777856204848488547154929 137083392153636366410366197)
  ·
    refine ⟨12851568014403409350971831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137083392153636366410366197 12851568014403409350971831)
    ·
      refine ⟨19277352021605114026457747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12851568014403409350971831 19277352021605114026457747)
      ·
        refine ⟨28916028032407671039686621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19277352021605114026457747 28916028032407671039686621)
        ·
          refine ⟨10843510512152876639882483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28916028032407671039686621 10843510512152876639882483)
          ·
            refine ⟨16265265768229314959823725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10843510512152876639882483 16265265768229314959823725)
            ·
              refine ⟨6099474663085993109933897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16265265768229314959823725 6099474663085993109933897)
              ·
                refine ⟨4574605997314494832450423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6099474663085993109933897 4574605997314494832450423)
                ·
                  refine ⟨6861908995971742248675635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4574605997314494832450423 6861908995971742248675635)
                  ·
                    refine ⟨10292863493957613373013453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6861908995971742248675635 10292863493957613373013453)
                    ·
                      refine ⟨3859823810234105014880045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10292863493957613373013453 3859823810234105014880045)
                      ·
                        rfl

theorem cell23_7516980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_7516980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7516980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7516980 prefixEnd_7516980 := by exact prefixLift 7516980
  have htrace : WordTrace (prefixWord ++ tailWord_7516980) baseStart_7516980 baseEnd_7516980 := by
    simpa [prefixWord, tailWord_7516980, baseEnd_7516980] using wordTrace_append hprefix tailTrace_7516980
  have hstable : (prefixWord ++ tailWord_7516980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7516980).length < 2 ^ (prefixWord ++ tailWord_7516980).sum := by decide
  have hdescent : baseEnd_7516980 < baseStart_7516980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7516980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517002 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 6, 1, 3]
def baseStart_7517002 : Nat := 118140960795 + 7517002 * 2 ^ 59
def prefixEnd_7517002 : Nat := 4983230072969 + 3 ^ 40 * 7517002 * 2
def baseEnd_7517002 : Nat := 3859835106808503928804943

theorem tailTrace_7517002 : CollatzResearch.WordTrace tailWord_7517002 prefixEnd_7517002 3859835106808503928804943 := by
  unfold tailWord_7517002
  simp only [CollatzResearch.WordTrace]
  refine ⟨68541896678298257644508315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182778391142128687052022173 68541896678298257644508315)
  ·
    refine ⟨102812845017447386466762473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68541896678298257644508315 102812845017447386466762473)
    ·
      refine ⟨77109633763085539850071855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102812845017447386466762473 77109633763085539850071855)
      ·
        refine ⟨115664450644628309775107783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77109633763085539850071855 115664450644628309775107783)
        ·
          refine ⟨173496675966942464662661675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115664450644628309775107783 173496675966942464662661675)
          ·
            refine ⟨260245013950413696993992513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173496675966942464662661675 260245013950413696993992513)
            ·
              refine ⟨195183760462810272745494385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260245013950413696993992513 195183760462810272745494385)
              ·
                refine ⟨146387820347107704559120789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195183760462810272745494385 146387820347107704559120789)
                ·
                  refine ⟨6861929078770673651208787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146387820347107704559120789 6861929078770673651208787)
                  ·
                    refine ⟨10292893618156010476813181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6861929078770673651208787 10292893618156010476813181)
                    ·
                      refine ⟨3859835106808503928804943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10292893618156010476813181 3859835106808503928804943)
                      ·
                        rfl

theorem cell23_7517002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_7517002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517002 prefixEnd_7517002 := by exact prefixLift 7517002
  have htrace : WordTrace (prefixWord ++ tailWord_7517002) baseStart_7517002 baseEnd_7517002 := by
    simpa [prefixWord, tailWord_7517002, baseEnd_7517002] using wordTrace_append hprefix tailTrace_7517002
  have hstable : (prefixWord ++ tailWord_7517002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517002).length < 2 ^ (prefixWord ++ tailWord_7517002).sum := by decide
  have hdescent : baseEnd_7517002 < baseStart_7517002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517029 : List Nat := [1, 3, 1, 3, 1, 1, 2, 5, 1, 3, 2]
def baseStart_7517029 : Nat := 118140960795 + 7517029 * 2 ^ 59
def prefixEnd_7517029 : Nat := 4983230072969 + 3 ^ 40 * 7517029 * 2
def baseEnd_7517029 : Nat := 3859848970786175323167319

theorem tailTrace_7517029 : CollatzResearch.WordTrace tailWord_7517029 prefixEnd_7517029 3859848970786175323167319 := by
  unfold tailWord_7517029
  simp only [CollatzResearch.WordTrace]
  refine ⟨274168571484095214189266141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182779047656063476126177427 274168571484095214189266141)
  ·
    refine ⟨102813214306535705320974803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274168571484095214189266141 102813214306535705320974803)
    ·
      refine ⟨154219821459803557981462205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102813214306535705320974803 154219821459803557981462205)
      ·
        refine ⟨57832433047426334243048327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154219821459803557981462205 57832433047426334243048327)
        ·
          refine ⟨86748649571139501364572491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57832433047426334243048327 86748649571139501364572491)
          ·
            refine ⟨130122974356709252046858737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86748649571139501364572491 130122974356709252046858737)
            ·
              refine ⟨97592230767531939035144053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130122974356709252046858737 97592230767531939035144053)
              ·
                refine ⟨9149271634456119284544755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97592230767531939035144053 9149271634456119284544755)
                ·
                  refine ⟨13723907451684178926817133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9149271634456119284544755 13723907451684178926817133)
                  ·
                    refine ⟨5146465294381567097556425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13723907451684178926817133 5146465294381567097556425)
                    ·
                      refine ⟨3859848970786175323167319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5146465294381567097556425 3859848970786175323167319)
                      ·
                        rfl

theorem cell23_7517029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_7517029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517029 prefixEnd_7517029 := by exact prefixLift 7517029
  have htrace : WordTrace (prefixWord ++ tailWord_7517029) baseStart_7517029 baseEnd_7517029 := by
    simpa [prefixWord, tailWord_7517029, baseEnd_7517029] using wordTrace_append hprefix tailTrace_7517029
  have hstable : (prefixWord ++ tailWord_7517029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517029).length < 2 ^ (prefixWord ++ tailWord_7517029).sum := by decide
  have hdescent : baseEnd_7517029 < baseStart_7517029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517046 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2]
def baseStart_7517046 : Nat := 118140960795 + 7517046 * 2 ^ 59
def prefixEnd_7517046 : Nat := 4983230072969 + 3 ^ 40 * 7517046 * 2
def baseEnd_7517046 : Nat := 3859857699957301756654741

theorem tailTrace_7517046 : CollatzResearch.WordTrace tailWord_7517046 prefixEnd_7517046 3859857699957301756654741 := by
  unfold tailWord_7517046
  simp only [CollatzResearch.WordTrace]
  refine ⟨17135574470314601630789687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182779461016689084061756661 17135574470314601630789687)
  ·
    refine ⟨25703361705471902446184531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17135574470314601630789687 25703361705471902446184531)
    ·
      refine ⟨38555042558207853669276797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25703361705471902446184531 38555042558207853669276797)
      ·
        refine ⟨14458140959327945125978799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38555042558207853669276797 14458140959327945125978799)
        ·
          refine ⟨21687211438991917688968199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14458140959327945125978799 21687211438991917688968199)
          ·
            refine ⟨32530817158487876533452299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21687211438991917688968199 32530817158487876533452299)
            ·
              refine ⟨48796225737731814800178449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32530817158487876533452299 48796225737731814800178449)
              ·
                refine ⟨36597169303298861100133837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48796225737731814800178449 36597169303298861100133837)
                ·
                  refine ⟨13723938488737072912550189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36597169303298861100133837 13723938488737072912550189)
                  ·
                    refine ⟨5146476933276402342206321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13723938488737072912550189 5146476933276402342206321)
                    ·
                      refine ⟨3859857699957301756654741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5146476933276402342206321 3859857699957301756654741)
                      ·
                        rfl

theorem cell23_7517046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_7517046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517046 prefixEnd_7517046 := by exact prefixLift 7517046
  have htrace : WordTrace (prefixWord ++ tailWord_7517046) baseStart_7517046 baseEnd_7517046 := by
    simpa [prefixWord, tailWord_7517046, baseEnd_7517046] using wordTrace_append hprefix tailTrace_7517046
  have hstable : (prefixWord ++ tailWord_7517046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517046).length < 2 ^ (prefixWord ++ tailWord_7517046).sum := by decide
  have hdescent : baseEnd_7517046 < baseStart_7517046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517055 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 4]
def baseStart_7517055 : Nat := 118140960795 + 7517055 * 2 ^ 59
def prefixEnd_7517055 : Nat := 4983230072969 + 3 ^ 40 * 7517055 * 2
def baseEnd_7517055 : Nat := 3859862321283192221442199

theorem tailTrace_7517055 : CollatzResearch.WordTrace tailWord_7517055 prefixEnd_7517055 3859862321283192221442199 := by
  unfold tailWord_7517055
  simp only [CollatzResearch.WordTrace]
  refine ⟨274169519782001020629712619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182779679854667347086475079 274169519782001020629712619)
  ·
    refine ⟨411254279673001530944568929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274169519782001020629712619 411254279673001530944568929)
    ·
      refine ⟨308440709754751148208426697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411254279673001530944568929 308440709754751148208426697)
      ·
        refine ⟨231330532316063361156320023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308440709754751148208426697 231330532316063361156320023)
        ·
          refine ⟨346995798474095041734480035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231330532316063361156320023 346995798474095041734480035)
          ·
            refine ⟨520493697711142562601720053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346995798474095041734480035 520493697711142562601720053)
            ·
              refine ⟨48796284160419615243911255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 520493697711142562601720053 48796284160419615243911255)
              ·
                refine ⟨73194426240629422865866883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48796284160419615243911255 73194426240629422865866883)
                ·
                  refine ⟨109791639360944134298800325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73194426240629422865866883 109791639360944134298800325)
                  ·
                    refine ⟨20585932380177025181025061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109791639360944134298800325 20585932380177025181025061)
                    ·
                      refine ⟨3859862321283192221442199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20585932380177025181025061 3859862321283192221442199)
                      ·
                        rfl

theorem cell23_7517055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_7517055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517055 prefixEnd_7517055 := by exact prefixLift 7517055
  have htrace : WordTrace (prefixWord ++ tailWord_7517055) baseStart_7517055 baseEnd_7517055 := by
    simpa [prefixWord, tailWord_7517055, baseEnd_7517055] using wordTrace_append hprefix tailTrace_7517055
  have hstable : (prefixWord ++ tailWord_7517055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517055).length < 2 ^ (prefixWord ++ tailWord_7517055).sum := by decide
  have hdescent : baseEnd_7517055 < baseStart_7517055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517059 : List Nat := [1, 1, 1, 3, 4, 1, 4, 1, 1, 4, 2]
def baseStart_7517059 : Nat := 118140960795 + 7517059 * 2 ^ 59
def prefixEnd_7517059 : Nat := 4983230072969 + 3 ^ 40 * 7517059 * 2
def baseEnd_7517059 : Nat := 3859864375205810205792181

theorem tailTrace_7517059 : CollatzResearch.WordTrace tailWord_7517059 prefixEnd_7517059 3859864375205810205792181 := by
  unfold tailWord_7517059
  simp only [CollatzResearch.WordTrace]
  refine ⟨274169665673986529312858231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182779777115991019541905487 274169665673986529312858231)
  ·
    refine ⟨411254498510979793969287347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274169665673986529312858231 411254498510979793969287347)
    ·
      refine ⟨616881747766469690953931021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411254498510979793969287347 616881747766469690953931021)
      ·
        refine ⟨231330655412426134107724133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 616881747766469690953931021 231330655412426134107724133)
        ·
          refine ⟨43374497889829900145198275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231330655412426134107724133 43374497889829900145198275)
          ·
            refine ⟨65061746834744850217797413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43374497889829900145198275 65061746834744850217797413)
            ·
              refine ⟨12199077531514659415837015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65061746834744850217797413 12199077531514659415837015)
              ·
                refine ⟨18298616297271989123755523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12199077531514659415837015 18298616297271989123755523)
                ·
                  refine ⟨27447924445907983685633285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18298616297271989123755523 27447924445907983685633285)
                  ·
                    refine ⟨5146485833607746941056241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27447924445907983685633285 5146485833607746941056241)
                    ·
                      refine ⟨3859864375205810205792181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5146485833607746941056241 3859864375205810205792181)
                      ·
                        rfl

theorem cell23_7517059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 4, 2].length) (baseStart_7517059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517059 prefixEnd_7517059 := by exact prefixLift 7517059
  have htrace : WordTrace (prefixWord ++ tailWord_7517059) baseStart_7517059 baseEnd_7517059 := by
    simpa [prefixWord, tailWord_7517059, baseEnd_7517059] using wordTrace_append hprefix tailTrace_7517059
  have hstable : (prefixWord ++ tailWord_7517059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517059).length < 2 ^ (prefixWord ++ tailWord_7517059).sum := by decide
  have hdescent : baseEnd_7517059 < baseStart_7517059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517065 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 9]
def baseStart_7517065 : Nat := 118140960795 + 7517065 * 2 ^ 59
def prefixEnd_7517065 : Nat := 4983230072969 + 3 ^ 40 * 7517065 * 2
def baseEnd_7517065 : Nat := 428874161787748575813017

theorem tailTrace_7517065 : CollatzResearch.WordTrace tailWord_7517065 prefixEnd_7517065 428874161787748575813017 := by
  unfold tailWord_7517065
  simp only [CollatzResearch.WordTrace]
  refine ⟨274169884511964792337576649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182779923007976528225051099 274169884511964792337576649)
  ·
    refine ⟨205627413383973594253182487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274169884511964792337576649 205627413383973594253182487)
    ·
      refine ⟨308441120075960391379773731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205627413383973594253182487 308441120075960391379773731)
      ·
        refine ⟨462661680113940587069660597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308441120075960391379773731 462661680113940587069660597)
        ·
          refine ⟨43374532510681930037780681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 462661680113940587069660597 43374532510681930037780681)
          ·
            refine ⟨32530899383011447528335511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43374532510681930037780681 32530899383011447528335511)
            ·
              refine ⟨48796349074517171292503267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32530899383011447528335511 48796349074517171292503267)
              ·
                refine ⟨73194523611775756938754901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48796349074517171292503267 73194523611775756938754901)
                ·
                  refine ⟨428874161787748575813017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73194523611775756938754901 428874161787748575813017)
                  ·
                    rfl

theorem cell23_7517065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 9].length) (baseStart_7517065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517065 prefixEnd_7517065 := by exact prefixLift 7517065
  have htrace : WordTrace (prefixWord ++ tailWord_7517065) baseStart_7517065 baseEnd_7517065 := by
    simpa [prefixWord, tailWord_7517065, baseEnd_7517065] using wordTrace_append hprefix tailTrace_7517065
  have hstable : (prefixWord ++ tailWord_7517065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517065).length < 2 ^ (prefixWord ++ tailWord_7517065).sum := by decide
  have hdescent : baseEnd_7517065 < baseStart_7517065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517076 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 4, 2, 2]
def baseStart_7517076 : Nat := 118140960795 + 7517076 * 2 ^ 59
def prefixEnd_7517076 : Nat := 4983230072969 + 3 ^ 40 * 7517076 * 2
def baseEnd_7517076 : Nat := 3859873104376936639279603

theorem tailTrace_7517076 : CollatzResearch.WordTrace tailWord_7517076 prefixEnd_7517076 3859873104376936639279603 := by
  unfold tailWord_7517076
  simp only [CollatzResearch.WordTrace]
  refine ⟨137085142857462470608113541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182780190476616627477484721 137085142857462470608113541)
  ·
    refine ⟨25703464285774213239021289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137085142857462470608113541 25703464285774213239021289)
    ·
      refine ⟨19277598214330659929265967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25703464285774213239021289 19277598214330659929265967)
      ·
        refine ⟨28916397321495989893898951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19277598214330659929265967 28916397321495989893898951)
        ·
          refine ⟨43374595982243984840848427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28916397321495989893898951 43374595982243984840848427)
          ·
            refine ⟨65061893973365977261272641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43374595982243984840848427 65061893973365977261272641)
            ·
              refine ⟨48796420480024482945954481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65061893973365977261272641 48796420480024482945954481)
              ·
                refine ⟨36597315360018362209465861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48796420480024482945954481 36597315360018362209465861)
                ·
                  refine ⟨6861996630003442914274849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36597315360018362209465861 6861996630003442914274849)
                  ·
                    refine ⟨5146497472502582185706137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6861996630003442914274849 5146497472502582185706137)
                    ·
                      refine ⟨3859873104376936639279603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5146497472502582185706137 3859873104376936639279603)
                      ·
                        rfl

theorem cell23_7517076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_7517076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517076 prefixEnd_7517076 := by exact prefixLift 7517076
  have htrace : WordTrace (prefixWord ++ tailWord_7517076) baseStart_7517076 baseEnd_7517076 := by
    simpa [prefixWord, tailWord_7517076, baseEnd_7517076] using wordTrace_append hprefix tailTrace_7517076
  have hstable : (prefixWord ++ tailWord_7517076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517076).length < 2 ^ (prefixWord ++ tailWord_7517076).sum := by decide
  have hdescent : baseEnd_7517076 < baseStart_7517076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517092 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 4, 3, 3]
def baseStart_7517092 : Nat := 118140960795 + 7517092 * 2 ^ 59
def prefixEnd_7517092 : Nat := 4983230072969 + 3 ^ 40 * 7517092 * 2
def baseEnd_7517092 : Nat := 3859881320067408576679529

theorem tailTrace_7517092 : CollatzResearch.WordTrace tailWord_7517092 prefixEnd_7517092 3859881320067408576679529 := by
  unfold tailWord_7517092
  simp only [CollatzResearch.WordTrace]
  refine ⟨137085434641433487974404765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182780579521911317299206353 137085434641433487974404765)
  ·
    refine ⟨51407037990537557990401787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137085434641433487974404765 51407037990537557990401787)
    ·
      refine ⟨77110556985806336985602681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51407037990537557990401787 77110556985806336985602681)
      ·
        refine ⟨57832917739354752739202011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77110556985806336985602681 57832917739354752739202011)
        ·
          refine ⟨86749376609032129108803017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57832917739354752739202011 86749376609032129108803017)
          ·
            refine ⟨65062032456774096831602263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86749376609032129108803017 65062032456774096831602263)
            ·
              refine ⟨97593048685161145247403395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65062032456774096831602263 97593048685161145247403395)
              ·
                refine ⟨146389573027741717871105093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97593048685161145247403395 146389573027741717871105093)
                ·
                  refine ⟨27448044942701572100832205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146389573027741717871105093 27448044942701572100832205)
                  ·
                    refine ⟨10293016853513089537812077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27448044942701572100832205 10293016853513089537812077)
                    ·
                      refine ⟨3859881320067408576679529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10293016853513089537812077 3859881320067408576679529)
                      ·
                        rfl

theorem cell23_7517092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_7517092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517092 prefixEnd_7517092 := by exact prefixLift 7517092
  have htrace : WordTrace (prefixWord ++ tailWord_7517092) baseStart_7517092 baseEnd_7517092 := by
    simpa [prefixWord, tailWord_7517092, baseEnd_7517092] using wordTrace_append hprefix tailTrace_7517092
  have hstable : (prefixWord ++ tailWord_7517092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517092).length < 2 ^ (prefixWord ++ tailWord_7517092).sum := by decide
  have hdescent : baseEnd_7517092 < baseStart_7517092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517132 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 1, 3, 4]
def baseStart_7517132 : Nat := 118140960795 + 7517132 * 2 ^ 59
def prefixEnd_7517132 : Nat := 4983230072969 + 3 ^ 40 * 7517132 * 2
def baseEnd_7517132 : Nat := 3859901859293588420179345

theorem tailTrace_7517132 : CollatzResearch.WordTrace tailWord_7517132 prefixEnd_7517132 3859901859293588420179345 := by
  unfold tailWord_7517132
  simp only [CollatzResearch.WordTrace]
  refine ⟨137086164101361031390132825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182781552135148041853510433 137086164101361031390132825)
  ·
    refine ⟨102814623076020773542599619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137086164101361031390132825 102814623076020773542599619)
    ·
      refine ⟨154221934614031160313899429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102814623076020773542599619 154221934614031160313899429)
      ·
        refine ⟨28916612740130842558856143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154221934614031160313899429 28916612740130842558856143)
        ·
          refine ⟨43374919110196263838284215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28916612740130842558856143 43374919110196263838284215)
          ·
            refine ⟨65062378665294395757426323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43374919110196263838284215 65062378665294395757426323)
            ·
              refine ⟨97593567997941593636139485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65062378665294395757426323 97593567997941593636139485)
              ·
                refine ⟨36597587999228097613552307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97593567997941593636139485 36597587999228097613552307)
                ·
                  refine ⟨54896381998842146420328461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36597587999228097613552307 54896381998842146420328461)
                  ·
                    refine ⟨20586143249565804907623173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54896381998842146420328461 20586143249565804907623173)
                    ·
                      refine ⟨3859901859293588420179345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20586143249565804907623173 3859901859293588420179345)
                      ·
                        rfl

theorem cell23_7517132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_7517132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517132 prefixEnd_7517132 := by exact prefixLift 7517132
  have htrace : WordTrace (prefixWord ++ tailWord_7517132) baseStart_7517132 baseEnd_7517132 := by
    simpa [prefixWord, tailWord_7517132, baseEnd_7517132] using wordTrace_append hprefix tailTrace_7517132
  have hstable : (prefixWord ++ tailWord_7517132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517132).length < 2 ^ (prefixWord ++ tailWord_7517132).sum := by decide
  have hdescent : baseEnd_7517132 < baseStart_7517132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517149 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_7517149 : Nat := 118140960795 + 7517149 * 2 ^ 59
def prefixEnd_7517149 : Nat := 4983230072969 + 3 ^ 40 * 7517149 * 2
def baseEnd_7517149 : Nat := 3859910588464714853666767

theorem tailTrace_7517149 : CollatzResearch.WordTrace tailWord_7517149 prefixEnd_7517149 3859910588464714853666767 := by
  unfold tailWord_7517149
  simp only [CollatzResearch.WordTrace]
  refine ⟨274172948243660474683634501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182781965495773649789089667 274172948243660474683634501)
  ·
    refine ⟨51407427795686339003181469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274172948243660474683634501 51407427795686339003181469)
    ·
      refine ⟨19277785423382377126193051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51407427795686339003181469 19277785423382377126193051)
      ·
        refine ⟨28916678135073565689289577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19277785423382377126193051 28916678135073565689289577)
        ·
          refine ⟨21687508601305174266967183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28916678135073565689289577 21687508601305174266967183)
          ·
            refine ⟨32531262901957761400450775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21687508601305174266967183 32531262901957761400450775)
            ·
              refine ⟨48796894352936642100676163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32531262901957761400450775 48796894352936642100676163)
              ·
                refine ⟨73195341529404963151014245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48796894352936642100676163 73195341529404963151014245)
                ·
                  refine ⟨13724126536763430590815171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73195341529404963151014245 13724126536763430590815171)
                  ·
                    refine ⟨20586189805145145886222757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13724126536763430590815171 20586189805145145886222757)
                    ·
                      refine ⟨3859910588464714853666767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20586189805145145886222757 3859910588464714853666767)
                      ·
                        rfl

theorem cell23_7517149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_7517149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517149 prefixEnd_7517149 := by exact prefixLift 7517149
  have htrace : WordTrace (prefixWord ++ tailWord_7517149) baseStart_7517149 baseEnd_7517149 := by
    simpa [prefixWord, tailWord_7517149, baseEnd_7517149] using wordTrace_append hprefix tailTrace_7517149
  have hstable : (prefixWord ++ tailWord_7517149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517149).length < 2 ^ (prefixWord ++ tailWord_7517149).sum := by decide
  have hdescent : baseEnd_7517149 < baseStart_7517149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517236 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_7517236 : Nat := 118140960795 + 7517236 * 2 ^ 59
def prefixEnd_7517236 : Nat := 4983230072969 + 3 ^ 40 * 7517236 * 2
def baseEnd_7517236 : Nat := 1286651753760552004426289

theorem tailTrace_7517236 : CollatzResearch.WordTrace tailWord_7517236 prefixEnd_7517236 1286651753760552004426289 := by
  unfold tailWord_7517236
  simp only [CollatzResearch.WordTrace]
  refine ⟨137088060697172644271025781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182784080929563525694701041 137088060697172644271025781)
  ·
    refine ⟨12852005690359935400408667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137088060697172644271025781 12852005690359935400408667)
    ·
      refine ⟨19278008535539903100613001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12852005690359935400408667 19278008535539903100613001)
      ·
        refine ⟨14458506401654927325459751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19278008535539903100613001 14458506401654927325459751)
        ·
          refine ⟨21687759602482390988189627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14458506401654927325459751 21687759602482390988189627)
          ·
            refine ⟨32531639403723586482284441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21687759602482390988189627 32531639403723586482284441)
            ·
              refine ⟨24398729552792689861713331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32531639403723586482284441 24398729552792689861713331)
              ·
                refine ⟨36598094329189034792569997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24398729552792689861713331 36598094329189034792569997)
                ·
                  refine ⟨13724285373445888047213749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36598094329189034792569997 13724285373445888047213749)
                  ·
                    refine ⟨1286651753760552004426289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13724285373445888047213749 1286651753760552004426289)
                    ·
                      rfl

theorem cell23_7517236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_7517236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517236 prefixEnd_7517236 := by exact prefixLift 7517236
  have htrace : WordTrace (prefixWord ++ tailWord_7517236) baseStart_7517236 baseEnd_7517236 := by
    simpa [prefixWord, tailWord_7517236, baseEnd_7517236] using wordTrace_append hprefix tailTrace_7517236
  have hstable : (prefixWord ++ tailWord_7517236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517236).length < 2 ^ (prefixWord ++ tailWord_7517236).sum := by decide
  have hdescent : baseEnd_7517236 < baseStart_7517236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517239 : List Nat := [1, 1, 3, 1, 2, 2, 1, 6, 1, 1, 4]
def baseStart_7517239 : Nat := 118140960795 + 7517239 * 2 ^ 59
def prefixEnd_7517239 : Nat := 4983230072969 + 3 ^ 40 * 7517239 * 2
def baseEnd_7517239 : Nat := 3859956801723619501541353

theorem tailTrace_7517239 : CollatzResearch.WordTrace tailWord_7517239 prefixEnd_7517239 3859956801723619501541353 := by
  unfold tailWord_7517239
  simp only [CollatzResearch.WordTrace]
  refine ⟨274176230813334420054410771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182784153875556280036273847 274176230813334420054410771)
  ·
    refine ⟨411264346220001630081616157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274176230813334420054410771 411264346220001630081616157)
    ·
      refine ⟨154224129832500611280606059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411264346220001630081616157 154224129832500611280606059)
      ·
        refine ⟨231336194748750916920909089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154224129832500611280606059 231336194748750916920909089)
        ·
          refine ⟨173502146061563187690681817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231336194748750916920909089 173502146061563187690681817)
          ·
            refine ⟨130126609546172390768011363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173502146061563187690681817 130126609546172390768011363)
            ·
              refine ⟨195189914319258586152017045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130126609546172390768011363 195189914319258586152017045)
              ·
                refine ⟨9149527233715246225875799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 195189914319258586152017045 9149527233715246225875799)
                ·
                  refine ⟨13724290850572869338813699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9149527233715246225875799 13724290850572869338813699)
                  ·
                    refine ⟨20586436275859304008220549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13724290850572869338813699 20586436275859304008220549)
                    ·
                      refine ⟨3859956801723619501541353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20586436275859304008220549 3859956801723619501541353)
                      ·
                        rfl

theorem cell23_7517239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 1, 4].length) (baseStart_7517239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517239 prefixEnd_7517239 := by exact prefixLift 7517239
  have htrace : WordTrace (prefixWord ++ tailWord_7517239) baseStart_7517239 baseEnd_7517239 := by
    simpa [prefixWord, tailWord_7517239, baseEnd_7517239] using wordTrace_append hprefix tailTrace_7517239
  have hstable : (prefixWord ++ tailWord_7517239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517239).length < 2 ^ (prefixWord ++ tailWord_7517239).sum := by decide
  have hdescent : baseEnd_7517239 < baseStart_7517239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517256 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 5, 2, 2]
def baseStart_7517256 : Nat := 118140960795 + 7517256 * 2 ^ 59
def prefixEnd_7517256 : Nat := 4983230072969 + 3 ^ 40 * 7517256 * 2
def baseEnd_7517256 : Nat := 3859965530894745935028775

theorem tailTrace_7517256 : CollatzResearch.WordTrace tailWord_7517256 prefixEnd_7517256 3859965530894745935028775 := by
  unfold tailWord_7517256
  simp only [CollatzResearch.WordTrace]
  refine ⟨137088425427136415978889811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182784567236181887971853081 137088425427136415978889811)
  ·
    refine ⟨205632638140704623968334717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137088425427136415978889811 205632638140704623968334717)
    ·
      refine ⟨77112239302764233988125519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205632638140704623968334717 77112239302764233988125519)
      ·
        refine ⟨115668358954146350982188279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77112239302764233988125519 115668358954146350982188279)
        ·
          refine ⟨173502538431219526473282419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115668358954146350982188279 173502538431219526473282419)
          ·
            refine ⟨260253807646829289709923629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173502538431219526473282419 260253807646829289709923629)
            ·
              refine ⟨97595177867560983641221361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260253807646829289709923629 97595177867560983641221361)
              ·
                refine ⟨73196383400670737730916021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97595177867560983641221361 73196383400670737730916021)
                ·
                  refine ⟨6862160943812881662273377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73196383400670737730916021 6862160943812881662273377)
                  ·
                    refine ⟨5146620707859661246705033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6862160943812881662273377 5146620707859661246705033)
                    ·
                      refine ⟨3859965530894745935028775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5146620707859661246705033 3859965530894745935028775)
                      ·
                        rfl

theorem cell23_7517256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_7517256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517256 prefixEnd_7517256 := by exact prefixLift 7517256
  have htrace : WordTrace (prefixWord ++ tailWord_7517256) baseStart_7517256 baseEnd_7517256 := by
    simpa [prefixWord, tailWord_7517256, baseEnd_7517256] using wordTrace_append hprefix tailTrace_7517256
  have hstable : (prefixWord ++ tailWord_7517256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517256).length < 2 ^ (prefixWord ++ tailWord_7517256).sum := by decide
  have hdescent : baseEnd_7517256 < baseStart_7517256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517262 : List Nat := [4, 1, 1, 1, 1, 3, 12]
def baseStart_7517262 : Nat := 118140960795 + 7517262 * 2 ^ 59
def prefixEnd_7517262 : Nat := 4983230072969 + 3 ^ 40 * 7517262 * 2
def baseEnd_7517262 : Nat := 47653933478749048290787

theorem tailTrace_7517262 : CollatzResearch.WordTrace tailWord_7517262 prefixEnd_7517262 47653933478749048290787 := by
  unfold tailWord_7517262
  simp only [CollatzResearch.WordTrace]
  refine ⟨34272133711531386872812255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182784713128167396654998693 34272133711531386872812255)
  ·
    refine ⟨51408200567297080309218383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34272133711531386872812255 51408200567297080309218383)
    ·
      refine ⟨77112300850945620463827575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51408200567297080309218383 77112300850945620463827575)
      ·
        refine ⟨115668451276418430695741363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77112300850945620463827575 115668451276418430695741363)
        ·
          refine ⟨173502676914627646043612045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115668451276418430695741363 173502676914627646043612045)
          ·
            refine ⟨65063503842985367266354517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173502676914627646043612045 65063503842985367266354517)
            ·
              refine ⟨47653933478749048290787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 65063503842985367266354517 47653933478749048290787)
              ·
                rfl

theorem cell23_7517262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 12].length) (baseStart_7517262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517262 prefixEnd_7517262 := by exact prefixLift 7517262
  have htrace : WordTrace (prefixWord ++ tailWord_7517262) baseStart_7517262 baseEnd_7517262 := by
    simpa [prefixWord, tailWord_7517262, baseEnd_7517262] using wordTrace_append hprefix tailTrace_7517262
  have hstable : (prefixWord ++ tailWord_7517262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517262).length < 2 ^ (prefixWord ++ tailWord_7517262).sum := by decide
  have hdescent : baseEnd_7517262 < baseStart_7517262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517266 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 4, 4]
def baseStart_7517266 : Nat := 118140960795 + 7517266 * 2 ^ 59
def prefixEnd_7517266 : Nat := 4983230072969 + 3 ^ 40 * 7517266 * 2
def baseEnd_7517266 : Nat := 1286656888567096965301243

theorem tailTrace_7517266 : CollatzResearch.WordTrace tailWord_7517266 prefixEnd_7517266 1286656888567096965301243 := by
  unfold tailWord_7517266
  simp only [CollatzResearch.WordTrace]
  refine ⟨68544303896059150916410913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182784810389491069110429101 68544303896059150916410913)
  ·
    refine ⟨51408227922044363187308185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68544303896059150916410913 51408227922044363187308185)
    ·
      refine ⟨38556170941533272390481139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51408227922044363187308185 38556170941533272390481139)
      ·
        refine ⟨57834256412299908585721709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38556170941533272390481139 57834256412299908585721709)
        ·
          refine ⟨21687846154612465719645641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57834256412299908585721709 21687846154612465719645641)
          ·
            refine ⟨16265884615959349289734231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21687846154612465719645641 16265884615959349289734231)
            ·
              refine ⟨24398826923939023934601347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16265884615959349289734231 24398826923939023934601347)
              ·
                refine ⟨36598240385908535901902021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24398826923939023934601347 36598240385908535901902021)
                ·
                  refine ⟨6862170072357850481606629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36598240385908535901902021 6862170072357850481606629)
                  ·
                    refine ⟨1286656888567096965301243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6862170072357850481606629 1286656888567096965301243)
                    ·
                      rfl

theorem cell23_7517266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_7517266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517266 prefixEnd_7517266 := by exact prefixLift 7517266
  have htrace : WordTrace (prefixWord ++ tailWord_7517266) baseStart_7517266 baseEnd_7517266 := by
    simpa [prefixWord, tailWord_7517266, baseEnd_7517266] using wordTrace_append hprefix tailTrace_7517266
  have hstable : (prefixWord ++ tailWord_7517266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517266).length < 2 ^ (prefixWord ++ tailWord_7517266).sum := by decide
  have hdescent : baseEnd_7517266 < baseStart_7517266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517293 : List Nat := [1, 5, 1, 1, 2, 3, 2, 2, 1, 2, 3]
def baseStart_7517293 : Nat := 118140960795 + 7517293 * 2 ^ 59
def prefixEnd_7517293 : Nat := 4983230072969 + 3 ^ 40 * 7517293 * 2
def baseEnd_7517293 : Nat := 3859984529678962290266105

theorem tailTrace_7517293 : CollatzResearch.WordTrace tailWord_7517293 prefixEnd_7517293 3859984529678962290266105 := by
  unfold tailWord_7517293
  simp only [CollatzResearch.WordTrace]
  refine ⟨274178200355138787276876533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182785466903425858184584355 274178200355138787276876533)
  ·
    refine ⟨25704206283294261307207175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 274178200355138787276876533 25704206283294261307207175)
    ·
      refine ⟨38556309424941391960810763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25704206283294261307207175 38556309424941391960810763)
      ·
        refine ⟨57834464137412087941216145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38556309424941391960810763 57834464137412087941216145)
        ·
          refine ⟨43375848103059065955912109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57834464137412087941216145 43375848103059065955912109)
          ·
            refine ⟨16265943038647149733467041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43375848103059065955912109 16265943038647149733467041)
            ·
              refine ⟨12199457278985362300100281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16265943038647149733467041 12199457278985362300100281)
              ·
                refine ⟨9149592959239021725075211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12199457278985362300100281 9149592959239021725075211)
                ·
                  refine ⟨13724389438858532587612817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9149592959239021725075211 13724389438858532587612817)
                  ·
                    refine ⟨10293292079143899440709613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13724389438858532587612817 10293292079143899440709613)
                    ·
                      refine ⟨3859984529678962290266105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10293292079143899440709613 3859984529678962290266105)
                      ·
                        rfl

theorem cell23_7517293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_7517293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517293 prefixEnd_7517293 := by exact prefixLift 7517293
  have htrace : WordTrace (prefixWord ++ tailWord_7517293) baseStart_7517293 baseEnd_7517293 := by
    simpa [prefixWord, tailWord_7517293, baseEnd_7517293] using wordTrace_append hprefix tailTrace_7517293
  have hstable : (prefixWord ++ tailWord_7517293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517293).length < 2 ^ (prefixWord ++ tailWord_7517293).sum := by decide
  have hdescent : baseEnd_7517293 < baseStart_7517293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517299 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 4, 7, 2]
def baseStart_7517299 : Nat := 118140960795 + 7517299 * 2 ^ 59
def prefixEnd_7517299 : Nat := 4983230072969 + 3 ^ 40 * 7517299 * 2
def baseEnd_7517299 : Nat := 3859987610562889266791077

theorem tailTrace_7517299 : CollatzResearch.WordTrace tailWord_7517299 prefixEnd_7517299 3859987610562889266791077 := by
  unfold tailWord_7517299
  simp only [CollatzResearch.WordTrace]
  refine ⟨274178419193117050301594951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182785612795411366867729967 274178419193117050301594951)
  ·
    refine ⟨411267628789675575452392427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274178419193117050301594951 411267628789675575452392427)
    ·
      refine ⟨616901443184513363178588641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411267628789675575452392427 616901443184513363178588641)
      ·
        refine ⟨462676082388385022383941481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616901443184513363178588641 462676082388385022383941481)
        ·
          refine ⟨347007061791288766787956111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462676082388385022383941481 347007061791288766787956111)
          ·
            refine ⟨520510592686933150181934167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347007061791288766787956111 520510592686933150181934167)
            ·
              refine ⟨780765889030399725272901251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520510592686933150181934167 780765889030399725272901251)
              ·
                refine ⟨1171148833545599587909351877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780765889030399725272901251 1171148833545599587909351877)
                ·
                  refine ⟨219590406289799922733003477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1171148833545599587909351877 219590406289799922733003477)
                  ·
                    refine ⟨5146650147417185689054769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 219590406289799922733003477 5146650147417185689054769)
                    ·
                      refine ⟨3859987610562889266791077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5146650147417185689054769 3859987610562889266791077)
                      ·
                        rfl

theorem cell23_7517299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 7, 2].length) (baseStart_7517299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517299 prefixEnd_7517299 := by exact prefixLift 7517299
  have htrace : WordTrace (prefixWord ++ tailWord_7517299) baseStart_7517299 baseEnd_7517299 := by
    simpa [prefixWord, tailWord_7517299, baseEnd_7517299] using wordTrace_append hprefix tailTrace_7517299
  have hstable : (prefixWord ++ tailWord_7517299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517299).length < 2 ^ (prefixWord ++ tailWord_7517299).sum := by decide
  have hdescent : baseEnd_7517299 < baseStart_7517299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517340 : List Nat := [2, 2, 3, 2, 1, 2, 4, 1, 2, 1, 3]
def baseStart_7517340 : Nat := 118140960795 + 7517340 * 2 ^ 59
def prefixEnd_7517340 : Nat := 4983230072969 + 3 ^ 40 * 7517340 * 2
def baseEnd_7517340 : Nat := 3860008663269723606378389

theorem tailTrace_7517340 : CollatzResearch.WordTrace tailWord_7517340 prefixEnd_7517340 3860008663269723606378389 := by
  unfold tailWord_7517340
  simp only [CollatzResearch.WordTrace]
  refine ⟨137089957292984257151918737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182786609723979009535891649 137089957292984257151918737)
  ·
    refine ⟨102817467969738192863939053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137089957292984257151918737 102817467969738192863939053)
    ·
      refine ⟨38556550488651822323977145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102817467969738192863939053 38556550488651822323977145)
      ·
        refine ⟨28917412866488866742982859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38556550488651822323977145 28917412866488866742982859)
        ·
          refine ⟨43376119299733300114474289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28917412866488866742982859 43376119299733300114474289)
          ·
            refine ⟨32532089474799975085855717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43376119299733300114474289 32532089474799975085855717)
            ·
              refine ⟨6099766776524995328597947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32532089474799975085855717 6099766776524995328597947)
              ·
                refine ⟨9149650164787492992896921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6099766776524995328597947 9149650164787492992896921)
                ·
                  refine ⟨6862237623590619744672691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9149650164787492992896921 6862237623590619744672691)
                  ·
                    refine ⟨10293356435385929617009037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6862237623590619744672691 10293356435385929617009037)
                    ·
                      refine ⟨3860008663269723606378389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10293356435385929617009037 3860008663269723606378389)
                      ·
                        rfl

theorem cell23_7517340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_7517340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517340 prefixEnd_7517340 := by exact prefixLift 7517340
  have htrace : WordTrace (prefixWord ++ tailWord_7517340) baseStart_7517340 baseEnd_7517340 := by
    simpa [prefixWord, tailWord_7517340, baseEnd_7517340] using wordTrace_append hprefix tailTrace_7517340
  have hstable : (prefixWord ++ tailWord_7517340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517340).length < 2 ^ (prefixWord ++ tailWord_7517340).sum := by decide
  have hdescent : baseEnd_7517340 < baseStart_7517340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517349 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 2, 1, 5]
def baseStart_7517349 : Nat := 118140960795 + 7517349 * 2 ^ 59
def prefixEnd_7517349 : Nat := 4983230072969 + 3 ^ 40 * 7517349 * 2
def baseEnd_7517349 : Nat := 3860013284595614071165847

theorem tailTrace_7517349 : CollatzResearch.WordTrace tailWord_7517349 prefixEnd_7517349 3860013284595614071165847 := by
  unfold tailWord_7517349
  simp only [CollatzResearch.WordTrace]
  refine ⟨274180242842935908840915101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182786828561957272560610067 274180242842935908840915101)
  ·
    refine ⟨102817591066100965815343163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274180242842935908840915101 102817591066100965815343163)
    ·
      refine ⟨154226386599151448723014745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102817591066100965815343163 154226386599151448723014745)
      ·
        refine ⟨115669789949363586542261059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154226386599151448723014745 115669789949363586542261059)
        ·
          refine ⟨173504684924045379813391589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115669789949363586542261059 173504684924045379813391589)
          ·
            refine ⟨32532128423258508715010923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173504684924045379813391589 32532128423258508715010923)
            ·
              refine ⟨48798192634887763072516385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32532128423258508715010923 48798192634887763072516385)
              ·
                refine ⟨36598644476165822304387289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48798192634887763072516385 36598644476165822304387289)
                ·
                  refine ⟨27448983357124366728290467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36598644476165822304387289 27448983357124366728290467)
                  ·
                    refine ⟨41173475035686550092435701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27448983357124366728290467 41173475035686550092435701)
                    ·
                      refine ⟨3860013284595614071165847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41173475035686550092435701 3860013284595614071165847)
                      ·
                        rfl

theorem cell23_7517349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_7517349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517349 prefixEnd_7517349 := by exact prefixLift 7517349
  have htrace : WordTrace (prefixWord ++ tailWord_7517349) baseStart_7517349 baseEnd_7517349 := by
    simpa [prefixWord, tailWord_7517349, baseEnd_7517349] using wordTrace_append hprefix tailTrace_7517349
  have hstable : (prefixWord ++ tailWord_7517349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517349).length < 2 ^ (prefixWord ++ tailWord_7517349).sum := by decide
  have hdescent : baseEnd_7517349 < baseStart_7517349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517399 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 4, 5]
def baseStart_7517399 : Nat := 118140960795 + 7517399 * 2 ^ 59
def prefixEnd_7517399 : Nat := 4983230072969 + 3 ^ 40 * 7517399 * 2
def baseEnd_7517399 : Nat := 1286679652876112958513539

theorem tailTrace_7517399 : CollatzResearch.WordTrace tailWord_7517399 prefixEnd_7517399 1286679652876112958513539 := by
  unfold tailWord_7517399
  simp only [CollatzResearch.WordTrace]
  refine ⟨274182066492754767380235251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182788044328503178253490167 274182066492754767380235251)
  ·
    refine ⟨411273099739132151070352877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274182066492754767380235251 411273099739132151070352877)
    ·
      refine ⟨154227412402174556651382329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411273099739132151070352877 154227412402174556651382329)
      ·
        refine ⟨115670559301630917488536747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154227412402174556651382329 115670559301630917488536747)
        ·
          refine ⟨173505838952446376232805121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115670559301630917488536747 173505838952446376232805121)
          ·
            refine ⟨130129379214334782174603841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173505838952446376232805121 130129379214334782174603841)
            ·
              refine ⟨97597034410751086630952881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130129379214334782174603841 97597034410751086630952881)
              ·
                refine ⟨73197775808063314973214661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97597034410751086630952881 73197775808063314973214661)
                ·
                  refine ⟨13724582964011871557477749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73197775808063314973214661 13724582964011871557477749)
                  ·
                    refine ⟨1286679652876112958513539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13724582964011871557477749 1286679652876112958513539)
                    ·
                      rfl

theorem cell23_7517399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_7517399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517399 prefixEnd_7517399 := by exact prefixLift 7517399
  have htrace : WordTrace (prefixWord ++ tailWord_7517399) baseStart_7517399 baseEnd_7517399 := by
    simpa [prefixWord, tailWord_7517399, baseEnd_7517399] using wordTrace_append hprefix tailTrace_7517399
  have hstable : (prefixWord ++ tailWord_7517399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517399).length < 2 ^ (prefixWord ++ tailWord_7517399).sum := by decide
  have hdescent : baseEnd_7517399 < baseStart_7517399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517449 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 2, 1, 6]
def baseStart_7517449 : Nat := 118140960795 + 7517449 * 2 ^ 59
def prefixEnd_7517449 : Nat := 4983230072969 + 3 ^ 40 * 7517449 * 2
def baseEnd_7517449 : Nat := 3860064632661063679915387

theorem tailTrace_7517449 : CollatzResearch.WordTrace tailWord_7517449 prefixEnd_7517449 3860064632661063679915387 := by
  unfold tailWord_7517449
  simp only [CollatzResearch.WordTrace]
  refine ⟨274183890142573625919555401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182789260095049083946370267 274183890142573625919555401)
  ·
    refine ⟨205637917606930219439666551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274183890142573625919555401 205637917606930219439666551)
    ·
      refine ⟨308456876410395329159499827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205637917606930219439666551 308456876410395329159499827)
      ·
        refine ⟨462685314615592993739249741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308456876410395329159499827 462685314615592993739249741)
        ·
          refine ⟨173506992980847372652218653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 462685314615592993739249741 173506992980847372652218653)
          ·
            refine ⟨65065122367817764744581995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173506992980847372652218653 65065122367817764744581995)
            ·
              refine ⟨97597683551726647116872993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65065122367817764744581995 97597683551726647116872993)
              ·
                refine ⟨73198262663794985337654745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97597683551726647116872993 73198262663794985337654745)
                ·
                  refine ⟨54898696997846239003241059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73198262663794985337654745 54898696997846239003241059)
                  ·
                    refine ⟨82348045496769358504861589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54898696997846239003241059 82348045496769358504861589)
                    ·
                      refine ⟨3860064632661063679915387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82348045496769358504861589 3860064632661063679915387)
                      ·
                        rfl

theorem cell23_7517449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_7517449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517449 prefixEnd_7517449 := by exact prefixLift 7517449
  have htrace : WordTrace (prefixWord ++ tailWord_7517449) baseStart_7517449 baseEnd_7517449 := by
    simpa [prefixWord, tailWord_7517449, baseEnd_7517449] using wordTrace_append hprefix tailTrace_7517449
  have hstable : (prefixWord ++ tailWord_7517449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517449).length < 2 ^ (prefixWord ++ tailWord_7517449).sum := by decide
  have hdescent : baseEnd_7517449 < baseStart_7517449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517497 : List Nat := [1, 2, 1, 6, 3, 1, 1, 1, 3, 4]
def baseStart_7517497 : Nat := 118140960795 + 7517497 * 2 ^ 59
def prefixEnd_7517497 : Nat := 4983230072969 + 3 ^ 40 * 7517497 * 2
def baseEnd_7517497 : Nat := 1286696426577493164038389

theorem tailTrace_7517497 : CollatzResearch.WordTrace tailWord_7517497 prefixEnd_7517497 1286696426577493164038389 := by
  unfold tailWord_7517497
  simp only [CollatzResearch.WordTrace]
  refine ⟨274185640846399730117302745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182790427230933153411535163 274185640846399730117302745)
  ·
    refine ⟨205639230634799797587977059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274185640846399730117302745 205639230634799797587977059)
    ·
      refine ⟨308458845952199696381965589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205639230634799797587977059 308458845952199696381965589)
      ·
        refine ⟨14459008404009360767904637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 308458845952199696381965589 14459008404009360767904637)
        ·
          refine ⟨5422128151503510287964239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14459008404009360767904637 5422128151503510287964239)
          ·
            refine ⟨8133192227255265431946359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5422128151503510287964239 8133192227255265431946359)
            ·
              refine ⟨12199788340882898147919539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8133192227255265431946359 12199788340882898147919539)
              ·
                refine ⟨18299682511324347221879309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12199788340882898147919539 18299682511324347221879309)
                ·
                  refine ⟨6862380941746630208204741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18299682511324347221879309 6862380941746630208204741)
                  ·
                    refine ⟨1286696426577493164038389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6862380941746630208204741 1286696426577493164038389)
                    ·
                      rfl

theorem cell23_7517497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 3, 4].length) (baseStart_7517497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517497 prefixEnd_7517497 := by exact prefixLift 7517497
  have htrace : WordTrace (prefixWord ++ tailWord_7517497) baseStart_7517497 baseEnd_7517497 := by
    simpa [prefixWord, tailWord_7517497, baseEnd_7517497] using wordTrace_append hprefix tailTrace_7517497
  have hstable : (prefixWord ++ tailWord_7517497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517497).length < 2 ^ (prefixWord ++ tailWord_7517497).sum := by decide
  have hdescent : baseEnd_7517497 < baseStart_7517497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517536 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 3, 6]
def baseStart_7517536 : Nat := 118140960795 + 7517536 * 2 ^ 59
def prefixEnd_7517536 : Nat := 4983230072969 + 3 ^ 40 * 7517536 * 2
def baseEnd_7517536 : Nat := 1286703101826001613175829

theorem tailTrace_7517536 : CollatzResearch.WordTrace tailWord_7517536 prefixEnd_7517536 1286703101826001613175829 := by
  unfold tailWord_7517536
  simp only [CollatzResearch.WordTrace]
  refine ⟨137093531646629219888986231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182791375528838959851981641 137093531646629219888986231)
  ·
    refine ⟨205640297469943829833479347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137093531646629219888986231 205640297469943829833479347)
    ·
      refine ⟨308460446204915744750219021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205640297469943829833479347 308460446204915744750219021)
      ·
        refine ⟨115672667326843404281332133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308460446204915744750219021 115672667326843404281332133)
        ·
          refine ⟨21688625123783138302749775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115672667326843404281332133 21688625123783138302749775)
          ·
            refine ⟨32532937685674707454124663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21688625123783138302749775 32532937685674707454124663)
            ·
              refine ⟨48799406528512061181186995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32532937685674707454124663 48799406528512061181186995)
              ·
                refine ⟨73199109792768091771780493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48799406528512061181186995 73199109792768091771780493)
                ·
                  refine ⟨27449666172288034414417685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73199109792768091771780493 27449666172288034414417685)
                  ·
                    refine ⟨1286703101826001613175829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27449666172288034414417685 1286703101826001613175829)
                    ·
                      rfl

theorem cell23_7517536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 3, 6].length) (baseStart_7517536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517536 prefixEnd_7517536 := by exact prefixLift 7517536
  have htrace : WordTrace (prefixWord ++ tailWord_7517536) baseStart_7517536 baseEnd_7517536 := by
    simpa [prefixWord, tailWord_7517536, baseEnd_7517536] using wordTrace_append hprefix tailTrace_7517536
  have hstable : (prefixWord ++ tailWord_7517536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517536).length < 2 ^ (prefixWord ++ tailWord_7517536).sum := by decide
  have hdescent : baseEnd_7517536 < baseStart_7517536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517540 : List Nat := [2, 3, 1, 1, 3, 3, 3, 1, 1, 5]
def baseStart_7517540 : Nat := 118140960795 + 7517540 * 2 ^ 59
def prefixEnd_7517540 : Nat := 4983230072969 + 3 ^ 40 * 7517540 * 2
def baseEnd_7517540 : Nat := 1286703786466874274625823

theorem tailTrace_7517540 : CollatzResearch.WordTrace tailWord_7517540 prefixEnd_7517540 1286703786466874274625823 := by
  unfold tailWord_7517540
  simp only [CollatzResearch.WordTrace]
  refine ⟨137093604592621974230559037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182791472790162632307412049 137093604592621974230559037)
  ·
    refine ⟨51410101722233240336459639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137093604592621974230559037 51410101722233240336459639)
    ·
      refine ⟨77115152583349860504689459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51410101722233240336459639 77115152583349860504689459)
      ·
        refine ⟨115672728875024790757034189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77115152583349860504689459 115672728875024790757034189)
        ·
          refine ⟨43377273328134296533887821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115672728875024790757034189 43377273328134296533887821)
          ·
            refine ⟨16266477498050361200207933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43377273328134296533887821 16266477498050361200207933)
            ·
              refine ⟨6099929061768885450077975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16266477498050361200207933 6099929061768885450077975)
              ·
                refine ⟨9149893592653328175116963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6099929061768885450077975 9149893592653328175116963)
                ·
                  refine ⟨13724840388979992262675445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9149893592653328175116963 13724840388979992262675445)
                  ·
                    refine ⟨1286703786466874274625823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13724840388979992262675445 1286703786466874274625823)
                    ·
                      rfl

theorem cell23_7517540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_7517540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517540 prefixEnd_7517540 := by exact prefixLift 7517540
  have htrace : WordTrace (prefixWord ++ tailWord_7517540) baseStart_7517540 baseEnd_7517540 := by
    simpa [prefixWord, tailWord_7517540, baseEnd_7517540] using wordTrace_append hprefix tailTrace_7517540
  have hstable : (prefixWord ++ tailWord_7517540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517540).length < 2 ^ (prefixWord ++ tailWord_7517540).sum := by decide
  have hdescent : baseEnd_7517540 < baseStart_7517540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517553 : List Nat := [1, 2, 2, 2, 1, 2, 3, 4, 2, 4]
def baseStart_7517553 : Nat := 118140960795 + 7517553 * 2 ^ 59
def prefixEnd_7517553 : Nat := 4983230072969 + 3 ^ 40 * 7517553 * 2
def baseEnd_7517553 : Nat := 1286706011549710424338303

theorem tailTrace_7517553 : CollatzResearch.WordTrace tailWord_7517553 prefixEnd_7517553 1286706011549710424338303 := by
  unfold tailWord_7517553
  simp only [CollatzResearch.WordTrace]
  refine ⟨274187683334196851681341313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182791788889464567787560875 274187683334196851681341313)
  ·
    refine ⟨205640762500647638761005985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274187683334196851681341313 205640762500647638761005985)
    ·
      refine ⟨154230571875485729070754489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205640762500647638761005985 154230571875485729070754489)
      ·
        refine ⟨115672928906614296803065867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154230571875485729070754489 115672928906614296803065867)
        ·
          refine ⟨173509393359921445204598801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115672928906614296803065867 173509393359921445204598801)
          ·
            refine ⟨130132045019941083903449101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173509393359921445204598801 130132045019941083903449101)
            ·
              refine ⟨48799516882477906463793413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130132045019941083903449101 48799516882477906463793413)
              ·
                refine ⟨9149909415464607461961265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48799516882477906463793413 9149909415464607461961265)
                ·
                  refine ⟨6862432061598455596470949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9149909415464607461961265 6862432061598455596470949)
                  ·
                    refine ⟨1286706011549710424338303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6862432061598455596470949 1286706011549710424338303)
                    ·
                      rfl

theorem cell23_7517553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 4].length) (baseStart_7517553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517553 prefixEnd_7517553 := by exact prefixLift 7517553
  have htrace : WordTrace (prefixWord ++ tailWord_7517553) baseStart_7517553 baseEnd_7517553 := by
    simpa [prefixWord, tailWord_7517553, baseEnd_7517553] using wordTrace_append hprefix tailTrace_7517553
  have hstable : (prefixWord ++ tailWord_7517553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517553).length < 2 ^ (prefixWord ++ tailWord_7517553).sum := by decide
  have hdescent : baseEnd_7517553 < baseStart_7517553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517570 : List Nat := [3, 4, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_7517570 : Nat := 118140960795 + 7517570 * 2 ^ 59
def prefixEnd_7517570 : Nat := 4983230072969 + 3 ^ 40 * 7517570 * 2
def baseEnd_7517570 : Nat := 1286708921273419235500777

theorem tailTrace_7517570 : CollatzResearch.WordTrace tailWord_7517570 prefixEnd_7517570 1286708921273419235500777 := by
  unfold tailWord_7517570
  simp only [CollatzResearch.WordTrace]
  refine ⟨68547075843783815896177541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182792202250090175723140109 68547075843783815896177541)
  ·
    refine ⟨12852576720709465480533289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68547075843783815896177541 12852576720709465480533289)
    ·
      refine ⟨9639432540532099110399967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12852576720709465480533289 9639432540532099110399967)
      ·
        refine ⟨14459148810798148665599951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9639432540532099110399967 14459148810798148665599951)
        ·
          refine ⟨21688723216197222998399927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14459148810798148665599951 21688723216197222998399927)
          ·
            refine ⟨32533084824295834497599891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21688723216197222998399927 32533084824295834497599891)
            ·
              refine ⟨48799627236443751746399837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32533084824295834497599891 48799627236443751746399837)
              ·
                refine ⟨18299860213666406904899939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48799627236443751746399837 18299860213666406904899939)
                ·
                  refine ⟨27449790320499610357349909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18299860213666406904899939 27449790320499610357349909)
                  ·
                    refine ⟨1286708921273419235500777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27449790320499610357349909 1286708921273419235500777)
                    ·
                      rfl

theorem cell23_7517570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_7517570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517570 prefixEnd_7517570 := by exact prefixLift 7517570
  have htrace : WordTrace (prefixWord ++ tailWord_7517570) baseStart_7517570 baseEnd_7517570 := by
    simpa [prefixWord, tailWord_7517570, baseEnd_7517570] using wordTrace_append hprefix tailTrace_7517570
  have hstable : (prefixWord ++ tailWord_7517570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517570).length < 2 ^ (prefixWord ++ tailWord_7517570).sum := by decide
  have hdescent : baseEnd_7517570 < baseStart_7517570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517577 : List Nat := [1, 2, 1, 1, 7, 1, 1, 2, 3, 2, 2]
def baseStart_7517577 : Nat := 118140960795 + 7517577 * 2 ^ 59
def prefixEnd_7517577 : Nat := 4983230072969 + 3 ^ 40 * 7517577 * 2
def baseEnd_7517577 : Nat := 3860130358184839179114799

theorem tailTrace_7517577 : CollatzResearch.WordTrace tailWord_7517577 prefixEnd_7517577 3860130358184839179114799 := by
  unfold tailWord_7517577
  simp only [CollatzResearch.WordTrace]
  refine ⟨274188558686109903780214985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182792372457406602520143323 274188558686109903780214985)
  ·
    refine ⟨205641419014582427835161239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274188558686109903780214985 205641419014582427835161239)
    ·
      refine ⟨308462128521873641752741859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205641419014582427835161239 308462128521873641752741859)
      ·
        refine ⟨462693192782810462629112789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308462128521873641752741859 462693192782810462629112789)
        ·
          refine ⟨10844371705847120217869831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 462693192782810462629112789 10844371705847120217869831)
          ·
            refine ⟨16266557558770680326804747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10844371705847120217869831 16266557558770680326804747)
            ·
              refine ⟨24399836338156020490207121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16266557558770680326804747 24399836338156020490207121)
              ·
                refine ⟨18299877253617015367655341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24399836338156020490207121 18299877253617015367655341)
                ·
                  refine ⟨6862453970106380762870753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18299877253617015367655341 6862453970106380762870753)
                  ·
                    refine ⟨5146840477579785572153065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6862453970106380762870753 5146840477579785572153065)
                    ·
                      refine ⟨3860130358184839179114799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5146840477579785572153065 3860130358184839179114799)
                      ·
                        rfl

theorem cell23_7517577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 2, 2].length) (baseStart_7517577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517577 prefixEnd_7517577 := by exact prefixLift 7517577
  have htrace : WordTrace (prefixWord ++ tailWord_7517577) baseStart_7517577 baseEnd_7517577 := by
    simpa [prefixWord, tailWord_7517577, baseEnd_7517577] using wordTrace_append hprefix tailTrace_7517577
  have hstable : (prefixWord ++ tailWord_7517577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517577).length < 2 ^ (prefixWord ++ tailWord_7517577).sum := by decide
  have hdescent : baseEnd_7517577 < baseStart_7517577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517593 : List Nat := [1, 2, 1, 2, 1, 5, 2, 2, 1, 3, 3]
def baseStart_7517593 : Nat := 118140960795 + 7517593 * 2 ^ 59
def prefixEnd_7517593 : Nat := 4983230072969 + 3 ^ 40 * 7517593 * 2
def baseEnd_7517593 : Nat := 3860138573875311116514725

theorem tailTrace_7517593 : CollatzResearch.WordTrace tailWord_7517593 prefixEnd_7517593 3860138573875311116514725 := by
  unfold tailWord_7517593
  simp only [CollatzResearch.WordTrace]
  refine ⟨274189142254051938512797433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182792761502701292341864955 274189142254051938512797433)
  ·
    refine ⟨205641856690538953884598075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274189142254051938512797433 205641856690538953884598075)
    ·
      refine ⟨308462785035808430826897113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205641856690538953884598075 308462785035808430826897113)
      ·
        refine ⟨231347088776856323120172835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308462785035808430826897113 231347088776856323120172835)
        ·
          refine ⟨347020633165284484680259253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231347088776856323120172835 347020633165284484680259253)
          ·
            refine ⟨32533184359245420438774305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 347020633165284484680259253 32533184359245420438774305)
            ·
              refine ⟨24399888269434065329080729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32533184359245420438774305 24399888269434065329080729)
              ·
                refine ⟨18299916202075548996810547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24399888269434065329080729 18299916202075548996810547)
                ·
                  refine ⟨27449874303113323495215821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18299916202075548996810547 27449874303113323495215821)
                  ·
                    refine ⟨10293702863667496310705933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27449874303113323495215821 10293702863667496310705933)
                    ·
                      refine ⟨3860138573875311116514725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10293702863667496310705933 3860138573875311116514725)
                      ·
                        rfl

theorem cell23_7517593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 3, 3].length) (baseStart_7517593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517593 prefixEnd_7517593 := by exact prefixLift 7517593
  have htrace : WordTrace (prefixWord ++ tailWord_7517593) baseStart_7517593 baseEnd_7517593 := by
    simpa [prefixWord, tailWord_7517593, baseEnd_7517593] using wordTrace_append hprefix tailTrace_7517593
  have hstable : (prefixWord ++ tailWord_7517593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517593).length < 2 ^ (prefixWord ++ tailWord_7517593).sum := by decide
  have hdescent : baseEnd_7517593 < baseStart_7517593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517594 : List Nat := [3, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2]
def baseStart_7517594 : Nat := 118140960795 + 7517594 * 2 ^ 59
def prefixEnd_7517594 : Nat := 4983230072969 + 3 ^ 40 * 7517594 * 2
def baseEnd_7517594 : Nat := 3860139087355965612602221

theorem tailTrace_7517594 : CollatzResearch.WordTrace tailWord_7517594 prefixEnd_7517594 3860139087355965612602221 := by
  unfold tailWord_7517594
  simp only [CollatzResearch.WordTrace]
  refine ⟨68547294681762078920895959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182792785818032210455722557 68547294681762078920895959)
  ·
    refine ⟨102820942022643118381343939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68547294681762078920895959 102820942022643118381343939)
    ·
      refine ⟨154231413033964677572015909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102820942022643118381343939 154231413033964677572015909)
      ·
        refine ⟨28918389943868377044752983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154231413033964677572015909 28918389943868377044752983)
        ·
          refine ⟨43377584915802565567129475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28918389943868377044752983 43377584915802565567129475)
          ·
            refine ⟨65066377373703848350694213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43377584915802565567129475 65066377373703848350694213)
            ·
              refine ⟨12199945757569471565755165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65066377373703848350694213 12199945757569471565755165)
              ·
                refine ⟨4574979659088551837158187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12199945757569471565755165 4574979659088551837158187)
                ·
                  refine ⟨6862469488632827755737281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4574979659088551837158187 6862469488632827755737281)
                  ·
                    refine ⟨5146852116474620816802961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6862469488632827755737281 5146852116474620816802961)
                    ·
                      refine ⟨3860139087355965612602221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5146852116474620816802961 3860139087355965612602221)
                      ·
                        rfl

theorem cell23_7517594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_7517594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517594 prefixEnd_7517594 := by exact prefixLift 7517594
  have htrace : WordTrace (prefixWord ++ tailWord_7517594) baseStart_7517594 baseEnd_7517594 := by
    simpa [prefixWord, tailWord_7517594, baseEnd_7517594] using wordTrace_append hprefix tailTrace_7517594
  have hstable : (prefixWord ++ tailWord_7517594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517594).length < 2 ^ (prefixWord ++ tailWord_7517594).sum := by decide
  have hdescent : baseEnd_7517594 < baseStart_7517594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517597 : List Nat := [1, 4, 2, 1, 3, 1, 4, 1, 1, 2, 3]
def baseStart_7517597 : Nat := 118140960795 + 7517597 * 2 ^ 59
def prefixEnd_7517597 : Nat := 4983230072969 + 3 ^ 40 * 7517597 * 2
def baseEnd_7517597 : Nat := 3860140627797929100864707

theorem tailTrace_7517597 : CollatzResearch.WordTrace tailWord_7517597 prefixEnd_7517597 3860140627797929100864707 := by
  unfold tailWord_7517597
  simp only [CollatzResearch.WordTrace]
  refine ⟨274189288146037447195943045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182792858764024964797295363 274189288146037447195943045)
  ·
    refine ⟨51410491527382021349239321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274189288146037447195943045 51410491527382021349239321)
    ·
      refine ⟨38557868645536516011929491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51410491527382021349239321 38557868645536516011929491)
      ·
        refine ⟨57836802968304774017894237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38557868645536516011929491 57836802968304774017894237)
        ·
          refine ⟨21688801113114290256710339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57836802968304774017894237 21688801113114290256710339)
          ·
            refine ⟨32533201669671435385065509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21688801113114290256710339 32533201669671435385065509)
            ·
              refine ⟨6099975313063394134699783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32533201669671435385065509 6099975313063394134699783)
              ·
                refine ⟨9149962969595091202049675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6099975313063394134699783 9149962969595091202049675)
                ·
                  refine ⟨13724944454392636803074513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9149962969595091202049675 13724944454392636803074513)
                  ·
                    refine ⟨10293708340794477602305885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13724944454392636803074513 10293708340794477602305885)
                    ·
                      refine ⟨3860140627797929100864707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10293708340794477602305885 3860140627797929100864707)
                      ·
                        rfl

theorem cell23_7517597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_7517597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517597 prefixEnd_7517597 := by exact prefixLift 7517597
  have htrace : WordTrace (prefixWord ++ tailWord_7517597) baseStart_7517597 baseEnd_7517597 := by
    simpa [prefixWord, tailWord_7517597, baseEnd_7517597] using wordTrace_append hprefix tailTrace_7517597
  have hstable : (prefixWord ++ tailWord_7517597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517597).length < 2 ^ (prefixWord ++ tailWord_7517597).sum := by decide
  have hdescent : baseEnd_7517597 < baseStart_7517597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517616 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 4]
def baseStart_7517616 : Nat := 118140960795 + 7517616 * 2 ^ 59
def prefixEnd_7517616 : Nat := 4983230072969 + 3 ^ 40 * 7517616 * 2
def baseEnd_7517616 : Nat := 3860150383930364526527119

theorem tailTrace_7517616 : CollatzResearch.WordTrace tailWord_7517616 prefixEnd_7517616 3860150383930364526527119 := by
  unfold tailWord_7517616
  simp only [CollatzResearch.WordTrace]
  refine ⟨137094990566484306720442351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182793320755312408960589801 137094990566484306720442351)
  ·
    refine ⟨205642485849726460080663527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137094990566484306720442351 205642485849726460080663527)
    ·
      refine ⟨308463728774589690120995291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205642485849726460080663527 308463728774589690120995291)
      ·
        refine ⟨462695593161884535181492937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308463728774589690120995291 462695593161884535181492937)
        ·
          refine ⟨347021694871413401386119703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462695593161884535181492937 347021694871413401386119703)
          ·
            refine ⟨520532542307120102079179555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347021694871413401386119703 520532542307120102079179555)
            ·
              refine ⟨780798813460680153118769333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520532542307120102079179555 780798813460680153118769333)
              ·
                refine ⟨73199888761938764354884625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 780798813460680153118769333 73199888761938764354884625)
                ·
                  refine ⟨54899916571454073266163469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73199888761938764354884625 54899916571454073266163469)
                  ·
                    refine ⟨20587468714295277474811301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54899916571454073266163469 20587468714295277474811301)
                    ·
                      refine ⟨3860150383930364526527119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20587468714295277474811301 3860150383930364526527119)
                      ·
                        rfl

theorem cell23_7517616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 4].length) (baseStart_7517616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517616 prefixEnd_7517616 := by exact prefixLift 7517616
  have htrace : WordTrace (prefixWord ++ tailWord_7517616) baseStart_7517616 baseEnd_7517616 := by
    simpa [prefixWord, tailWord_7517616, baseEnd_7517616] using wordTrace_append hprefix tailTrace_7517616
  have hstable : (prefixWord ++ tailWord_7517616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517616).length < 2 ^ (prefixWord ++ tailWord_7517616).sum := by decide
  have hdescent : baseEnd_7517616 < baseStart_7517616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517634 : List Nat := [3, 5, 2, 1, 1, 1, 1, 9]
def baseStart_7517634 : Nat := 118140960795 + 7517634 * 2 ^ 59
def prefixEnd_7517634 : Nat := 4983230072969 + 3 ^ 40 * 7517634 * 2
def baseEnd_7517634 : Nat := 142968875058597979855631

theorem tailTrace_7517634 : CollatzResearch.WordTrace tailWord_7517634 prefixEnd_7517634 142968875058597979855631 := by
  unfold tailWord_7517634
  simp only [CollatzResearch.WordTrace]
  refine ⟨68547659411725850628759989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182793758431268935010026637 68547659411725850628759989)
  ·
    refine ⟨6426343069849298496446249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68547659411725850628759989 6426343069849298496446249)
    ·
      refine ⟨4819757302386973872334687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6426343069849298496446249 4819757302386973872334687)
      ·
        refine ⟨7229635953580460808502031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4819757302386973872334687 7229635953580460808502031)
        ·
          refine ⟨10844453930370691212753047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7229635953580460808502031 10844453930370691212753047)
          ·
            refine ⟨16266680895556036819129571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10844453930370691212753047 16266680895556036819129571)
            ·
              refine ⟨24400021343334055228694357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16266680895556036819129571 24400021343334055228694357)
              ·
                refine ⟨142968875058597979855631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24400021343334055228694357 142968875058597979855631)
                ·
                  rfl

theorem cell23_7517634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 9].length) (baseStart_7517634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517634 prefixEnd_7517634 := by exact prefixLift 7517634
  have htrace : WordTrace (prefixWord ++ tailWord_7517634) baseStart_7517634 baseEnd_7517634 := by
    simpa [prefixWord, tailWord_7517634, baseEnd_7517634] using wordTrace_append hprefix tailTrace_7517634
  have hstable : (prefixWord ++ tailWord_7517634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517634).length < 2 ^ (prefixWord ++ tailWord_7517634).sum := by decide
  have hdescent : baseEnd_7517634 < baseStart_7517634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517653 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 2, 1, 5]
def baseStart_7517653 : Nat := 118140960795 + 7517653 * 2 ^ 59
def prefixEnd_7517653 : Nat := 4983230072969 + 3 ^ 40 * 7517653 * 2
def baseEnd_7517653 : Nat := 3860169382714580881764449

theorem tailTrace_7517653 : CollatzResearch.WordTrace tailWord_7517653 prefixEnd_7517653 3860169382714580881764449 := by
  unfold tailWord_7517653
  simp only [CollatzResearch.WordTrace]
  refine ⟨274191330633834568759981613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182794220422556379173321075 274191330633834568759981613)
  ·
    refine ⟨102821748987687963284993105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274191330633834568759981613 102821748987687963284993105)
    ·
      refine ⟨77116311740765972463744829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102821748987687963284993105 77116311740765972463744829)
      ·
        refine ⟨28918616902787239673904311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77116311740765972463744829 28918616902787239673904311)
        ·
          refine ⟨43377925354180859510856467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28918616902787239673904311 43377925354180859510856467)
          ·
            refine ⟨65066888031271289266284701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43377925354180859510856467 65066888031271289266284701)
            ·
              refine ⟨24400083011726733474856763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65066888031271289266284701 24400083011726733474856763)
              ·
                refine ⟨36600124517590100212285145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24400083011726733474856763 36600124517590100212285145)
                ·
                  refine ⟨27450093388192575159213859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36600124517590100212285145 27450093388192575159213859)
                  ·
                    refine ⟨41175140082288862738820789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27450093388192575159213859 41175140082288862738820789)
                    ·
                      refine ⟨3860169382714580881764449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41175140082288862738820789 3860169382714580881764449)
                      ·
                        rfl

theorem cell23_7517653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_7517653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517653 prefixEnd_7517653 := by exact prefixLift 7517653
  have htrace : WordTrace (prefixWord ++ tailWord_7517653) baseStart_7517653 baseEnd_7517653 := by
    simpa [prefixWord, tailWord_7517653, baseEnd_7517653] using wordTrace_append hprefix tailTrace_7517653
  have hstable : (prefixWord ++ tailWord_7517653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517653).length < 2 ^ (prefixWord ++ tailWord_7517653).sum := by decide
  have hdescent : baseEnd_7517653 < baseStart_7517653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517654 : List Nat := [5, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2]
def baseStart_7517654 : Nat := 118140960795 + 7517654 * 2 ^ 59
def prefixEnd_7517654 : Nat := 4983230072969 + 3 ^ 40 * 7517654 * 2
def baseEnd_7517654 : Nat := 3860169896195235377851945

theorem tailTrace_7517654 : CollatzResearch.WordTrace tailWord_7517654 prefixEnd_7517654 3860169896195235377851945 := by
  unfold tailWord_7517654
  simp only [CollatzResearch.WordTrace]
  refine ⟨17136960444176934120673001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182794244737887297287178677 17136960444176934120673001)
  ·
    refine ⟨12852720333132700590504751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17136960444176934120673001 12852720333132700590504751)
    ·
      refine ⟨19279080499699050885757127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12852720333132700590504751 19279080499699050885757127)
      ·
        refine ⟨28918620749548576328635691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19279080499699050885757127 28918620749548576328635691)
        ·
          refine ⟨43377931124322864492953537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28918620749548576328635691 43377931124322864492953537)
          ·
            refine ⟨32533448343242148369715153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43377931124322864492953537 32533448343242148369715153)
            ·
              refine ⟨24400086257431611277286365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32533448343242148369715153 24400086257431611277286365)
              ·
                refine ⟨9150032346536854228982387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24400086257431611277286365 9150032346536854228982387)
                ·
                  refine ⟨13725048519805281343473581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9150032346536854228982387 13725048519805281343473581)
                  ·
                    refine ⟨5146893194926980503802593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13725048519805281343473581 5146893194926980503802593)
                    ·
                      refine ⟨3860169896195235377851945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5146893194926980503802593 3860169896195235377851945)
                      ·
                        rfl

theorem cell23_7517654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_7517654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517654 prefixEnd_7517654 := by exact prefixLift 7517654
  have htrace : WordTrace (prefixWord ++ tailWord_7517654) baseStart_7517654 baseEnd_7517654 := by
    simpa [prefixWord, tailWord_7517654, baseEnd_7517654] using wordTrace_append hprefix tailTrace_7517654
  have hstable : (prefixWord ++ tailWord_7517654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517654).length < 2 ^ (prefixWord ++ tailWord_7517654).sum := by decide
  have hdescent : baseEnd_7517654 < baseStart_7517654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517656 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 9]
def baseStart_7517656 : Nat := 118140960795 + 7517656 * 2 ^ 59
def prefixEnd_7517656 : Nat := 4983230072969 + 3 ^ 40 * 7517656 * 2
def baseEnd_7517656 : Nat := 428907880350727152225215

theorem tailTrace_7517656 : CollatzResearch.WordTrace tailWord_7517656 prefixEnd_7517656 428907880350727152225215 := by
  unfold tailWord_7517656
  simp only [CollatzResearch.WordTrace]
  refine ⟨137095720026411850136170411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182794293368549133514893881 137095720026411850136170411)
  ·
    refine ⟨205643580039617775204255617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137095720026411850136170411 205643580039617775204255617)
    ·
      refine ⟨154232685029713331403191713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205643580039617775204255617 154232685029713331403191713)
      ·
        refine ⟨115674513772284998552393785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154232685029713331403191713 115674513772284998552393785)
        ·
          refine ⟨86755885329213748914295339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115674513772284998552393785 86755885329213748914295339)
          ·
            refine ⟨130133827993820623371443009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86755885329213748914295339 130133827993820623371443009)
            ·
              refine ⟨97600370995365467528582257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130133827993820623371443009 97600370995365467528582257)
              ·
                refine ⟨73200278246524100646436693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97600370995365467528582257 73200278246524100646436693)
                ·
                  refine ⟨428907880350727152225215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73200278246524100646436693 428907880350727152225215)
                  ·
                    rfl

theorem cell23_7517656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 9].length) (baseStart_7517656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517656 prefixEnd_7517656 := by exact prefixLift 7517656
  have htrace : WordTrace (prefixWord ++ tailWord_7517656) baseStart_7517656 baseEnd_7517656 := by
    simpa [prefixWord, tailWord_7517656, baseEnd_7517656] using wordTrace_append hprefix tailTrace_7517656
  have hstable : (prefixWord ++ tailWord_7517656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517656).length < 2 ^ (prefixWord ++ tailWord_7517656).sum := by decide
  have hdescent : baseEnd_7517656 < baseStart_7517656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517667 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 4, 2, 2]
def baseStart_7517667 : Nat := 118140960795 + 7517667 * 2 ^ 59
def prefixEnd_7517667 : Nat := 4983230072969 + 3 ^ 40 * 7517667 * 2
def baseEnd_7517667 : Nat := 3860176571443743826989385

theorem tailTrace_7517667 : CollatzResearch.WordTrace tailWord_7517667 prefixEnd_7517667 3860176571443743826989385 := by
  unfold tailWord_7517667
  simp only [CollatzResearch.WordTrace]
  refine ⟨274191841255783849150991255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182794560837189232767327503 274191841255783849150991255)
  ·
    refine ⟨411287761883675773726486883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274191841255783849150991255 411287761883675773726486883)
    ·
      refine ⟨616931642825513660589730325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411287761883675773726486883 616931642825513660589730325)
      ·
        refine ⟨28918670757445952840143609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 616931642825513660589730325 28918670757445952840143609)
        ·
          refine ⟨21689003068084464630107707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28918670757445952840143609 21689003068084464630107707)
          ·
            refine ⟨32533504602126696945161561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21689003068084464630107707 32533504602126696945161561)
            ·
              refine ⟨24400128451595022708871171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32533504602126696945161561 24400128451595022708871171)
              ·
                refine ⟨36600192677392534063306757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24400128451595022708871171 36600192677392534063306757)
                ·
                  refine ⟨6862536127011100136870017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36600192677392534063306757 6862536127011100136870017)
                  ·
                    refine ⟨5146902095258325102652513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6862536127011100136870017 5146902095258325102652513)
                    ·
                      refine ⟨3860176571443743826989385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5146902095258325102652513 3860176571443743826989385)
                      ·
                        rfl

theorem cell23_7517667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_7517667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517667 prefixEnd_7517667 := by exact prefixLift 7517667
  have htrace : WordTrace (prefixWord ++ tailWord_7517667) baseStart_7517667 baseEnd_7517667 := by
    simpa [prefixWord, tailWord_7517667, baseEnd_7517667] using wordTrace_append hprefix tailTrace_7517667
  have hstable : (prefixWord ++ tailWord_7517667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517667).length < 2 ^ (prefixWord ++ tailWord_7517667).sum := by decide
  have hdescent : baseEnd_7517667 < baseStart_7517667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517676 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 8]
def baseStart_7517676 : Nat := 118140960795 + 7517676 * 2 ^ 59
def prefixEnd_7517676 : Nat := 4983230072969 + 3 ^ 40 * 7517676 * 2
def baseEnd_7517676 : Nat := 3860181192769634291776843

theorem tailTrace_7517676 : CollatzResearch.WordTrace tailWord_7517676 prefixEnd_7517676 3860181192769634291776843 := by
  unfold tailWord_7517676
  simp only [CollatzResearch.WordTrace]
  refine ⟨137096084756375621844034441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182794779675167495792045921 137096084756375621844034441)
  ·
    refine ⟨102822063567281716383025831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137096084756375621844034441 102822063567281716383025831)
    ·
      refine ⟨154233095350922574574538747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102822063567281716383025831 154233095350922574574538747)
      ·
        refine ⟨231349643026383861861808121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154233095350922574574538747 231349643026383861861808121)
        ·
          refine ⟨173512232269787896396356091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231349643026383861861808121 173512232269787896396356091)
          ·
            refine ⟨260268348404681844594534137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173512232269787896396356091 260268348404681844594534137)
            ·
              refine ⟨195201261303511383445900603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260268348404681844594534137 195201261303511383445900603)
              ·
                refine ⟨292801891955267075168850905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195201261303511383445900603 292801891955267075168850905)
                ·
                  refine ⟨219601418966450306376638179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292801891955267075168850905 219601418966450306376638179)
                  ·
                    refine ⟨329402128449675459564957269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 219601418966450306376638179 329402128449675459564957269)
                    ·
                      refine ⟨3860181192769634291776843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 329402128449675459564957269 3860181192769634291776843)
                      ·
                        rfl

theorem cell23_7517676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_7517676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517676 prefixEnd_7517676 := by exact prefixLift 7517676
  have htrace : WordTrace (prefixWord ++ tailWord_7517676) baseStart_7517676 baseEnd_7517676 := by
    simpa [prefixWord, tailWord_7517676, baseEnd_7517676] using wordTrace_append hprefix tailTrace_7517676
  have hstable : (prefixWord ++ tailWord_7517676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517676).length < 2 ^ (prefixWord ++ tailWord_7517676).sum := by decide
  have hdescent : baseEnd_7517676 < baseStart_7517676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517783 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 6]
def baseStart_7517783 : Nat := 118140960795 + 7517783 * 2 ^ 59
def prefixEnd_7517783 : Nat := 4983230072969 + 3 ^ 40 * 7517783 * 2
def baseEnd_7517783 : Nat := 3860236135199665373138851

theorem tailTrace_7517783 : CollatzResearch.WordTrace tailWord_7517783 prefixEnd_7517783 3860236135199665373138851 := by
  unfold tailWord_7517783
  simp only [CollatzResearch.WordTrace]
  refine ⟨274196072123363600962214003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182797381415575733974809335 274196072123363600962214003)
  ·
    refine ⟨411294108185045401443321005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274196072123363600962214003 411294108185045401443321005)
    ·
      refine ⟨154235290569392025541245377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 411294108185045401443321005 154235290569392025541245377)
      ·
        refine ⟨115676467927044019155934033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154235290569392025541245377 115676467927044019155934033)
        ·
          refine ⟨86757350945283014366950525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115676467927044019155934033 86757350945283014366950525)
          ·
            refine ⟨32534006604481130387606447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86757350945283014366950525 32534006604481130387606447)
            ·
              refine ⟨48801009906721695581409671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32534006604481130387606447 48801009906721695581409671)
              ·
                refine ⟨73201514860082543372114507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48801009906721695581409671 73201514860082543372114507)
                ·
                  refine ⟨109802272290123815058171761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73201514860082543372114507 109802272290123815058171761)
                  ·
                    refine ⟨82351704217592861293628821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109802272290123815058171761 82351704217592861293628821)
                    ·
                      refine ⟨3860236135199665373138851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82351704217592861293628821 3860236135199665373138851)
                      ·
                        rfl

theorem cell23_7517783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_7517783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517783 prefixEnd_7517783 := by exact prefixLift 7517783
  have htrace : WordTrace (prefixWord ++ tailWord_7517783) baseStart_7517783 baseEnd_7517783 := by
    simpa [prefixWord, tailWord_7517783, baseEnd_7517783] using wordTrace_append hprefix tailTrace_7517783
  have hstable : (prefixWord ++ tailWord_7517783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517783).length < 2 ^ (prefixWord ++ tailWord_7517783).sum := by decide
  have hdescent : baseEnd_7517783 < baseStart_7517783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517797 : List Nat := [1, 3, 1, 3, 3, 2, 3, 1, 6]
def baseStart_7517797 : Nat := 118140960795 + 7517797 * 2 ^ 59
def prefixEnd_7517797 : Nat := 4983230072969 + 3 ^ 40 * 7517797 * 2
def baseEnd_7517797 : Nat := 428915924880980924262643

theorem tailTrace_7517797 : CollatzResearch.WordTrace tailWord_7517797 prefixEnd_7517797 428915924880980924262643 := by
  unfold tailWord_7517797
  simp only [CollatzResearch.WordTrace]
  refine ⟨274196582745312881353223645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182797721830208587568815763 274196582745312881353223645)
  ·
    refine ⟨102823718529492330507458867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 274196582745312881353223645 102823718529492330507458867)
    ·
      refine ⟨154235577794238495761188301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102823718529492330507458867 154235577794238495761188301)
      ·
        refine ⟨57838341672839435910445613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154235577794238495761188301 57838341672839435910445613)
        ·
          refine ⟨21689378127314788466417105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57838341672839435910445613 21689378127314788466417105)
          ·
            refine ⟨16267033595486091349812829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21689378127314788466417105 16267033595486091349812829)
            ·
              refine ⟨6100137598307284256179811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16267033595486091349812829 6100137598307284256179811)
              ·
                refine ⟨9150206397460926384269717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6100137598307284256179811 9150206397460926384269717)
                ·
                  refine ⟨428915924880980924262643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9150206397460926384269717 428915924880980924262643)
                  ·
                    rfl

theorem cell23_7517797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 6].length) (baseStart_7517797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517797 prefixEnd_7517797 := by exact prefixLift 7517797
  have htrace : WordTrace (prefixWord ++ tailWord_7517797) baseStart_7517797 baseEnd_7517797 := by
    simpa [prefixWord, tailWord_7517797, baseEnd_7517797] using wordTrace_append hprefix tailTrace_7517797
  have hstable : (prefixWord ++ tailWord_7517797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517797).length < 2 ^ (prefixWord ++ tailWord_7517797).sum := by decide
  have hdescent : baseEnd_7517797 < baseStart_7517797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517817 : List Nat := [1, 2, 1, 3, 3, 1, 2, 3, 2, 3, 2]
def baseStart_7517817 : Nat := 118140960795 + 7517817 * 2 ^ 59
def prefixEnd_7517817 : Nat := 4983230072969 + 3 ^ 40 * 7517817 * 2
def baseEnd_7517817 : Nat := 3860253593541918240113695

theorem tailTrace_7517817 : CollatzResearch.WordTrace tailWord_7517817 prefixEnd_7517817 3860253593541918240113695 := by
  unfold tailWord_7517817
  simp only [CollatzResearch.WordTrace]
  refine ⟨274197312205240424768951705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182798208136826949845967803 274197312205240424768951705)
  ·
    refine ⟨205647984153930318576713779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274197312205240424768951705 205647984153930318576713779)
    ·
      refine ⟨308471976230895477865070669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205647984153930318576713779 308471976230895477865070669)
      ·
        refine ⟨115676991086585804199401501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308471976230895477865070669 115676991086585804199401501)
        ·
          refine ⟨43378871657469676574775563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115676991086585804199401501 43378871657469676574775563)
          ·
            refine ⟨65068307486204514862163345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43378871657469676574775563 65068307486204514862163345)
            ·
              refine ⟨48801230614653386146622509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65068307486204514862163345 48801230614653386146622509)
              ·
                refine ⟨18300461480495019804983441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48801230614653386146622509 18300461480495019804983441)
                ·
                  refine ⟨13725346110371264853737581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18300461480495019804983441 13725346110371264853737581)
                  ·
                    refine ⟨5147004791389224320151593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13725346110371264853737581 5147004791389224320151593)
                    ·
                      refine ⟨3860253593541918240113695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5147004791389224320151593 3860253593541918240113695)
                      ·
                        rfl

theorem cell23_7517817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_7517817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517817 prefixEnd_7517817 := by exact prefixLift 7517817
  have htrace : WordTrace (prefixWord ++ tailWord_7517817) baseStart_7517817 baseEnd_7517817 := by
    simpa [prefixWord, tailWord_7517817, baseEnd_7517817] using wordTrace_append hprefix tailTrace_7517817
  have hstable : (prefixWord ++ tailWord_7517817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517817).length < 2 ^ (prefixWord ++ tailWord_7517817).sum := by decide
  have hdescent : baseEnd_7517817 < baseStart_7517817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517834 : List Nat := [3, 1, 2, 3, 2, 2, 1, 2, 2, 3, 2]
def baseStart_7517834 : Nat := 118140960795 + 7517834 * 2 ^ 59
def prefixEnd_7517834 : Nat := 4983230072969 + 3 ^ 40 * 7517834 * 2
def baseEnd_7517834 : Nat := 3860262322713044673601117

theorem tailTrace_7517834 : CollatzResearch.WordTrace tailWord_7517834 prefixEnd_7517834 3860262322713044673601117 := by
  unfold tailWord_7517834
  simp only [CollatzResearch.WordTrace]
  refine ⟨68549483061544709168080139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182798621497452557781547037 68549483061544709168080139)
  ·
    refine ⟨102824224592317063752120209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68549483061544709168080139 102824224592317063752120209)
    ·
      refine ⟨77118168444237797814090157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102824224592317063752120209 77118168444237797814090157)
      ·
        refine ⟨28919313166589174180283809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77118168444237797814090157 28919313166589174180283809)
        ·
          refine ⟨21689484874941880635212857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28919313166589174180283809 21689484874941880635212857)
          ·
            refine ⟨16267113656206410476409643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21689484874941880635212857 16267113656206410476409643)
            ·
              refine ⟨24400670484309615714614465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16267113656206410476409643 24400670484309615714614465)
              ·
                refine ⟨18300502863232211785960849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24400670484309615714614465 18300502863232211785960849)
                ·
                  refine ⟨13725377147424158839470637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18300502863232211785960849 13725377147424158839470637)
                  ·
                    refine ⟨5147016430284059564801489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13725377147424158839470637 5147016430284059564801489)
                    ·
                      refine ⟨3860262322713044673601117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5147016430284059564801489 3860262322713044673601117)
                      ·
                        rfl

theorem cell23_7517834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_7517834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517834 prefixEnd_7517834 := by exact prefixLift 7517834
  have htrace : WordTrace (prefixWord ++ tailWord_7517834) baseStart_7517834 baseEnd_7517834 := by
    simpa [prefixWord, tailWord_7517834, baseEnd_7517834] using wordTrace_append hprefix tailTrace_7517834
  have hstable : (prefixWord ++ tailWord_7517834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517834).length < 2 ^ (prefixWord ++ tailWord_7517834).sum := by decide
  have hdescent : baseEnd_7517834 < baseStart_7517834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517843 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 4]
def baseStart_7517843 : Nat := 118140960795 + 7517843 * 2 ^ 59
def prefixEnd_7517843 : Nat := 4983230072969 + 3 ^ 40 * 7517843 * 2
def baseEnd_7517843 : Nat := 3860266944038935138388575

theorem tailTrace_7517843 : CollatzResearch.WordTrace tailWord_7517843 prefixEnd_7517843 3860266944038935138388575 := by
  unfold tailWord_7517843
  simp only [CollatzResearch.WordTrace]
  refine ⟨274198260503146231209398183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182798840335430820806265455 274198260503146231209398183)
  ·
    refine ⟨411297390754719346814097275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274198260503146231209398183 411297390754719346814097275)
    ·
      refine ⟨616946086132079020221145913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411297390754719346814097275 616946086132079020221145913)
      ·
        refine ⟨462709564599059265165859435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616946086132079020221145913 462709564599059265165859435)
        ·
          refine ⟨694064346898588897748789153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462709564599059265165859435 694064346898588897748789153)
          ·
            refine ⟨520548260173941673311591865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 694064346898588897748789153 520548260173941673311591865)
            ·
              refine ⟨390411195130456254983693899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520548260173941673311591865 390411195130456254983693899)
              ·
                refine ⟨585616792695684382475540849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390411195130456254983693899 585616792695684382475540849)
                ·
                  refine ⟨439212594521763286856655637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585616792695684382475540849 439212594521763286856655637)
                  ·
                    refine ⟨20588090368207654071405733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 439212594521763286856655637 20588090368207654071405733)
                    ·
                      refine ⟨3860266944038935138388575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20588090368207654071405733 3860266944038935138388575)
                      ·
                        rfl

theorem cell23_7517843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 4].length) (baseStart_7517843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517843 prefixEnd_7517843 := by exact prefixLift 7517843
  have htrace : WordTrace (prefixWord ++ tailWord_7517843) baseStart_7517843 baseEnd_7517843 := by
    simpa [prefixWord, tailWord_7517843, baseEnd_7517843] using wordTrace_append hprefix tailTrace_7517843
  have hstable : (prefixWord ++ tailWord_7517843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517843).length < 2 ^ (prefixWord ++ tailWord_7517843).sum := by decide
  have hdescent : baseEnd_7517843 < baseStart_7517843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517860 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 1, 1, 6]
def baseStart_7517860 : Nat := 118140960795 + 7517860 * 2 ^ 59
def prefixEnd_7517860 : Nat := 4983230072969 + 3 ^ 40 * 7517860 * 2
def baseEnd_7517860 : Nat := 3860275673210061571875997

theorem tailTrace_7517860 : CollatzResearch.WordTrace tailWord_7517860 prefixEnd_7517860 3860275673210061571875997 := by
  unfold tailWord_7517860
  simp only [CollatzResearch.WordTrace]
  refine ⟨137099440272042321556383517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182799253696056428741844689 137099440272042321556383517)
  ·
    refine ⟨51412290102015870583643819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137099440272042321556383517 51412290102015870583643819)
    ·
      refine ⟨77118435153023805875465729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51412290102015870583643819 77118435153023805875465729)
      ·
        refine ⟨57838826364767854406599297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77118435153023805875465729 57838826364767854406599297)
        ·
          refine ⟨43379119773575890804949473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57838826364767854406599297 43379119773575890804949473)
          ·
            refine ⟨32534339830181918103712105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43379119773575890804949473 32534339830181918103712105)
            ·
              refine ⟨24400754872636438577784079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32534339830181918103712105 24400754872636438577784079)
              ·
                refine ⟨36601132308954657866676119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24400754872636438577784079 36601132308954657866676119)
                ·
                  refine ⟨54901698463431986800014179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36601132308954657866676119 54901698463431986800014179)
                  ·
                    refine ⟨82352547695147980200021269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54901698463431986800014179 82352547695147980200021269)
                    ·
                      refine ⟨3860275673210061571875997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82352547695147980200021269 3860275673210061571875997)
                      ·
                        rfl

theorem cell23_7517860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_7517860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517860 prefixEnd_7517860 := by exact prefixLift 7517860
  have htrace : WordTrace (prefixWord ++ tailWord_7517860) baseStart_7517860 baseEnd_7517860 := by
    simpa [prefixWord, tailWord_7517860, baseEnd_7517860] using wordTrace_append hprefix tailTrace_7517860
  have hstable : (prefixWord ++ tailWord_7517860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517860).length < 2 ^ (prefixWord ++ tailWord_7517860).sum := by decide
  have hdescent : baseEnd_7517860 < baseStart_7517860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517883 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 4, 7]
def baseStart_7517883 : Nat := 118140960795 + 7517883 * 2 ^ 59
def prefixEnd_7517883 : Nat := 4983230072969 + 3 ^ 40 * 7517883 * 2
def baseEnd_7517883 : Nat := 1286762494421704993962797

theorem tailTrace_7517883 : CollatzResearch.WordTrace tailWord_7517883 prefixEnd_7517883 1286762494421704993962797 := by
  unfold tailWord_7517883
  simp only [CollatzResearch.WordTrace]
  refine ⟨274199719423001318040854303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182799812948667545360569535 274199719423001318040854303)
  ·
    refine ⟨411299579134501977061281455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274199719423001318040854303 411299579134501977061281455)
    ·
      refine ⟨616949368701752965591922183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411299579134501977061281455 616949368701752965591922183)
      ·
        refine ⟨925424053052629448387883275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616949368701752965591922183 925424053052629448387883275)
        ·
          refine ⟨1388136079578944172581824913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925424053052629448387883275 1388136079578944172581824913)
          ·
            refine ⟨1041102059684208129436368685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1388136079578944172581824913 1041102059684208129436368685)
            ·
              refine ⟨390413272381578048538638257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1041102059684208129436368685 390413272381578048538638257)
              ·
                refine ⟨292809954286183536403978693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390413272381578048538638257 292809954286183536403978693)
                ·
                  refine ⟨54901866428659413075746005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 292809954286183536403978693 54901866428659413075746005)
                  ·
                    refine ⟨1286762494421704993962797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54901866428659413075746005 1286762494421704993962797)
                    ·
                      rfl

theorem cell23_7517883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 7].length) (baseStart_7517883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517883 prefixEnd_7517883 := by exact prefixLift 7517883
  have htrace : WordTrace (prefixWord ++ tailWord_7517883) baseStart_7517883 baseEnd_7517883 := by
    simpa [prefixWord, tailWord_7517883, baseEnd_7517883] using wordTrace_append hprefix tailTrace_7517883
  have hstable : (prefixWord ++ tailWord_7517883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517883).length < 2 ^ (prefixWord ++ tailWord_7517883).sum := by decide
  have hdescent : baseEnd_7517883 < baseStart_7517883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517898 : List Nat := [3, 1, 2, 1, 5, 1, 1, 4, 1, 2, 2]
def baseStart_7517898 : Nat := 118140960795 + 7517898 * 2 ^ 59
def prefixEnd_7517898 : Nat := 4983230072969 + 3 ^ 40 * 7517898 * 2
def baseEnd_7517898 : Nat := 3860295185474932423200823

theorem tailTrace_7517898 : CollatzResearch.WordTrace tailWord_7517898 prefixEnd_7517898 3860295185474932423200823 := by
  unfold tailWord_7517898
  simp only [CollatzResearch.WordTrace]
  refine ⟨68550066629486743900662587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182800177678631317068433565 68550066629486743900662587)
  ·
    refine ⟨102825099944230115850993881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68550066629486743900662587 102825099944230115850993881)
    ·
      refine ⟨77118824958172586888245411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102825099944230115850993881 77118824958172586888245411)
      ·
        refine ⟨115678237437258880332368117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77118824958172586888245411 115678237437258880332368117)
        ·
          refine ⟨10844834759743020031159511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115678237437258880332368117 10844834759743020031159511)
          ·
            refine ⟨16267252139614530046739267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10844834759743020031159511 16267252139614530046739267)
            ·
              refine ⟨24400878209421795070108901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16267252139614530046739267 24400878209421795070108901)
              ·
                refine ⟨4575164664266586575645419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24400878209421795070108901 4575164664266586575645419)
                ·
                  refine ⟨6862746996399879863468129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4575164664266586575645419 6862746996399879863468129)
                  ·
                    refine ⟨5147060247299909897601097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6862746996399879863468129 5147060247299909897601097)
                    ·
                      refine ⟨3860295185474932423200823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5147060247299909897601097 3860295185474932423200823)
                      ·
                        rfl

theorem cell23_7517898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 4, 1, 2, 2].length) (baseStart_7517898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517898 prefixEnd_7517898 := by exact prefixLift 7517898
  have htrace : WordTrace (prefixWord ++ tailWord_7517898) baseStart_7517898 baseEnd_7517898 := by
    simpa [prefixWord, tailWord_7517898, baseEnd_7517898] using wordTrace_append hprefix tailTrace_7517898
  have hstable : (prefixWord ++ tailWord_7517898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517898).length < 2 ^ (prefixWord ++ tailWord_7517898).sum := by decide
  have hdescent : baseEnd_7517898 < baseStart_7517898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517914 : List Nat := [3, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3]
def baseStart_7517914 : Nat := 118140960795 + 7517914 * 2 ^ 59
def prefixEnd_7517914 : Nat := 4983230072969 + 3 ^ 40 * 7517914 * 2
def baseEnd_7517914 : Nat := 3860303401165404360600749

theorem tailTrace_7517914 : CollatzResearch.WordTrace tailWord_7517914 prefixEnd_7517914 3860303401165404360600749 := by
  unfold tailWord_7517914
  simp only [CollatzResearch.WordTrace]
  refine ⟨68550212521472252583808199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182800566723926006890155197 68550212521472252583808199)
  ·
    refine ⟨102825318782208378875712299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68550212521472252583808199 102825318782208378875712299)
    ·
      refine ⟨154237978173312568313568449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102825318782208378875712299 154237978173312568313568449)
      ·
        refine ⟨115678483629984426235176337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154237978173312568313568449 115678483629984426235176337)
        ·
          refine ⟨86758862722488319676382253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115678483629984426235176337 86758862722488319676382253)
          ·
            refine ⟨32534573520933119878643345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86758862722488319676382253 32534573520933119878643345)
            ·
              refine ⟨24400930140699839908982509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32534573520933119878643345 24400930140699839908982509)
              ·
                refine ⟨9150348802762439965868441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24400930140699839908982509 9150348802762439965868441)
                ·
                  refine ⟨6862761602071829974401331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9150348802762439965868441 6862761602071829974401331)
                  ·
                    refine ⟨10294142403107744961601997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6862761602071829974401331 10294142403107744961601997)
                    ·
                      refine ⟨3860303401165404360600749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10294142403107744961601997 3860303401165404360600749)
                      ·
                        rfl

theorem cell23_7517914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_7517914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517914 prefixEnd_7517914 := by exact prefixLift 7517914
  have htrace : WordTrace (prefixWord ++ tailWord_7517914) baseStart_7517914 baseEnd_7517914 := by
    simpa [prefixWord, tailWord_7517914, baseEnd_7517914] using wordTrace_append hprefix tailTrace_7517914
  have hstable : (prefixWord ++ tailWord_7517914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517914).length < 2 ^ (prefixWord ++ tailWord_7517914).sum := by decide
  have hdescent : baseEnd_7517914 < baseStart_7517914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7517924 : List Nat := [2, 3, 1, 1, 1, 3, 2, 4, 1, 3, 2]
def baseStart_7517924 : Nat := 118140960795 + 7517924 * 2 ^ 59
def prefixEnd_7517924 : Nat := 4983230072969 + 3 ^ 40 * 7517924 * 2
def baseEnd_7517924 : Nat := 3860308535971949321475703

theorem tailTrace_7517924 : CollatzResearch.WordTrace tailWord_7517924 prefixEnd_7517924 3860308535971949321475703 := by
  unfold tailWord_7517924
  simp only [CollatzResearch.WordTrace]
  refine ⟨137100607407926391021548413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182800809877235188028731217 137100607407926391021548413)
  ·
    refine ⟨51412727777972396633080655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137100607407926391021548413 51412727777972396633080655)
    ·
      refine ⟨77119091666958594949620983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51412727777972396633080655 77119091666958594949620983)
      ·
        refine ⟨115678637500437892424431475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77119091666958594949620983 115678637500437892424431475)
        ·
          refine ⟨173517956250656838636647213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115678637500437892424431475 173517956250656838636647213)
          ·
            refine ⟨65069233593996314488742705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173517956250656838636647213 65069233593996314488742705)
            ·
              refine ⟨48801925195497235866557029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65069233593996314488742705 48801925195497235866557029)
              ·
                refine ⟨9150360974155731724979443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48801925195497235866557029 9150360974155731724979443)
                ·
                  refine ⟨13725541461233597587469165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9150360974155731724979443 13725541461233597587469165)
                  ·
                    refine ⟨5147078047962599095300937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13725541461233597587469165 5147078047962599095300937)
                    ·
                      refine ⟨3860308535971949321475703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5147078047962599095300937 3860308535971949321475703)
                      ·
                        rfl

theorem cell23_7517924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_7517924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7517924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7517924 prefixEnd_7517924 := by exact prefixLift 7517924
  have htrace : WordTrace (prefixWord ++ tailWord_7517924) baseStart_7517924 baseEnd_7517924 := by
    simpa [prefixWord, tailWord_7517924, baseEnd_7517924] using wordTrace_append hprefix tailTrace_7517924
  have hstable : (prefixWord ++ tailWord_7517924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7517924).length < 2 ^ (prefixWord ++ tailWord_7517924).sum := by decide
  have hdescent : baseEnd_7517924 < baseStart_7517924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7517924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518022 : List Nat := [6, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2]
def baseStart_7518022 : Nat := 118140960795 + 7518022 * 2 ^ 59
def prefixEnd_7518022 : Nat := 4983230072969 + 3 ^ 40 * 7518022 * 2
def baseEnd_7518022 : Nat := 3860358857076089938050253

theorem tailTrace_7518022 : CollatzResearch.WordTrace tailWord_7518022 prefixEnd_7518022 3860358857076089938050253 := by
  unfold tailWord_7518022
  simp only [CollatzResearch.WordTrace]
  refine ⟨8568899661546804524380135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 182803192779665163186776213 8568899661546804524380135)
  ·
    refine ⟨12853349492320206786570203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8568899661546804524380135 12853349492320206786570203)
    ·
      refine ⟨19280024238480310179855305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12853349492320206786570203 19280024238480310179855305)
      ·
        refine ⟨14460018178860232634891479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19280024238480310179855305 14460018178860232634891479)
        ·
          refine ⟨21690027268290348952337219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14460018178860232634891479 21690027268290348952337219)
          ·
            refine ⟨32535040902435523428505829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21690027268290348952337219 32535040902435523428505829)
            ·
              refine ⟨6100320169206660642844843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32535040902435523428505829 6100320169206660642844843)
              ·
                refine ⟨9150480253809990964267265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6100320169206660642844843 9150480253809990964267265)
                ·
                  refine ⟨6862860190357493223200449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9150480253809990964267265 6862860190357493223200449)
                  ·
                    refine ⟨5147145142768119917400337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6862860190357493223200449 5147145142768119917400337)
                    ·
                      refine ⟨3860358857076089938050253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5147145142768119917400337 3860358857076089938050253)
                      ·
                        rfl

theorem cell23_7518022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_7518022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518022 prefixEnd_7518022 := by exact prefixLift 7518022
  have htrace : WordTrace (prefixWord ++ tailWord_7518022) baseStart_7518022 baseEnd_7518022 := by
    simpa [prefixWord, tailWord_7518022, baseEnd_7518022] using wordTrace_append hprefix tailTrace_7518022
  have hstable : (prefixWord ++ tailWord_7518022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518022).length < 2 ^ (prefixWord ++ tailWord_7518022).sum := by decide
  have hdescent : baseEnd_7518022 < baseStart_7518022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518040 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 3, 3, 6]
def baseStart_7518040 : Nat := 118140960795 + 7518040 * 2 ^ 59
def prefixEnd_7518040 : Nat := 4983230072969 + 3 ^ 40 * 7518040 * 2
def baseEnd_7518040 : Nat := 3860368099727870867625169

theorem tailTrace_7518040 : CollatzResearch.WordTrace tailWord_7518040 prefixEnd_7518040 3860368099727870867625169 := by
  unfold tailWord_7518040
  simp only [CollatzResearch.WordTrace]
  refine ⟨137102722841716266927159787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182803630455621689236213049 137102722841716266927159787)
  ·
    refine ⟨205654084262574400390739681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137102722841716266927159787 205654084262574400390739681)
    ·
      refine ⟨154240563196930800293054761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205654084262574400390739681 154240563196930800293054761)
      ·
        refine ⟨115680422397698100219791071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154240563196930800293054761 115680422397698100219791071)
        ·
          refine ⟨173520633596547150329686607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115680422397698100219791071 173520633596547150329686607)
          ·
            refine ⟨260280950394820725494529911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173520633596547150329686607 260280950394820725494529911)
            ·
              refine ⟨390421425592231088241794867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260280950394820725494529911 390421425592231088241794867)
              ·
                refine ⟨585632138388346632362692301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390421425592231088241794867 585632138388346632362692301)
                ·
                  refine ⟨219612051895629987136009613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 585632138388346632362692301 219612051895629987136009613)
                  ·
                    refine ⟨82354519460861245176003605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 219612051895629987136009613 82354519460861245176003605)
                    ·
                      refine ⟨3860368099727870867625169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 82354519460861245176003605 3860368099727870867625169)
                      ·
                        rfl

theorem cell23_7518040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_7518040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518040 prefixEnd_7518040 := by exact prefixLift 7518040
  have htrace : WordTrace (prefixWord ++ tailWord_7518040) baseStart_7518040 baseEnd_7518040 := by
    simpa [prefixWord, tailWord_7518040, baseEnd_7518040] using wordTrace_append hprefix tailTrace_7518040
  have hstable : (prefixWord ++ tailWord_7518040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518040).length < 2 ^ (prefixWord ++ tailWord_7518040).sum := by decide
  have hdescent : baseEnd_7518040 < baseStart_7518040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518077 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 2, 5, 3]
def baseStart_7518077 : Nat := 118140960795 + 7518077 * 2 ^ 59
def prefixEnd_7518077 : Nat := 4983230072969 + 3 ^ 40 * 7518077 * 2
def baseEnd_7518077 : Nat := 3860387098512087222862499

theorem tailTrace_7518077 : CollatzResearch.WordTrace tailWord_7518077 prefixEnd_7518077 3860387098512087222862499 := by
  unfold tailWord_7518077
  simp only [CollatzResearch.WordTrace]
  refine ⟨274206795184298489173416485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182804530122865659448944323 274206795184298489173416485)
  ·
    refine ⟨51413774097055966720015591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 274206795184298489173416485 51413774097055966720015591)
    ·
      refine ⟨77120661145583950080023387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51413774097055966720015591 77120661145583950080023387)
      ·
        refine ⟨115680991718375925120035081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77120661145583950080023387 115680991718375925120035081)
        ·
          refine ⟨86760743788781943840026311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115680991718375925120035081 86760743788781943840026311)
          ·
            refine ⟨130141115683172915760039467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86760743788781943840026311 130141115683172915760039467)
            ·
              refine ⟨195211673524759373640059201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130141115683172915760039467 195211673524759373640059201)
              ·
                refine ⟨146408755143569530230044401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195211673524759373640059201 146408755143569530230044401)
                ·
                  refine ⟨109806566357677147672533301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146408755143569530230044401 109806566357677147672533301)
                  ·
                    refine ⟨10294365596032232594299997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109806566357677147672533301 10294365596032232594299997)
                    ·
                      refine ⟨3860387098512087222862499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10294365596032232594299997 3860387098512087222862499)
                      ·
                        rfl

theorem cell23_7518077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_7518077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518077 prefixEnd_7518077 := by exact prefixLift 7518077
  have htrace : WordTrace (prefixWord ++ tailWord_7518077) baseStart_7518077 baseEnd_7518077 := by
    simpa [prefixWord, tailWord_7518077, baseEnd_7518077] using wordTrace_append hprefix tailTrace_7518077
  have hstable : (prefixWord ++ tailWord_7518077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518077).length < 2 ^ (prefixWord ++ tailWord_7518077).sum := by decide
  have hdescent : baseEnd_7518077 < baseStart_7518077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518078 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_7518078 : Nat := 118140960795 + 7518078 * 2 ^ 59
def prefixEnd_7518078 : Nat := 4983230072969 + 3 ^ 40 * 7518078 * 2
def baseEnd_7518078 : Nat := 3860387611992741718949995

theorem tailTrace_7518078 : CollatzResearch.WordTrace tailWord_7518078 prefixEnd_7518078 3860387611992741718949995 := by
  unfold tailWord_7518078
  simp only [CollatzResearch.WordTrace]
  refine ⟨34275853957161858293025361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 182804554438196577562801925 34275853957161858293025361)
  ·
    refine ⟨25706890467871393719769021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34275853957161858293025361 25706890467871393719769021)
    ·
      refine ⟨9640083925451772644913383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25706890467871393719769021 9640083925451772644913383)
      ·
        refine ⟨14460125888177658967370075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9640083925451772644913383 14460125888177658967370075)
        ·
          refine ⟨21690188832266488451055113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14460125888177658967370075 21690188832266488451055113)
          ·
            refine ⟨16267641624199866338291335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21690188832266488451055113 16267641624199866338291335)
            ·
              refine ⟨24401462436299799507437003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16267641624199866338291335 24401462436299799507437003)
              ·
                refine ⟨36602193654449699261155505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24401462436299799507437003 36602193654449699261155505)
                ·
                  refine ⟨27451645240837274445866629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36602193654449699261155505 27451645240837274445866629)
                  ·
                    refine ⟨5147183482656988958599993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27451645240837274445866629 5147183482656988958599993)
                    ·
                      refine ⟨3860387611992741718949995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5147183482656988958599993 3860387611992741718949995)
                      ·
                        rfl

theorem cell23_7518078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_7518078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518078 prefixEnd_7518078 := by exact prefixLift 7518078
  have htrace : WordTrace (prefixWord ++ tailWord_7518078) baseStart_7518078 baseEnd_7518078 := by
    simpa [prefixWord, tailWord_7518078, baseEnd_7518078] using wordTrace_append hprefix tailTrace_7518078
  have hstable : (prefixWord ++ tailWord_7518078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518078).length < 2 ^ (prefixWord ++ tailWord_7518078).sum := by decide
  have hdescent : baseEnd_7518078 < baseStart_7518078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518097 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 3, 5]
def baseStart_7518097 : Nat := 118140960795 + 7518097 * 2 ^ 59
def prefixEnd_7518097 : Nat := 4983230072969 + 3 ^ 40 * 7518097 * 2
def baseEnd_7518097 : Nat := 1286799122708392381537469

theorem tailTrace_7518097 : CollatzResearch.WordTrace tailWord_7518097 prefixEnd_7518097 1286799122708392381537469 := by
  unfold tailWord_7518097
  simp only [CollatzResearch.WordTrace]
  refine ⟨274207524644226032589144545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182805016429484021726096363 274207524644226032589144545)
  ·
    refine ⟨205655643483169524441858409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274207524644226032589144545 205655643483169524441858409)
    ·
      refine ⟨154241732612377143331393807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205655643483169524441858409 154241732612377143331393807)
      ·
        refine ⟨231362598918565714997090711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154241732612377143331393807 231362598918565714997090711)
        ·
          refine ⟨347043898377848572495636067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231362598918565714997090711 347043898377848572495636067)
          ·
            refine ⟨520565847566772858743454101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347043898377848572495636067 520565847566772858743454101)
            ·
              refine ⟨24401524104692477753599411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 520565847566772858743454101 24401524104692477753599411)
              ·
                refine ⟨36602286157038716630399117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24401524104692477753599411 36602286157038716630399117)
                ·
                  refine ⟨13725857308889518736399669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36602286157038716630399117 13725857308889518736399669)
                  ·
                    refine ⟨1286799122708392381537469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13725857308889518736399669 1286799122708392381537469)
                    ·
                      rfl

theorem cell23_7518097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_7518097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518097 prefixEnd_7518097 := by exact prefixLift 7518097
  have htrace : WordTrace (prefixWord ++ tailWord_7518097) baseStart_7518097 baseEnd_7518097 := by
    simpa [prefixWord, tailWord_7518097, baseEnd_7518097] using wordTrace_append hprefix tailTrace_7518097
  have hstable : (prefixWord ++ tailWord_7518097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518097).length < 2 ^ (prefixWord ++ tailWord_7518097).sum := by decide
  have hdescent : baseEnd_7518097 < baseStart_7518097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518098 : List Nat := [3, 2, 3, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_7518098 : Nat := 118140960795 + 7518098 * 2 ^ 59
def prefixEnd_7518098 : Nat := 4983230072969 + 3 ^ 40 * 7518098 * 2
def baseEnd_7518098 : Nat := 3860397881605831640699903

theorem tailTrace_7518098 : CollatzResearch.WordTrace tailWord_7518098 prefixEnd_7518098 3860397881605831640699903 := by
  unfold tailWord_7518098
  simp only [CollatzResearch.WordTrace]
  refine ⟨68551890279305602439982737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182805040744814939839953965 68551890279305602439982737)
  ·
    refine ⟨51413917709479201829987053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68551890279305602439982737 51413917709479201829987053)
    ·
      refine ⟨19280219141054700686245145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51413917709479201829987053 19280219141054700686245145)
      ·
        refine ⟨14460164355791025514683859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19280219141054700686245145 14460164355791025514683859)
        ·
          refine ⟨21690246533686538272025789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14460164355791025514683859 21690246533686538272025789)
          ·
            refine ⟨8133842450132451852009671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21690246533686538272025789 8133842450132451852009671)
            ·
              refine ⟨12200763675198677778014507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8133842450132451852009671 12200763675198677778014507)
              ·
                refine ⟨18301145512798016667021761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12200763675198677778014507 18301145512798016667021761)
                ·
                  refine ⟨13725859134598512500266321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18301145512798016667021761 13725859134598512500266321)
                  ·
                    refine ⟨10294394350948884375199741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13725859134598512500266321 10294394350948884375199741)
                    ·
                      refine ⟨3860397881605831640699903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10294394350948884375199741 3860397881605831640699903)
                      ·
                        rfl

theorem cell23_7518098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_7518098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518098 prefixEnd_7518098 := by exact prefixLift 7518098
  have htrace : WordTrace (prefixWord ++ tailWord_7518098) baseStart_7518098 baseEnd_7518098 := by
    simpa [prefixWord, tailWord_7518098, baseEnd_7518098] using wordTrace_append hprefix tailTrace_7518098
  have hstable : (prefixWord ++ tailWord_7518098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518098).length < 2 ^ (prefixWord ++ tailWord_7518098).sum := by decide
  have hdescent : baseEnd_7518098 < baseStart_7518098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518154 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 3, 2, 3]
def baseStart_7518154 : Nat := 118140960795 + 7518154 * 2 ^ 59
def prefixEnd_7518154 : Nat := 4983230072969 + 3 ^ 40 * 7518154 * 2
def baseEnd_7518154 : Nat := 3860426636522483421599645

theorem tailTrace_7518154 : CollatzResearch.WordTrace tailWord_7518154 prefixEnd_7518154 3860426636522483421599645 := by
  unfold tailWord_7518154
  simp only [CollatzResearch.WordTrace]
  refine ⟨68552400901254882830992379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182806402403346354215979677 68552400901254882830992379)
  ·
    refine ⟨102828601351882324246488569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68552400901254882830992379 102828601351882324246488569)
    ·
      refine ⟨77121451013911743184866427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102828601351882324246488569 77121451013911743184866427)
      ·
        refine ⟨115682176520867614777299641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77121451013911743184866427 115682176520867614777299641)
        ·
          refine ⟨86761632390650711082974731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115682176520867614777299641 86761632390650711082974731)
          ·
            refine ⟨130142448585976066624462097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86761632390650711082974731 130142448585976066624462097)
            ·
              refine ⟨97606836439482049968346573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130142448585976066624462097 97606836439482049968346573)
              ·
                refine ⟨36602563664805768738129965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97606836439482049968346573 36602563664805768738129965)
                ·
                  refine ⟨13725961374302163276798737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36602563664805768738129965 13725961374302163276798737)
                  ·
                    refine ⟨10294471030726622457599053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13725961374302163276798737 10294471030726622457599053)
                    ·
                      refine ⟨3860426636522483421599645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10294471030726622457599053 3860426636522483421599645)
                      ·
                        rfl

theorem cell23_7518154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_7518154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518154 prefixEnd_7518154 := by exact prefixLift 7518154
  have htrace : WordTrace (prefixWord ++ tailWord_7518154) baseStart_7518154 baseEnd_7518154 := by
    simpa [prefixWord, tailWord_7518154, baseEnd_7518154] using wordTrace_append hprefix tailTrace_7518154
  have hstable : (prefixWord ++ tailWord_7518154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518154).length < 2 ^ (prefixWord ++ tailWord_7518154).sum := by decide
  have hdescent : baseEnd_7518154 < baseStart_7518154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518162 : List Nat := [3, 2, 2, 3, 2, 2, 1, 3, 1, 1, 3]
def baseStart_7518162 : Nat := 118140960795 + 7518162 * 2 ^ 59
def prefixEnd_7518162 : Nat := 4983230072969 + 3 ^ 40 * 7518162 * 2
def baseEnd_7518162 : Nat := 3860430744367719390299609

theorem tailTrace_7518162 : CollatzResearch.WordTrace tailWord_7518162 prefixEnd_7518162 3860430744367719390299609 := by
  unfold tailWord_7518162
  simp only [CollatzResearch.WordTrace]
  refine ⟨68552473847247637172565185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 182806596925993699126840493 68552473847247637172565185)
  ·
    refine ⟨51414355385435727879423889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68552473847247637172565185 51414355385435727879423889)
    ·
      refine ⟨38560766539076795909567917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51414355385435727879423889 38560766539076795909567917)
      ·
        refine ⟨14460287452153798466087969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38560766539076795909567917 14460287452153798466087969)
        ·
          refine ⟨10845215589115348849565977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14460287452153798466087969 10845215589115348849565977)
          ·
            refine ⟨8133911691836511637174483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10845215589115348849565977 8133911691836511637174483)
            ·
              refine ⟨12200867537754767455761725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8133911691836511637174483 12200867537754767455761725)
              ·
                refine ⟨4575325326658037795910647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12200867537754767455761725 4575325326658037795910647)
                ·
                  refine ⟨6862987989987056693865971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4575325326658037795910647 6862987989987056693865971)
                  ·
                    refine ⟨10294481984980585040798957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6862987989987056693865971 10294481984980585040798957)
                    ·
                      refine ⟨3860430744367719390299609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10294481984980585040798957 3860430744367719390299609)
                      ·
                        rfl

theorem cell23_7518162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_7518162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518162 prefixEnd_7518162 := by exact prefixLift 7518162
  have htrace : WordTrace (prefixWord ++ tailWord_7518162) baseStart_7518162 baseEnd_7518162 := by
    simpa [prefixWord, tailWord_7518162, baseEnd_7518162] using wordTrace_append hprefix tailTrace_7518162
  have hstable : (prefixWord ++ tailWord_7518162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518162).length < 2 ^ (prefixWord ++ tailWord_7518162).sum := by decide
  have hdescent : baseEnd_7518162 < baseStart_7518162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7518164 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_7518164 : Nat := 118140960795 + 7518164 * 2 ^ 59
def prefixEnd_7518164 : Nat := 4983230072969 + 3 ^ 40 * 7518164 * 2
def baseEnd_7518164 : Nat := 3860431771329028382474599

theorem tailTrace_7518164 : CollatzResearch.WordTrace tailWord_7518164 prefixEnd_7518164 3860431771329028382474599 := by
  unfold tailWord_7518164
  simp only [CollatzResearch.WordTrace]
  refine ⟨137104984167491651515916773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 182806645556655535354555697 137104984167491651515916773)
  ·
    refine ⟨25707184531404684659234395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137104984167491651515916773 25707184531404684659234395)
    ·
      refine ⟨38560776797107026988851593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25707184531404684659234395 38560776797107026988851593)
      ·
        refine ⟨28920582597830270241638695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38560776797107026988851593 28920582597830270241638695)
        ·
          refine ⟨43380873896745405362458043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28920582597830270241638695 43380873896745405362458043)
          ·
            refine ⟨65071310845118108043687065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43380873896745405362458043 65071310845118108043687065)
            ·
              refine ⟨48803483133838581032765299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65071310845118108043687065 48803483133838581032765299)
              ·
                refine ⟨73205224700757871549147949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48803483133838581032765299 73205224700757871549147949)
                ·
                  refine ⟨27451959262784201830930481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73205224700757871549147949 27451959262784201830930481)
                  ·
                    refine ⟨20588969447088151373197861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27451959262784201830930481 20588969447088151373197861)
                    ·
                      refine ⟨3860431771329028382474599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20588969447088151373197861 3860431771329028382474599)
                      ·
                        rfl

theorem cell23_7518164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_7518164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7518164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7518164 prefixEnd_7518164 := by exact prefixLift 7518164
  have htrace : WordTrace (prefixWord ++ tailWord_7518164) baseStart_7518164 baseEnd_7518164 := by
    simpa [prefixWord, tailWord_7518164, baseEnd_7518164] using wordTrace_append hprefix tailTrace_7518164
  have hstable : (prefixWord ++ tailWord_7518164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7518164).length < 2 ^ (prefixWord ++ tailWord_7518164).sum := by decide
  have hdescent : baseEnd_7518164 < baseStart_7518164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7518164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
