import V185TrunkScan20Chunk018

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_115069 : List Nat := [1, 4, 1, 1, 2, 4, 2, 5]
def baseStart_115069 : Nat := 118140960795 + 115069 * 2 ^ 59
def prefixEnd_115069 : Nat := 4983230072969 + 3 ^ 40 * 115069 * 2
def baseEnd_115069 : Nat := 17506875683649044654315

theorem tailTrace_115069 : CollatzResearch.WordTrace tailWord_115069 prefixEnd_115069 17506875683649044654315 := by
  unfold tailWord_115069
  simp only [CollatzResearch.WordTrace]
  refine ⟨4196911220132140065716261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2797940813421426710477507 4196911220132140065716261)
  ·
    refine ⟨786920853774776262321799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4196911220132140065716261 786920853774776262321799)
    ·
      refine ⟨1180381280662164393482699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 786920853774776262321799 1180381280662164393482699)
      ·
        refine ⟨1770571920993246590224049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1180381280662164393482699 1770571920993246590224049)
        ·
          refine ⟨1327928940744934942668037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1770571920993246590224049 1327928940744934942668037)
          ·
            refine ⟨248986676389675301750257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1327928940744934942668037 248986676389675301750257)
            ·
              refine ⟨186740007292256476312693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248986676389675301750257 186740007292256476312693)
              ·
                refine ⟨17506875683649044654315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186740007292256476312693 17506875683649044654315)
                ·
                  rfl

theorem cell20_115069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 5].length) (baseStart_115069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115069 prefixEnd_115069 := by exact prefixLift 115069
  have htrace : WordTrace (prefixWord ++ tailWord_115069) baseStart_115069 baseEnd_115069 := by
    simpa [prefixWord, tailWord_115069, baseEnd_115069] using wordTrace_append hprefix tailTrace_115069
  have hstable : (prefixWord ++ tailWord_115069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115069).length < 2 ^ (prefixWord ++ tailWord_115069).sum := by decide
  have hdescent : baseEnd_115069 < baseStart_115069 := by decide
  rcases family_descends (prefixWord ++ tailWord_115069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115135 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 9]
def baseStart_115135 : Nat := 118140960795 + 115135 * 2 ^ 59
def prefixEnd_115135 : Nat := 4983230072969 + 3 ^ 40 * 115135 * 2
def baseEnd_115135 : Nat := 52550751249344237762675

theorem tailTrace_115135 : CollatzResearch.WordTrace tailWord_115135 prefixEnd_115135 52550751249344237762675 := by
  unfold tailWord_115135
  simp only [CollatzResearch.WordTrace]
  refine ⟨4199318437893033337618859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2799545625262022225079239 4199318437893033337618859)
  ·
    refine ⟨6298977656839550006428289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4199318437893033337618859 6298977656839550006428289)
    ·
      refine ⟨4724233242629662504821217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6298977656839550006428289 4724233242629662504821217)
      ·
        refine ⟨3543174931972246878615913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4724233242629662504821217 3543174931972246878615913)
        ·
          refine ⟨2657381198979185158961935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3543174931972246878615913 2657381198979185158961935)
          ·
            refine ⟨3986071798468777738442903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2657381198979185158961935 3986071798468777738442903)
            ·
              refine ⟨5979107697703166607664355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3986071798468777738442903 5979107697703166607664355)
              ·
                refine ⟨8968661546554749911496533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5979107697703166607664355 8968661546554749911496533)
                ·
                  refine ⟨52550751249344237762675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8968661546554749911496533 52550751249344237762675)
                  ·
                    rfl

theorem cell20_115135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_115135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115135 prefixEnd_115135 := by exact prefixLift 115135
  have htrace : WordTrace (prefixWord ++ tailWord_115135) baseStart_115135 baseEnd_115135 := by
    simpa [prefixWord, tailWord_115135, baseEnd_115135] using wordTrace_append hprefix tailTrace_115135
  have hstable : (prefixWord ++ tailWord_115135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115135).length < 2 ^ (prefixWord ++ tailWord_115135).sum := by decide
  have hdescent : baseEnd_115135 < baseStart_115135 := by decide
  rcases family_descends (prefixWord ++ tailWord_115135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115176 : List Nat := [2, 1, 4, 1, 1, 4, 2, 1, 4]
def baseStart_115176 : Nat := 118140960795 + 115176 * 2 ^ 59
def prefixEnd_115176 : Nat := 4983230072969 + 3 ^ 40 * 115176 * 2
def baseEnd_115176 : Nat := 52569464766530317395841

theorem tailTrace_115176 : CollatzResearch.WordTrace tailWord_115176 prefixEnd_115176 52569464766530317395841 := by
  unfold tailWord_115176
  simp only [CollatzResearch.WordTrace]
  refine ⟨2100406915372248669930691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2800542553829664893240921 2100406915372248669930691)
  ·
    refine ⟨3150610373058373004896037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2100406915372248669930691 3150610373058373004896037)
    ·
      refine ⟨590739444948444938418007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3150610373058373004896037 590739444948444938418007)
      ·
        refine ⟨886109167422667407627011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590739444948444938418007 886109167422667407627011)
        ·
          refine ⟨1329163751134001111440517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886109167422667407627011 1329163751134001111440517)
          ·
            refine ⟨249218203337625208395097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1329163751134001111440517 249218203337625208395097)
            ·
              refine ⟨186913652503218906296323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249218203337625208395097 186913652503218906296323)
              ·
                refine ⟨280370478754828359444485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186913652503218906296323 280370478754828359444485)
                ·
                  refine ⟨52569464766530317395841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 280370478754828359444485 52569464766530317395841)
                  ·
                    rfl

theorem cell20_115176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_115176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115176 prefixEnd_115176 := by exact prefixLift 115176
  have htrace : WordTrace (prefixWord ++ tailWord_115176) baseStart_115176 baseEnd_115176 := by
    simpa [prefixWord, tailWord_115176, baseEnd_115176] using wordTrace_append hprefix tailTrace_115176
  have hstable : (prefixWord ++ tailWord_115176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115176).length < 2 ^ (prefixWord ++ tailWord_115176).sum := by decide
  have hdescent : baseEnd_115176 < baseStart_115176 := by decide
  rcases family_descends (prefixWord ++ tailWord_115176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115197 : List Nat := [1, 4, 1, 1, 1, 3, 1, 4, 4]
def baseStart_115197 : Nat := 118140960795 + 115197 * 2 ^ 59
def prefixEnd_115197 : Nat := 4983230072969 + 3 ^ 40 * 115197 * 2
def baseEnd_115197 : Nat := 52579049738747577695755

theorem tailTrace_115197 : CollatzResearch.WordTrace tailWord_115197 prefixEnd_115197 52579049738747577695755 := by
  unfold tailWord_115197
  simp only [CollatzResearch.WordTrace]
  refine ⟨4201579763668417926375845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2801053175778945284250563 4201579763668417926375845)
  ·
    refine ⟨787796205687828361195471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4201579763668417926375845 787796205687828361195471)
    ·
      refine ⟨1181694308531742541793207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 787796205687828361195471 1181694308531742541793207)
      ·
        refine ⟨1772541462797613812689811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1181694308531742541793207 1772541462797613812689811)
        ·
          refine ⟨2658812194196420719034717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1772541462797613812689811 2658812194196420719034717)
          ·
            refine ⟨997054572823657769638019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2658812194196420719034717 997054572823657769638019)
            ·
              refine ⟨1495581859235486654457029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 997054572823657769638019 1495581859235486654457029)
              ·
                refine ⟨280421598606653747710693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1495581859235486654457029 280421598606653747710693)
                ·
                  refine ⟨52579049738747577695755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 280421598606653747710693 52579049738747577695755)
                  ·
                    rfl

theorem cell20_115197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_115197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115197 prefixEnd_115197 := by exact prefixLift 115197
  have htrace : WordTrace (prefixWord ++ tailWord_115197) baseStart_115197 baseEnd_115197 := by
    simpa [prefixWord, tailWord_115197, baseEnd_115197] using wordTrace_append hprefix tailTrace_115197
  have hstable : (prefixWord ++ tailWord_115197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115197).length < 2 ^ (prefixWord ++ tailWord_115197).sum := by decide
  have hdescent : baseEnd_115197 < baseStart_115197 := by decide
  rcases family_descends (prefixWord ++ tailWord_115197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115206 : List Nat := [6, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_115206 : Nat := 118140960795 + 115206 * 2 ^ 59
def prefixEnd_115206 : Nat := 4983230072969 + 3 ^ 40 * 115206 * 2
def baseEnd_115206 : Nat := 52583157583983546395719

theorem tailTrace_115206 : CollatzResearch.WordTrace tailWord_115206 prefixEnd_115206 52583157583983546395719 := by
  unfold tailWord_115206
  simp only [CollatzResearch.WordTrace]
  refine ⟨131309625644869139482921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2801272013757208308968981 131309625644869139482921)
  ·
    refine ⟨98482219233651854612191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131309625644869139482921 98482219233651854612191)
    ·
      refine ⟨147723328850477781918287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98482219233651854612191 147723328850477781918287)
      ·
        refine ⟨221584993275716672877431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147723328850477781918287 221584993275716672877431)
        ·
          refine ⟨332377489913575009316147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221584993275716672877431 332377489913575009316147)
          ·
            refine ⟨498566234870362513974221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332377489913575009316147 498566234870362513974221)
            ·
              refine ⟨186962338076385942740333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 498566234870362513974221 186962338076385942740333)
              ·
                refine ⟨70110876778644728527625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186962338076385942740333 70110876778644728527625)
                ·
                  refine ⟨52583157583983546395719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70110876778644728527625 52583157583983546395719)
                  ·
                    rfl

theorem cell20_115206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_115206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115206 prefixEnd_115206 := by exact prefixLift 115206
  have htrace : WordTrace (prefixWord ++ tailWord_115206) baseStart_115206 baseEnd_115206 := by
    simpa [prefixWord, tailWord_115206, baseEnd_115206] using wordTrace_append hprefix tailTrace_115206
  have hstable : (prefixWord ++ tailWord_115206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115206).length < 2 ^ (prefixWord ++ tailWord_115206).sum := by decide
  have hdescent : baseEnd_115206 < baseStart_115206 := by decide
  rcases family_descends (prefixWord ++ tailWord_115206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115228 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 5]
def baseStart_115228 : Nat := 118140960795 + 115228 * 2 ^ 59
def prefixEnd_115228 : Nat := 4983230072969 + 3 ^ 40 * 115228 * 2
def baseEnd_115228 : Nat := 52593198983449247662295

theorem tailTrace_115228 : CollatzResearch.WordTrace tailWord_115228 prefixEnd_115228 52593198983449247662295 := by
  unfold tailWord_115228
  simp only [CollatzResearch.WordTrace]
  refine ⟨2101355213278055110377169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2801806951037406813836225 2101355213278055110377169)
  ·
    refine ⟨1576016409958541332782877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2101355213278055110377169 1576016409958541332782877)
    ·
      refine ⟨591006153734452999793579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1576016409958541332782877 591006153734452999793579)
      ·
        refine ⟨886509230601679499690369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591006153734452999793579 886509230601679499690369)
        ·
          refine ⟨664881922951259624767777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 886509230601679499690369 664881922951259624767777)
          ·
            refine ⟨498661442213444718575833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 664881922951259624767777 498661442213444718575833)
            ·
              refine ⟨373996081660083538931875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498661442213444718575833 373996081660083538931875)
              ·
                refine ⟨560994122490125308397813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373996081660083538931875 560994122490125308397813)
                ·
                  refine ⟨52593198983449247662295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 560994122490125308397813 52593198983449247662295)
                  ·
                    rfl

theorem cell20_115228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_115228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115228 prefixEnd_115228 := by exact prefixLift 115228
  have htrace : WordTrace (prefixWord ++ tailWord_115228) baseStart_115228 baseEnd_115228 := by
    simpa [prefixWord, tailWord_115228, baseEnd_115228] using wordTrace_append hprefix tailTrace_115228
  have hstable : (prefixWord ++ tailWord_115228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115228).length < 2 ^ (prefixWord ++ tailWord_115228).sum := by decide
  have hdescent : baseEnd_115228 < baseStart_115228 := by decide
  rcases family_descends (prefixWord ++ tailWord_115228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115297 : List Nat := [1, 2, 3, 1, 1, 6, 1, 5]
def baseStart_115297 : Nat := 118140960795 + 115297 * 2 ^ 59
def prefixEnd_115297 : Nat := 4983230072969 + 3 ^ 40 * 115297 * 2
def baseEnd_115297 : Nat := 17541564154530558120671

theorem tailTrace_115297 : CollatzResearch.WordTrace tailWord_115297 prefixEnd_115297 17541564154530558120671 := by
  unfold tailWord_115297
  simp only [CollatzResearch.WordTrace]
  refine ⟨4205227063306135005016145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2803484708870756670010763 4205227063306135005016145)
  ·
    refine ⟨3153920297479601253762109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4205227063306135005016145 3153920297479601253762109)
    ·
      refine ⟨1182720111554850470160791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3153920297479601253762109 1182720111554850470160791)
      ·
        refine ⟨1774080167332275705241187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1182720111554850470160791 1774080167332275705241187)
        ·
          refine ⟨2661120250998413557861781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1774080167332275705241187 2661120250998413557861781)
          ·
            refine ⟨124740011765550635524771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2661120250998413557861781 124740011765550635524771)
            ·
              refine ⟨187110017648325953287157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124740011765550635524771 187110017648325953287157)
              ·
                refine ⟨17541564154530558120671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187110017648325953287157 17541564154530558120671)
                ·
                  rfl

theorem cell20_115297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 5].length) (baseStart_115297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115297 prefixEnd_115297 := by exact prefixLift 115297
  have htrace : WordTrace (prefixWord ++ tailWord_115297) baseStart_115297 baseEnd_115297 := by
    simpa [prefixWord, tailWord_115297, baseEnd_115297] using wordTrace_append hprefix tailTrace_115297
  have hstable : (prefixWord ++ tailWord_115297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115297).length < 2 ^ (prefixWord ++ tailWord_115297).sum := by decide
  have hdescent : baseEnd_115297 < baseStart_115297 := by decide
  rcases family_descends (prefixWord ++ tailWord_115297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115314 : List Nat := [3, 2, 1, 2, 4, 1, 3, 4]
def baseStart_115314 : Nat := 118140960795 + 115314 * 2 ^ 59
def prefixEnd_115314 : Nat := 4983230072969 + 3 ^ 40 * 115314 * 2
def baseEnd_115314 : Nat := 17544150575605056931759

theorem tailTrace_115314 : CollatzResearch.WordTrace tailWord_115314 prefixEnd_115314 17544150575605056931759 := by
  unfold tailWord_115314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1051461776061136727096249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2803898069496364605589997 1051461776061136727096249)
  ·
    refine ⟨788596332045852545322187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1051461776061136727096249 788596332045852545322187)
    ·
      refine ⟨1182894498068778817983281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 788596332045852545322187 1182894498068778817983281)
      ·
        refine ⟨887170873551584113487461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1182894498068778817983281 887170873551584113487461)
        ·
          refine ⟨166344538790922021278899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 887170873551584113487461 166344538790922021278899)
          ·
            refine ⟨249516808186383031918349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166344538790922021278899 249516808186383031918349)
            ·
              refine ⟨93568803069893636969381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249516808186383031918349 93568803069893636969381)
              ·
                refine ⟨17544150575605056931759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93568803069893636969381 17544150575605056931759)
                ·
                  rfl

theorem cell20_115314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_115314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115314 prefixEnd_115314 := by exact prefixLift 115314
  have htrace : WordTrace (prefixWord ++ tailWord_115314) baseStart_115314 baseEnd_115314 := by
    simpa [prefixWord, tailWord_115314, baseEnd_115314] using wordTrace_append hprefix tailTrace_115314
  have hstable : (prefixWord ++ tailWord_115314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115314).length < 2 ^ (prefixWord ++ tailWord_115314).sum := by decide
  have hdescent : baseEnd_115314 < baseStart_115314 := by decide
  rcases family_descends (prefixWord ++ tailWord_115314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115328 : List Nat := [2, 1, 1, 2, 1, 5, 1, 5, 2]
def baseStart_115328 : Nat := 118140960795 + 115328 * 2 ^ 59
def prefixEnd_115328 : Nat := 4983230072969 + 3 ^ 40 * 115328 * 2
def baseEnd_115328 : Nat := 52638841708293344328553

theorem tailTrace_115328 : CollatzResearch.WordTrace tailWord_115328 prefixEnd_115328 52638841708293344328553 := by
  unfold tailWord_115328
  simp only [CollatzResearch.WordTrace]
  refine ⟨2103178863096913649697319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2804238484129218199596425 2103178863096913649697319)
  ·
    refine ⟨3154768294645370474545979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2103178863096913649697319 3154768294645370474545979)
    ·
      refine ⟨4732152441968055711818969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3154768294645370474545979 4732152441968055711818969)
      ·
        refine ⟨3549114331476041783864227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4732152441968055711818969 3549114331476041783864227)
        ·
          refine ⟨5323671497214062675796341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3549114331476041783864227 5323671497214062675796341)
          ·
            refine ⟨499094202863818375855907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5323671497214062675796341 499094202863818375855907)
            ·
              refine ⟨748641304295727563783861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499094202863818375855907 748641304295727563783861)
              ·
                refine ⟨70185122277724459104737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 748641304295727563783861 70185122277724459104737)
                ·
                  refine ⟨52638841708293344328553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70185122277724459104737 52638841708293344328553)
                  ·
                    rfl

theorem cell20_115328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 2].length) (baseStart_115328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115328 prefixEnd_115328 := by exact prefixLift 115328
  have htrace : WordTrace (prefixWord ++ tailWord_115328) baseStart_115328 baseEnd_115328 := by
    simpa [prefixWord, tailWord_115328, baseEnd_115328] using wordTrace_append hprefix tailTrace_115328
  have hstable : (prefixWord ++ tailWord_115328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115328).length < 2 ^ (prefixWord ++ tailWord_115328).sum := by decide
  have hdescent : baseEnd_115328 < baseStart_115328 := by decide
  rcases family_descends (prefixWord ++ tailWord_115328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115338 : List Nat := [3, 1, 2, 3, 3, 2, 1, 2, 3]
def baseStart_115338 : Nat := 118140960795 + 115338 * 2 ^ 59
def prefixEnd_115338 : Nat := 4983230072969 + 3 ^ 40 * 115338 * 2
def baseEnd_115338 : Nat := 52643405980777753995179

theorem tailTrace_115338 : CollatzResearch.WordTrace tailWord_115338 prefixEnd_115338 52643405980777753995179 := by
  unfold tailWord_115338
  simp only [CollatzResearch.WordTrace]
  refine ⟨1051680614039399751814667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2804481637438399338172445 1051680614039399751814667)
  ·
    refine ⟨1577520921059099627722001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1051680614039399751814667 1577520921059099627722001)
    ·
      refine ⟨1183140690794324720791501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1577520921059099627722001 1183140690794324720791501)
      ·
        refine ⟨443677759047871770296813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1183140690794324720791501 443677759047871770296813)
        ·
          refine ⟨166379159642951913861305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 443677759047871770296813 166379159642951913861305)
          ·
            refine ⟨124784369732213935395979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166379159642951913861305 124784369732213935395979)
            ·
              refine ⟨187176554598320903093969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124784369732213935395979 187176554598320903093969)
              ·
                refine ⟨140382415948740677320477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187176554598320903093969 140382415948740677320477)
                ·
                  refine ⟨52643405980777753995179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140382415948740677320477 52643405980777753995179)
                  ·
                    rfl

theorem cell20_115338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_115338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115338 prefixEnd_115338 := by exact prefixLift 115338
  have htrace : WordTrace (prefixWord ++ tailWord_115338) baseStart_115338 baseEnd_115338 := by
    simpa [prefixWord, tailWord_115338, baseEnd_115338] using wordTrace_append hprefix tailTrace_115338
  have hstable : (prefixWord ++ tailWord_115338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115338).length < 2 ^ (prefixWord ++ tailWord_115338).sum := by decide
  have hdescent : baseEnd_115338 < baseStart_115338 := by decide
  rcases family_descends (prefixWord ++ tailWord_115338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115342 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_115342 : Nat := 118140960795 + 115342 * 2 ^ 59
def prefixEnd_115342 : Nat := 4983230072969 + 3 ^ 40 * 115342 * 2
def baseEnd_115342 : Nat := 52645231689771517861829

theorem tailTrace_115342 : CollatzResearch.WordTrace tailWord_115342 prefixEnd_115342 52645231689771517861829 := by
  unfold tailWord_115342
  simp only [CollatzResearch.WordTrace]
  refine ⟨525858543517888461300535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2804578898762071793602853 525858543517888461300535)
  ·
    refine ⟨788787815276832691950803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 525858543517888461300535 788787815276832691950803)
    ·
      refine ⟨1183181722915249037926205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 788787815276832691950803 1183181722915249037926205)
      ·
        refine ⟨443693146093218389222327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1183181722915249037926205 443693146093218389222327)
        ·
          refine ⟨665539719139827583833491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443693146093218389222327 665539719139827583833491)
          ·
            refine ⟨998309578709741375750237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665539719139827583833491 998309578709741375750237)
            ·
              refine ⟨374366092016153015906339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 998309578709741375750237 374366092016153015906339)
              ·
                refine ⟨561549138024229523859509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374366092016153015906339 561549138024229523859509)
                ·
                  refine ⟨52645231689771517861829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 561549138024229523859509 52645231689771517861829)
                  ·
                    rfl

theorem cell20_115342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_115342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115342 prefixEnd_115342 := by exact prefixLift 115342
  have htrace : WordTrace (prefixWord ++ tailWord_115342) baseStart_115342 baseEnd_115342 := by
    simpa [prefixWord, tailWord_115342, baseEnd_115342] using wordTrace_append hprefix tailTrace_115342
  have hstable : (prefixWord ++ tailWord_115342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115342).length < 2 ^ (prefixWord ++ tailWord_115342).sum := by decide
  have hdescent : baseEnd_115342 < baseStart_115342 := by decide
  rcases family_descends (prefixWord ++ tailWord_115342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115373 : List Nat := [1, 5, 2, 1, 1, 3, 1, 6]
def baseStart_115373 : Nat := 118140960795 + 115373 * 2 ^ 59
def prefixEnd_115373 : Nat := 4983230072969 + 3 ^ 40 * 115373 * 2
def baseEnd_115373 : Nat := 17553126978157729276123

theorem tailTrace_115373 : CollatzResearch.WordTrace tailWord_115373 prefixEnd_115373 17553126978157729276123 := by
  unfold tailWord_115373
  simp only [CollatzResearch.WordTrace]
  refine ⟨4207999011030799984782773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2805332674020533323188515 4207999011030799984782773)
  ·
    refine ⟨394499907284137498573385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4207999011030799984782773 394499907284137498573385)
    ·
      refine ⟨295874930463103123930039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394499907284137498573385 295874930463103123930039)
      ·
        refine ⟨443812395694654685895059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295874930463103123930039 443812395694654685895059)
        ·
          refine ⟨665718593541982028842589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443812395694654685895059 665718593541982028842589)
          ·
            refine ⟨249644472578243260815971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 665718593541982028842589 249644472578243260815971)
            ·
              refine ⟨374466708867364891223957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249644472578243260815971 374466708867364891223957)
              ·
                refine ⟨17553126978157729276123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 374466708867364891223957 17553126978157729276123)
                ·
                  rfl

theorem cell20_115373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 6].length) (baseStart_115373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115373 prefixEnd_115373 := by exact prefixLift 115373
  have htrace : WordTrace (prefixWord ++ tailWord_115373) baseStart_115373 baseEnd_115373 := by
    simpa [prefixWord, tailWord_115373, baseEnd_115373] using wordTrace_append hprefix tailTrace_115373
  have hstable : (prefixWord ++ tailWord_115373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115373).length < 2 ^ (prefixWord ++ tailWord_115373).sum := by decide
  have hdescent : baseEnd_115373 < baseStart_115373 := by decide
  rcases family_descends (prefixWord ++ tailWord_115373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115404 : List Nat := [2, 2, 1, 5, 1, 1, 3, 1, 4]
def baseStart_115404 : Nat := 118140960795 + 115404 * 2 ^ 59
def prefixEnd_115404 : Nat := 4983230072969 + 3 ^ 40 * 115404 * 2
def baseEnd_115404 : Nat := 52673530179174857794909

theorem tailTrace_115404 : CollatzResearch.WordTrace tailWord_115404 prefixEnd_115404 52673530179174857794909 := by
  unfold tailWord_115404
  simp only [CollatzResearch.WordTrace]
  refine ⟨2104564836959246139580633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2806086449278994852774177 2104564836959246139580633)
  ·
    refine ⟨1578423627719434604685475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2104564836959246139580633 1578423627719434604685475)
    ·
      refine ⟨2367635441579151907028213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1578423627719434604685475 2367635441579151907028213)
      ·
        refine ⟨221965822648045491283895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2367635441579151907028213 221965822648045491283895)
        ·
          refine ⟨332948733972068236925843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221965822648045491283895 332948733972068236925843)
          ·
            refine ⟨499423100958102355388765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332948733972068236925843 499423100958102355388765)
            ·
              refine ⟨187283662859288383270787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 499423100958102355388765 187283662859288383270787)
              ·
                refine ⟨280925494288932574906181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187283662859288383270787 280925494288932574906181)
                ·
                  refine ⟨52673530179174857794909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 280925494288932574906181 52673530179174857794909)
                  ·
                    rfl

theorem cell20_115404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_115404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115404 prefixEnd_115404 := by exact prefixLift 115404
  have htrace : WordTrace (prefixWord ++ tailWord_115404) baseStart_115404 baseEnd_115404 := by
    simpa [prefixWord, tailWord_115404, baseEnd_115404] using wordTrace_append hprefix tailTrace_115404
  have hstable : (prefixWord ++ tailWord_115404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115404).length < 2 ^ (prefixWord ++ tailWord_115404).sum := by decide
  have hdescent : baseEnd_115404 < baseStart_115404 := by decide
  rcases family_descends (prefixWord ++ tailWord_115404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115418 : List Nat := [3, 1, 1, 2, 2, 2, 3, 3, 3]
def baseStart_115418 : Nat := 118140960795 + 115418 * 2 ^ 59
def prefixEnd_115418 : Nat := 4983230072969 + 3 ^ 40 * 115418 * 2
def baseEnd_115418 : Nat := 52679920160653031328185

theorem tailTrace_115418 : CollatzResearch.WordTrace tailWord_115418 prefixEnd_115418 52679920160653031328185 := by
  unfold tailWord_115418
  simp only [CollatzResearch.WordTrace]
  refine ⟨1052410073966943167542727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2806426863911848446780605 1052410073966943167542727)
  ·
    refine ⟨1578615110950414751314091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1052410073966943167542727 1578615110950414751314091)
    ·
      refine ⟨2367922666425622126971137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1578615110950414751314091 2367922666425622126971137)
      ·
        refine ⟨1775941999819216595228353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2367922666425622126971137 1775941999819216595228353)
        ·
          refine ⟨1331956499864412446421265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1775941999819216595228353 1331956499864412446421265)
          ·
            refine ⟨998967374898309334815949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1331956499864412446421265 998967374898309334815949)
            ·
              refine ⟨374612765586866000555981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 998967374898309334815949 374612765586866000555981)
              ·
                refine ⟨140479787095074750208493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374612765586866000555981 140479787095074750208493)
                ·
                  refine ⟨52679920160653031328185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140479787095074750208493 52679920160653031328185)
                  ·
                    rfl

theorem cell20_115418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_115418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115418 prefixEnd_115418 := by exact prefixLift 115418
  have htrace : WordTrace (prefixWord ++ tailWord_115418) baseStart_115418 baseEnd_115418 := by
    simpa [prefixWord, tailWord_115418, baseEnd_115418] using wordTrace_append hprefix tailTrace_115418
  have hstable : (prefixWord ++ tailWord_115418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115418).length < 2 ^ (prefixWord ++ tailWord_115418).sum := by decide
  have hdescent : baseEnd_115418 < baseStart_115418 := by decide
  rcases family_descends (prefixWord ++ tailWord_115418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115445 : List Nat := [1, 3, 6, 1, 2, 7]
def baseStart_115445 : Nat := 118140960795 + 115445 * 2 ^ 59
def prefixEnd_115445 : Nat := 4983230072969 + 3 ^ 40 * 115445 * 2
def baseEnd_115445 : Nat := 1951564581346701386225

theorem tailTrace_115445 : CollatzResearch.WordTrace tailWord_115445 prefixEnd_115445 1951564581346701386225 := by
  unfold tailWord_115445
  simp only [CollatzResearch.WordTrace]
  refine ⟨4210625066769956281403789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2807083377846637520935859 4210625066769956281403789)
  ·
    refine ⟨1578984400038733605526421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4210625066769956281403789 1578984400038733605526421)
    ·
      refine ⟨74014893751815637759051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1578984400038733605526421 74014893751815637759051)
      ·
        refine ⟨111022340627723456638577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74014893751815637759051 111022340627723456638577)
        ·
          refine ⟨83266755470792592478933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111022340627723456638577 83266755470792592478933)
          ·
            refine ⟨1951564581346701386225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 83266755470792592478933 1951564581346701386225)
            ·
              rfl

theorem cell20_115445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 7].length) (baseStart_115445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115445 prefixEnd_115445 := by exact prefixLift 115445
  have htrace : WordTrace (prefixWord ++ tailWord_115445) baseStart_115445 baseEnd_115445 := by
    simpa [prefixWord, tailWord_115445, baseEnd_115445] using wordTrace_append hprefix tailTrace_115445
  have hstable : (prefixWord ++ tailWord_115445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115445).length < 2 ^ (prefixWord ++ tailWord_115445).sum := by decide
  have hdescent : baseEnd_115445 < baseStart_115445 := by decide
  rcases family_descends (prefixWord ++ tailWord_115445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115487 : List Nat := [1, 1, 2, 4, 2, 3, 3, 4]
def baseStart_115487 : Nat := 118140960795 + 115487 * 2 ^ 59
def prefixEnd_115487 : Nat := 4983230072969 + 3 ^ 40 * 115487 * 2
def baseEnd_115487 : Nat := 17570471213598486009301

theorem tailTrace_115487 : CollatzResearch.WordTrace tailWord_115487 prefixEnd_115487 17570471213598486009301 := by
  unfold tailWord_115487
  simp only [CollatzResearch.WordTrace]
  refine ⟨4212156932617797454432715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2808104621745198302955143 4212156932617797454432715)
  ·
    refine ⟨6318235398926696181649073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4212156932617797454432715 6318235398926696181649073)
    ·
      refine ⟨4738676549195022136236805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6318235398926696181649073 4738676549195022136236805)
      ·
        refine ⟨888501852974066650544401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4738676549195022136236805 888501852974066650544401)
        ·
          refine ⟨666376389730549987908301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 888501852974066650544401 666376389730549987908301)
          ·
            refine ⟨249891146148956245465613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 666376389730549987908301 249891146148956245465613)
            ·
              refine ⟨93709179805858592049605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249891146148956245465613 93709179805858592049605)
              ·
                refine ⟨17570471213598486009301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93709179805858592049605 17570471213598486009301)
                ·
                  rfl

theorem cell20_115487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 4].length) (baseStart_115487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115487 prefixEnd_115487 := by exact prefixLift 115487
  have htrace : WordTrace (prefixWord ++ tailWord_115487) baseStart_115487 baseEnd_115487 := by
    simpa [prefixWord, tailWord_115487, baseEnd_115487] using wordTrace_append hprefix tailTrace_115487
  have hstable : (prefixWord ++ tailWord_115487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115487).length < 2 ^ (prefixWord ++ tailWord_115487).sum := by decide
  have hdescent : baseEnd_115487 < baseStart_115487 := by decide
  rcases family_descends (prefixWord ++ tailWord_115487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115546 : List Nat := [3, 1, 1, 2, 1, 5, 1, 6]
def baseStart_115546 : Nat := 118140960795 + 115546 * 2 ^ 59
def prefixEnd_115546 : Nat := 4983230072969 + 3 ^ 40 * 115546 * 2
def baseEnd_115546 : Nat := 17579447616151158353665

theorem tailTrace_115546 : CollatzResearch.WordTrace tailWord_115546 prefixEnd_115546 17579447616151158353665 := by
  unfold tailWord_115546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1053577209851012632707623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2809539226269367020553661 1053577209851012632707623)
  ·
    refine ⟨1580365814776518949061435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1053577209851012632707623 1580365814776518949061435)
    ·
      refine ⟨2370548722164778423592153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1580365814776518949061435 2370548722164778423592153)
      ·
        refine ⟨1777911541623583817694115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2370548722164778423592153 1777911541623583817694115)
        ·
          refine ⟨2666867312435375726541173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1777911541623583817694115 2666867312435375726541173)
          ·
            refine ⟨250018810540816474363235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2666867312435375726541173 250018810540816474363235)
            ·
              refine ⟨375028215811224711544853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250018810540816474363235 375028215811224711544853)
              ·
                refine ⟨17579447616151158353665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 375028215811224711544853 17579447616151158353665)
                ·
                  rfl

theorem cell20_115546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_115546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115546 prefixEnd_115546 := by exact prefixLift 115546
  have htrace : WordTrace (prefixWord ++ tailWord_115546) baseStart_115546 baseEnd_115546 := by
    simpa [prefixWord, tailWord_115546, baseEnd_115546] using wordTrace_append hprefix tailTrace_115546
  have hstable : (prefixWord ++ tailWord_115546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115546).length < 2 ^ (prefixWord ++ tailWord_115546).sum := by decide
  have hdescent : baseEnd_115546 < baseStart_115546 := by decide
  rcases family_descends (prefixWord ++ tailWord_115546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115577 : List Nat := [1, 2, 1, 3, 2, 3, 3, 1, 4]
def baseStart_115577 : Nat := 118140960795 + 115577 * 2 ^ 59
def prefixEnd_115577 : Nat := 4983230072969 + 3 ^ 40 * 115577 * 2
def baseEnd_115577 : Nat := 52752492093155145027535

theorem tailTrace_115577 : CollatzResearch.WordTrace tailWord_115577 prefixEnd_115577 52752492093155145027535 := by
  unfold tailWord_115577
  simp only [CollatzResearch.WordTrace]
  refine ⟨4215439502291742825208985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2810293001527828550139323 4215439502291742825208985)
  ·
    refine ⟨3161579626718807118906739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4215439502291742825208985 3161579626718807118906739)
    ·
      refine ⟨4742369440078210678360109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3161579626718807118906739 4742369440078210678360109)
      ·
        refine ⟨1778388540029329004385041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4742369440078210678360109 1778388540029329004385041)
        ·
          refine ⟨1333791405021996753288781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1778388540029329004385041 1333791405021996753288781)
          ·
            refine ⟨500171776883248782483293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1333791405021996753288781 500171776883248782483293)
            ·
              refine ⟨187564416331218293431235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 500171776883248782483293 187564416331218293431235)
              ·
                refine ⟨281346624496827440146853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187564416331218293431235 281346624496827440146853)
                ·
                  refine ⟨52752492093155145027535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281346624496827440146853 52752492093155145027535)
                  ·
                    rfl

theorem cell20_115577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_115577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115577 prefixEnd_115577 := by exact prefixLift 115577
  have htrace : WordTrace (prefixWord ++ tailWord_115577) baseStart_115577 baseEnd_115577 := by
    simpa [prefixWord, tailWord_115577, baseEnd_115577] using wordTrace_append hprefix tailTrace_115577
  have hstable : (prefixWord ++ tailWord_115577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115577).length < 2 ^ (prefixWord ++ tailWord_115577).sum := by decide
  have hdescent : baseEnd_115577 < baseStart_115577 := by decide
  rcases family_descends (prefixWord ++ tailWord_115577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115646 : List Nat := [4, 2, 1, 1, 1, 2, 1, 5, 3]
def baseStart_115646 : Nat := 118140960795 + 115646 * 2 ^ 59
def prefixEnd_115646 : Nat := 4983230072969 + 3 ^ 40 * 115646 * 2
def baseEnd_115646 : Nat := 52783985573297571727253

theorem tailTrace_115646 : CollatzResearch.WordTrace tailWord_115646 prefixEnd_115646 52783985573297571727253 := by
  unfold tailWord_115646
  simp only [CollatzResearch.WordTrace]
  refine ⟨527244517380220951183849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2811970759361178406313861 527244517380220951183849)
  ·
    refine ⟨395433388035165713387887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 527244517380220951183849 395433388035165713387887)
    ·
      refine ⟨593150082052748570081831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395433388035165713387887 593150082052748570081831)
      ·
        refine ⟨889725123079122855122747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593150082052748570081831 889725123079122855122747)
        ·
          refine ⟨1334587684618684282684121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 889725123079122855122747 1334587684618684282684121)
          ·
            refine ⟨1000940763464013212013091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1334587684618684282684121 1000940763464013212013091)
            ·
              refine ⟨1501411145196019818019637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000940763464013212013091 1501411145196019818019637)
              ·
                refine ⟨140757294862126857939341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1501411145196019818019637 140757294862126857939341)
                ·
                  refine ⟨52783985573297571727253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140757294862126857939341 52783985573297571727253)
                  ·
                    rfl

theorem cell20_115646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_115646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115646 prefixEnd_115646 := by exact prefixLift 115646
  have htrace : WordTrace (prefixWord ++ tailWord_115646) baseStart_115646 baseEnd_115646 := by
    simpa [prefixWord, tailWord_115646, baseEnd_115646] using wordTrace_append hprefix tailTrace_115646
  have hstable : (prefixWord ++ tailWord_115646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115646).length < 2 ^ (prefixWord ++ tailWord_115646).sum := by decide
  have hdescent : baseEnd_115646 < baseStart_115646 := by decide
  rcases family_descends (prefixWord ++ tailWord_115646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115736 : List Nat := [2, 1, 2, 3, 2, 4, 6]
def baseStart_115736 : Nat := 118140960795 + 115736 * 2 ^ 59
def prefixEnd_115736 : Nat := 4983230072969 + 3 ^ 40 * 115736 * 2
def baseEnd_115736 : Nat := 5869451558406362080765

theorem tailTrace_115736 : CollatzResearch.WordTrace tailWord_115736 prefixEnd_115736 5869451558406362080765 := by
  unfold tailWord_115736
  simp only [CollatzResearch.WordTrace]
  refine ⟨2110619354357856490123531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2814159139143808653498041 2110619354357856490123531)
  ·
    refine ⟨3165929031536784735185297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2110619354357856490123531 3165929031536784735185297)
    ·
      refine ⟨2374446773652588551388973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3165929031536784735185297 2374446773652588551388973)
      ·
        refine ⟨890417540119720706770865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2374446773652588551388973 890417540119720706770865)
        ·
          refine ⟨667813155089790530078149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 890417540119720706770865 667813155089790530078149)
          ·
            refine ⟨125214966579335724389653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 667813155089790530078149 125214966579335724389653)
            ·
              refine ⟨5869451558406362080765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 125214966579335724389653 5869451558406362080765)
              ·
                rfl

theorem cell20_115736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 6].length) (baseStart_115736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115736 prefixEnd_115736 := by exact prefixLift 115736
  have htrace : WordTrace (prefixWord ++ tailWord_115736) baseStart_115736 baseEnd_115736 := by
    simpa [prefixWord, tailWord_115736, baseEnd_115736] using wordTrace_append hprefix tailTrace_115736
  have hstable : (prefixWord ++ tailWord_115736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115736).length < 2 ^ (prefixWord ++ tailWord_115736).sum := by decide
  have hdescent : baseEnd_115736 < baseStart_115736 := by decide
  rcases family_descends (prefixWord ++ tailWord_115736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115743 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 5]
def baseStart_115743 : Nat := 118140960795 + 115743 * 2 ^ 59
def prefixEnd_115743 : Nat := 4983230072969 + 3 ^ 40 * 115743 * 2
def baseEnd_115743 : Nat := 52828259016396345493523

theorem tailTrace_115743 : CollatzResearch.WordTrace tailWord_115743 prefixEnd_115743 52828259016396345493523 := by
  unfold tailWord_115743
  simp only [CollatzResearch.WordTrace]
  refine ⟨4221494019690353175751883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2814329346460235450501255 4221494019690353175751883)
  ·
    refine ⟨6332241029535529763627825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4221494019690353175751883 6332241029535529763627825)
    ·
      refine ⟨4749180772151647322720869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6332241029535529763627825 4749180772151647322720869)
      ·
        refine ⟨890471394778433873010163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4749180772151647322720869 890471394778433873010163)
        ·
          refine ⟨1335707092167650809515245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890471394778433873010163 1335707092167650809515245)
          ·
            refine ⟨500890159562869053568217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1335707092167650809515245 500890159562869053568217)
            ·
              refine ⟨375667619672151790176163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500890159562869053568217 375667619672151790176163)
              ·
                refine ⟨563501429508227685264245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375667619672151790176163 563501429508227685264245)
                ·
                  refine ⟨52828259016396345493523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 563501429508227685264245 52828259016396345493523)
                  ·
                    rfl

theorem cell20_115743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 5].length) (baseStart_115743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115743 prefixEnd_115743 := by exact prefixLift 115743
  have htrace : WordTrace (prefixWord ++ tailWord_115743) baseStart_115743 baseEnd_115743 := by
    simpa [prefixWord, tailWord_115743, baseEnd_115743] using wordTrace_append hprefix tailTrace_115743
  have hstable : (prefixWord ++ tailWord_115743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115743).length < 2 ^ (prefixWord ++ tailWord_115743).sum := by decide
  have hdescent : baseEnd_115743 < baseStart_115743 := by decide
  rcases family_descends (prefixWord ++ tailWord_115743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115746 : List Nat := [3, 3, 1, 1, 1, 5, 1, 1, 4]
def baseStart_115746 : Nat := 118140960795 + 115746 * 2 ^ 59
def prefixEnd_115746 : Nat := 4983230072969 + 3 ^ 40 * 115746 * 2
def baseEnd_115746 : Nat := 52829628298141668393511

theorem tailTrace_115746 : CollatzResearch.WordTrace tailWord_115746 prefixEnd_115746 52829628298141668393511 := by
  unfold tailWord_115746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1055400859669871172027773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2814402292452989792074061 1055400859669871172027773)
  ·
    refine ⟨395775322376201689510415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1055400859669871172027773 395775322376201689510415)
    ·
      refine ⟨593662983564302534265623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395775322376201689510415 593662983564302534265623)
      ·
        refine ⟨890494475346453801398435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593662983564302534265623 890494475346453801398435)
        ·
          refine ⟨1335741713019680702097653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890494475346453801398435 1335741713019680702097653)
          ·
            refine ⟨125225785595595065821655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1335741713019680702097653 125225785595595065821655)
            ·
              refine ⟨187838678393392598732483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125225785595595065821655 187838678393392598732483)
              ·
                refine ⟨281758017590088898098725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187838678393392598732483 281758017590088898098725)
                ·
                  refine ⟨52829628298141668393511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281758017590088898098725 52829628298141668393511)
                  ·
                    rfl

theorem cell20_115746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_115746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115746 prefixEnd_115746 := by exact prefixLift 115746
  have htrace : WordTrace (prefixWord ++ tailWord_115746) baseStart_115746 baseEnd_115746 := by
    simpa [prefixWord, tailWord_115746, baseEnd_115746] using wordTrace_append hprefix tailTrace_115746
  have hstable : (prefixWord ++ tailWord_115746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115746).length < 2 ^ (prefixWord ++ tailWord_115746).sum := by decide
  have hdescent : baseEnd_115746 < baseStart_115746 := by decide
  rcases family_descends (prefixWord ++ tailWord_115746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115870 : List Nat := [4, 3, 1, 1, 2, 2, 3, 1, 3]
def baseStart_115870 : Nat := 118140960795 + 115870 * 2 ^ 59
def prefixEnd_115870 : Nat := 4983230072969 + 3 ^ 40 * 115870 * 2
def baseEnd_115870 : Nat := 52886225276948348259671

theorem tailTrace_115870 : CollatzResearch.WordTrace tailWord_115870 prefixEnd_115870 52886225276948348259671 := by
  unfold tailWord_115870
  simp only [CollatzResearch.WordTrace]
  refine ⟨528265761278781733203133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2817417393486835910416709 528265761278781733203133)
  ·
    refine ⟨198099660479543149951175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 528265761278781733203133 198099660479543149951175)
    ·
      refine ⟨297149490719314724926763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198099660479543149951175 297149490719314724926763)
      ·
        refine ⟨445724236078972087390145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297149490719314724926763 445724236078972087390145)
        ·
          refine ⟨334293177059229065542609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445724236078972087390145 334293177059229065542609)
          ·
            refine ⟨250719882794421799156957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334293177059229065542609 250719882794421799156957)
            ·
              refine ⟨94019956047908174683859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250719882794421799156957 94019956047908174683859)
              ·
                refine ⟨141029934071862262025789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94019956047908174683859 141029934071862262025789)
                ·
                  refine ⟨52886225276948348259671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141029934071862262025789 52886225276948348259671)
                  ·
                    rfl

theorem cell20_115870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_115870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115870 prefixEnd_115870 := by exact prefixLift 115870
  have htrace : WordTrace (prefixWord ++ tailWord_115870) baseStart_115870 baseEnd_115870 := by
    simpa [prefixWord, tailWord_115870, baseEnd_115870] using wordTrace_append hprefix tailTrace_115870
  have hstable : (prefixWord ++ tailWord_115870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115870).length < 2 ^ (prefixWord ++ tailWord_115870).sum := by decide
  have hdescent : baseEnd_115870 < baseStart_115870 := by decide
  rcases family_descends (prefixWord ++ tailWord_115870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115905 : List Nat := [1, 2, 6, 1, 1, 3, 6]
def baseStart_115905 : Nat := 118140960795 + 115905 * 2 ^ 59
def prefixEnd_115905 : Nat := 4983230072969 + 3 ^ 40 * 115905 * 2
def baseEnd_115905 : Nat := 5878022247849309121429

theorem tailTrace_115905 : CollatzResearch.WordTrace tailWord_115905 prefixEnd_115905 5878022247849309121429 := by
  unfold tailWord_115905
  simp only [CollatzResearch.WordTrace]
  refine ⟨4227402645103454843149169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2818268430068969895432779 4227402645103454843149169)
  ·
    refine ⟨3170551983827591132361877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4227402645103454843149169 3170551983827591132361877)
    ·
      refine ⟨148619624241918334329463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3170551983827591132361877 148619624241918334329463)
      ·
        refine ⟨222929436362877501494195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148619624241918334329463 222929436362877501494195)
        ·
          refine ⟨334394154544316252241293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222929436362877501494195 334394154544316252241293)
          ·
            refine ⟨125397807954118594590485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334394154544316252241293 125397807954118594590485)
            ·
              refine ⟨5878022247849309121429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 125397807954118594590485 5878022247849309121429)
              ·
                rfl

theorem cell20_115905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 6].length) (baseStart_115905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115905 prefixEnd_115905 := by exact prefixLift 115905
  have htrace : WordTrace (prefixWord ++ tailWord_115905) baseStart_115905 baseEnd_115905 := by
    simpa [prefixWord, tailWord_115905, baseEnd_115905] using wordTrace_append hprefix tailTrace_115905
  have hstable : (prefixWord ++ tailWord_115905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115905).length < 2 ^ (prefixWord ++ tailWord_115905).sum := by decide
  have hdescent : baseEnd_115905 < baseStart_115905 := by decide
  rcases family_descends (prefixWord ++ tailWord_115905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115940 : List Nat := [2, 3, 1, 1, 1, 2, 2, 4, 4]
def baseStart_115940 : Nat := 118140960795 + 115940 * 2 ^ 59
def prefixEnd_115940 : Nat := 4983230072969 + 3 ^ 40 * 115940 * 2
def baseEnd_115940 : Nat := 52918175184339215926051

theorem tailTrace_115940 : CollatzResearch.WordTrace tailWord_115940 prefixEnd_115940 52918175184339215926051 := by
  unfold tailWord_115940
  simp only [CollatzResearch.WordTrace]
  refine ⟨2114339599988327910336637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2819119466651103880448849 2114339599988327910336637)
  ·
    refine ⟨792877349995622966376239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2114339599988327910336637 792877349995622966376239)
    ·
      refine ⟨1189316024993434449564359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 792877349995622966376239 1189316024993434449564359)
      ·
        refine ⟨1783974037490151674346539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1189316024993434449564359 1783974037490151674346539)
        ·
          refine ⟨2675961056235227511519809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1783974037490151674346539 2675961056235227511519809)
          ·
            refine ⟨2006970792176420633639857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2675961056235227511519809 2006970792176420633639857)
            ·
              refine ⟨1505228094132315475229893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2006970792176420633639857 1505228094132315475229893)
              ·
                refine ⟨282230267649809151605605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1505228094132315475229893 282230267649809151605605)
                ·
                  refine ⟨52918175184339215926051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 282230267649809151605605 52918175184339215926051)
                  ·
                    rfl

theorem cell20_115940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_115940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115940 prefixEnd_115940 := by exact prefixLift 115940
  have htrace : WordTrace (prefixWord ++ tailWord_115940) baseStart_115940 baseEnd_115940 := by
    simpa [prefixWord, tailWord_115940, baseEnd_115940] using wordTrace_append hprefix tailTrace_115940
  have hstable : (prefixWord ++ tailWord_115940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115940).length < 2 ^ (prefixWord ++ tailWord_115940).sum := by decide
  have hdescent : baseEnd_115940 < baseStart_115940 := by decide
  rcases family_descends (prefixWord ++ tailWord_115940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115947 : List Nat := [1, 1, 1, 1, 2, 6, 2, 6]
def baseStart_115947 : Nat := 118140960795 + 115947 * 2 ^ 59
def prefixEnd_115947 : Nat := 4983230072969 + 3 ^ 40 * 115947 * 2
def baseEnd_115947 : Nat := 17640456725026100897563

theorem tailTrace_115947 : CollatzResearch.WordTrace tailWord_115947 prefixEnd_115947 17640456725026100897563 := by
  unfold tailWord_115947
  simp only [CollatzResearch.WordTrace]
  refine ⟨4228934510951296016178095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2819289673967530677452063 4228934510951296016178095)
  ·
    refine ⟨6343401766426944024267143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4228934510951296016178095 6343401766426944024267143)
    ·
      refine ⟨9515102649640416036400715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6343401766426944024267143 9515102649640416036400715)
      ·
        refine ⟨14272653974460624054601073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9515102649640416036400715 14272653974460624054601073)
        ·
          refine ⟨10704490480845468040950805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14272653974460624054601073 10704490480845468040950805)
          ·
            refine ⟨501772991289631314419569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10704490480845468040950805 501772991289631314419569)
            ·
              refine ⟨376329743467223485814677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501772991289631314419569 376329743467223485814677)
              ·
                refine ⟨17640456725026100897563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 376329743467223485814677 17640456725026100897563)
                ·
                  rfl

theorem cell20_115947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 6].length) (baseStart_115947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115947 prefixEnd_115947 := by exact prefixLift 115947
  have htrace : WordTrace (prefixWord ++ tailWord_115947) baseStart_115947 baseEnd_115947 := by
    simpa [prefixWord, tailWord_115947, baseEnd_115947] using wordTrace_append hprefix tailTrace_115947
  have hstable : (prefixWord ++ tailWord_115947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115947).length < 2 ^ (prefixWord ++ tailWord_115947).sum := by decide
  have hdescent : baseEnd_115947 < baseStart_115947 := by decide
  rcases family_descends (prefixWord ++ tailWord_115947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115964 : List Nat := [2, 2, 2, 1, 6, 7]
def baseStart_115964 : Nat := 118140960795 + 115964 * 2 ^ 59
def prefixEnd_115964 : Nat := 4983230072969 + 3 ^ 40 * 115964 * 2
def baseEnd_115964 : Nat := 1960338127344511078739

theorem tailTrace_115964 : CollatzResearch.WordTrace tailWord_115964 prefixEnd_115964 1960338127344511078739 := by
  unfold tailWord_115964
  simp only [CollatzResearch.WordTrace]
  refine ⟨2114777275944853959773473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2819703034593138613031297 2114777275944853959773473)
  ·
    refine ⟨1586082956958640469830105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2114777275944853959773473 1586082956958640469830105)
    ·
      refine ⟨1189562217718980352372579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1586082956958640469830105 1189562217718980352372579)
      ·
        refine ⟨1784343326578470528558869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1189562217718980352372579 1784343326578470528558869)
        ·
          refine ⟨83641093433365806026197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1784343326578470528558869 83641093433365806026197)
          ·
            refine ⟨1960338127344511078739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 83641093433365806026197 1960338127344511078739)
            ·
              rfl

theorem cell20_115964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 7].length) (baseStart_115964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115964 prefixEnd_115964 := by exact prefixLift 115964
  have htrace : WordTrace (prefixWord ++ tailWord_115964) baseStart_115964 baseEnd_115964 := by
    simpa [prefixWord, tailWord_115964, baseEnd_115964] using wordTrace_append hprefix tailTrace_115964
  have hstable : (prefixWord ++ tailWord_115964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115964).length < 2 ^ (prefixWord ++ tailWord_115964).sum := by decide
  have hdescent : baseEnd_115964 < baseStart_115964 := by decide
  rcases family_descends (prefixWord ++ tailWord_115964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115971 : List Nat := [1, 1, 1, 3, 2, 4, 1, 4, 3]
def baseStart_115971 : Nat := 118140960795 + 115971 * 2 ^ 59
def prefixEnd_115971 : Nat := 4983230072969 + 3 ^ 40 * 115971 * 2
def baseEnd_115971 : Nat := 52932324429040885892591

theorem tailTrace_115971 : CollatzResearch.WordTrace tailWord_115971 prefixEnd_115971 52932324429040885892591 := by
  unfold tailWord_115971
  simp only [CollatzResearch.WordTrace]
  refine ⟨4229809862864348115051767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2819873241909565410034511 4229809862864348115051767)
  ·
    refine ⟨6344714794296522172577651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4229809862864348115051767 6344714794296522172577651)
    ·
      refine ⟨9517072191444783258866477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6344714794296522172577651 9517072191444783258866477)
      ·
        refine ⟨3568902071791793722074929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9517072191444783258866477 3568902071791793722074929)
        ·
          refine ⟨2676676553843845291556197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3568902071791793722074929 2676676553843845291556197)
          ·
            refine ⟨501876853845720992166787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2676676553843845291556197 501876853845720992166787)
            ·
              refine ⟨752815280768581488250181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501876853845720992166787 752815280768581488250181)
              ·
                refine ⟨141152865144109029046909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 752815280768581488250181 141152865144109029046909)
                ·
                  refine ⟨52932324429040885892591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141152865144109029046909 52932324429040885892591)
                  ·
                    rfl

theorem cell20_115971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 3].length) (baseStart_115971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115971 prefixEnd_115971 := by exact prefixLift 115971
  have htrace : WordTrace (prefixWord ++ tailWord_115971) baseStart_115971 baseEnd_115971 := by
    simpa [prefixWord, tailWord_115971, baseEnd_115971] using wordTrace_append hprefix tailTrace_115971
  have hstable : (prefixWord ++ tailWord_115971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115971).length < 2 ^ (prefixWord ++ tailWord_115971).sum := by decide
  have hdescent : baseEnd_115971 < baseStart_115971 := by decide
  rcases family_descends (prefixWord ++ tailWord_115971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115978 : List Nat := [3, 1, 2, 2, 1, 1, 1, 5, 4]
def baseStart_115978 : Nat := 118140960795 + 115978 * 2 ^ 59
def prefixEnd_115978 : Nat := 4983230072969 + 3 ^ 40 * 115978 * 2
def baseEnd_115978 : Nat := 52935519419779972659229

theorem tailTrace_115978 : CollatzResearch.WordTrace tailWord_115978 prefixEnd_115978 52935519419779972659229 := by
  unfold tailWord_115978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1057516293459747077639147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2820043449225992207037725 1057516293459747077639147)
  ·
    refine ⟨1586274440189620616458721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1057516293459747077639147 1586274440189620616458721)
    ·
      refine ⟨1189705830142215462344041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1586274440189620616458721 1189705830142215462344041)
      ·
        refine ⟨892279372606661596758031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1189705830142215462344041 892279372606661596758031)
        ·
          refine ⟨1338419058909992395137047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892279372606661596758031 1338419058909992395137047)
          ·
            refine ⟨2007628588364988592705571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338419058909992395137047 2007628588364988592705571)
            ·
              refine ⟨3011442882547482889058357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2007628588364988592705571 3011442882547482889058357)
              ·
                refine ⟨282322770238826520849221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3011442882547482889058357 282322770238826520849221)
                ·
                  refine ⟨52935519419779972659229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 282322770238826520849221 52935519419779972659229)
                  ·
                    rfl

theorem cell20_115978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_115978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_115978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_115978 prefixEnd_115978 := by exact prefixLift 115978
  have htrace : WordTrace (prefixWord ++ tailWord_115978) baseStart_115978 baseEnd_115978 := by
    simpa [prefixWord, tailWord_115978, baseEnd_115978] using wordTrace_append hprefix tailTrace_115978
  have hstable : (prefixWord ++ tailWord_115978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115978).length < 2 ^ (prefixWord ++ tailWord_115978).sum := by decide
  have hdescent : baseEnd_115978 < baseStart_115978 := by decide
  rcases family_descends (prefixWord ++ tailWord_115978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116033 : List Nat := [1, 2, 5, 2, 1, 1, 1, 3, 4]
def baseStart_116033 : Nat := 118140960795 + 116033 * 2 ^ 59
def prefixEnd_116033 : Nat := 4983230072969 + 3 ^ 40 * 116033 * 2
def baseEnd_116033 : Nat := 52960622918444225825671

theorem tailTrace_116033 : CollatzResearch.WordTrace tailWord_116033 prefixEnd_116033 52960622918444225825671 := by
  unfold tailWord_116033
  simp only [CollatzResearch.WordTrace]
  refine ⟨4232071188639732703808753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2821380792426488469205835 4232071188639732703808753)
  ·
    refine ⟨3174053391479799527856565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4232071188639732703808753 3174053391479799527856565)
    ·
      refine ⟨297567505451231205736553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3174053391479799527856565 297567505451231205736553)
      ·
        refine ⟨223175629088423404302415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297567505451231205736553 223175629088423404302415)
        ·
          refine ⟨334763443632635106453623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223175629088423404302415 334763443632635106453623)
          ·
            refine ⟨502145165448952659680435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334763443632635106453623 502145165448952659680435)
            ·
              refine ⟨753217748173428989520653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502145165448952659680435 753217748173428989520653)
              ·
                refine ⟨282456655565035871070245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 753217748173428989520653 282456655565035871070245)
                ·
                  refine ⟨52960622918444225825671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 282456655565035871070245 52960622918444225825671)
                  ·
                    rfl

theorem cell20_116033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_116033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116033 prefixEnd_116033 := by exact prefixLift 116033
  have htrace : WordTrace (prefixWord ++ tailWord_116033) baseStart_116033 baseEnd_116033 := by
    simpa [prefixWord, tailWord_116033, baseEnd_116033] using wordTrace_append hprefix tailTrace_116033
  have hstable : (prefixWord ++ tailWord_116033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116033).length < 2 ^ (prefixWord ++ tailWord_116033).sum := by decide
  have hdescent : baseEnd_116033 < baseStart_116033 := by decide
  rcases family_descends (prefixWord ++ tailWord_116033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116094 : List Nat := [4, 2, 3, 2, 2, 1, 2, 1, 3]
def baseStart_116094 : Nat := 118140960795 + 116094 * 2 ^ 59
def prefixEnd_116094 : Nat := 4983230072969 + 3 ^ 40 * 116094 * 2
def baseEnd_116094 : Nat := 52988464980599124792089

theorem tailTrace_116094 : CollatzResearch.WordTrace tailWord_116094 prefixEnd_116094 52988464980599124792089 := by
  unfold tailWord_116094
  simp only [CollatzResearch.WordTrace]
  refine ⟨529287005177342515222417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2822864027612493414519557 529287005177342515222417)
  ·
    refine ⟨396965253883006886416813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 529287005177342515222417 396965253883006886416813)
    ·
      refine ⟨148861970206127582406305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 396965253883006886416813 148861970206127582406305)
      ·
        refine ⟨111646477654595686804729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148861970206127582406305 111646477654595686804729)
        ·
          refine ⟨83734858240946765103547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111646477654595686804729 83734858240946765103547)
          ·
            refine ⟨125602287361420147655321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83734858240946765103547 125602287361420147655321)
            ·
              refine ⟨94201715521065110741491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125602287361420147655321 94201715521065110741491)
              ·
                refine ⟨141302573281597666112237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94201715521065110741491 141302573281597666112237)
                ·
                  refine ⟨52988464980599124792089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141302573281597666112237 52988464980599124792089)
                  ·
                    rfl

theorem cell20_116094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_116094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116094 prefixEnd_116094 := by exact prefixLift 116094
  have htrace : WordTrace (prefixWord ++ tailWord_116094) baseStart_116094 baseEnd_116094 := by
    simpa [prefixWord, tailWord_116094, baseEnd_116094] using wordTrace_append hprefix tailTrace_116094
  have hstable : (prefixWord ++ tailWord_116094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116094).length < 2 ^ (prefixWord ++ tailWord_116094).sum := by decide
  have hdescent : baseEnd_116094 < baseStart_116094 := by decide
  rcases family_descends (prefixWord ++ tailWord_116094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116098 : List Nat := [3, 4, 2, 1, 1, 1, 4, 1, 3]
def baseStart_116098 : Nat := 118140960795 + 116098 * 2 ^ 59
def prefixEnd_116098 : Nat := 4983230072969 + 3 ^ 40 * 116098 * 2
def baseEnd_116098 : Nat := 52990290689592888658739

theorem tailTrace_116098 : CollatzResearch.WordTrace tailWord_116098 prefixEnd_116098 52990290689592888658739 := by
  unfold tailWord_116098
  simp only [CollatzResearch.WordTrace]
  refine ⟨1058610483351062201231237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2822961288936165869949965 1058610483351062201231237)
  ·
    refine ⟨198489465628324162730857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1058610483351062201231237 198489465628324162730857)
    ·
      refine ⟨148867099221243122048143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198489465628324162730857 148867099221243122048143)
      ·
        refine ⟨223300648831864683072215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148867099221243122048143 223300648831864683072215)
        ·
          refine ⟨334950973247797024608323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223300648831864683072215 334950973247797024608323)
          ·
            refine ⟨502426459871695536912485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334950973247797024608323 502426459871695536912485)
            ·
              refine ⟨94204961225942913171091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 502426459871695536912485 94204961225942913171091)
              ·
                refine ⟨141307441838914369756637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94204961225942913171091 141307441838914369756637)
                ·
                  refine ⟨52990290689592888658739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141307441838914369756637 52990290689592888658739)
                  ·
                    rfl

theorem cell20_116098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_116098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116098 prefixEnd_116098 := by exact prefixLift 116098
  have htrace : WordTrace (prefixWord ++ tailWord_116098) baseStart_116098 baseEnd_116098 := by
    simpa [prefixWord, tailWord_116098, baseEnd_116098] using wordTrace_append hprefix tailTrace_116098
  have hstable : (prefixWord ++ tailWord_116098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116098).length < 2 ^ (prefixWord ++ tailWord_116098).sum := by decide
  have hdescent : baseEnd_116098 < baseStart_116098 := by decide
  rcases family_descends (prefixWord ++ tailWord_116098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116099 : List Nat := [1, 1, 1, 3, 5, 1, 1, 7]
def baseStart_116099 : Nat := 118140960795 + 116099 * 2 ^ 59
def prefixEnd_116099 : Nat := 4983230072969 + 3 ^ 40 * 116099 * 2
def baseEnd_116099 : Nat := 17663582372280443208467

theorem tailTrace_116099 : CollatzResearch.WordTrace tailWord_116099 prefixEnd_116099 17663582372280443208467 := by
  unfold tailWord_116099
  simp only [CollatzResearch.WordTrace]
  refine ⟨4234478406400625975711351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2822985604267083983807567 4234478406400625975711351)
  ·
    refine ⟨6351717609600938963567027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4234478406400625975711351 6351717609600938963567027)
    ·
      refine ⟨9527576414401408445350541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6351717609600938963567027 9527576414401408445350541)
      ·
        refine ⟨3572841155400528167006453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9527576414401408445350541 3572841155400528167006453)
        ·
          refine ⟨334953858318799515656855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3572841155400528167006453 334953858318799515656855)
          ·
            refine ⟨502430787478199273485283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334953858318799515656855 502430787478199273485283)
            ·
              refine ⟨753646181217298910227925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502430787478199273485283 753646181217298910227925)
              ·
                refine ⟨17663582372280443208467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 753646181217298910227925 17663582372280443208467)
                ·
                  rfl

theorem cell20_116099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 7].length) (baseStart_116099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116099 prefixEnd_116099 := by exact prefixLift 116099
  have htrace : WordTrace (prefixWord ++ tailWord_116099) baseStart_116099 baseEnd_116099 := by
    simpa [prefixWord, tailWord_116099, baseEnd_116099] using wordTrace_append hprefix tailTrace_116099
  have hstable : (prefixWord ++ tailWord_116099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116099).length < 2 ^ (prefixWord ++ tailWord_116099).sum := by decide
  have hdescent : baseEnd_116099 < baseStart_116099 := by decide
  rcases family_descends (prefixWord ++ tailWord_116099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116116 : List Nat := [2, 4, 2, 1, 2, 1, 2, 6]
def baseStart_116116 : Nat := 118140960795 + 116116 * 2 ^ 59
def prefixEnd_116116 : Nat := 4983230072969 + 3 ^ 40 * 116116 * 2
def baseEnd_116116 : Nat := 17666168793354942019555

theorem tailTrace_116116 : CollatzResearch.WordTrace tailWord_116116 prefixEnd_116116 17666168793354942019555 := by
  unfold tailWord_116116
  simp only [CollatzResearch.WordTrace]
  refine ⟨2117549223669518939540101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2823398964892691919386801 2117549223669518939540101)
  ·
    refine ⟨397040479438034801163769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2117549223669518939540101 397040479438034801163769)
    ·
      refine ⟨297780359578526100872827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397040479438034801163769 297780359578526100872827)
      ·
        refine ⟨446670539367789151309241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297780359578526100872827 446670539367789151309241)
        ·
          refine ⟨335002904525841863481931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446670539367789151309241 335002904525841863481931)
          ·
            refine ⟨502504356788762795222897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335002904525841863481931 502504356788762795222897)
            ·
              refine ⟨376878267591572096417173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 502504356788762795222897 376878267591572096417173)
              ·
                refine ⟨17666168793354942019555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 376878267591572096417173 17666168793354942019555)
                ·
                  rfl

theorem cell20_116116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_116116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116116 prefixEnd_116116 := by exact prefixLift 116116
  have htrace : WordTrace (prefixWord ++ tailWord_116116) baseStart_116116 baseEnd_116116 := by
    simpa [prefixWord, tailWord_116116, baseEnd_116116] using wordTrace_append hprefix tailTrace_116116
  have hstable : (prefixWord ++ tailWord_116116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116116).length < 2 ^ (prefixWord ++ tailWord_116116).sum := by decide
  have hdescent : baseEnd_116116 < baseStart_116116 := by decide
  rcases family_descends (prefixWord ++ tailWord_116116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116168 : List Nat := [2, 1, 3, 1, 3, 1, 3, 2, 4]
def baseStart_116168 : Nat := 118140960795 + 116168 * 2 ^ 59
def prefixEnd_116168 : Nat := 4983230072969 + 3 ^ 40 * 116168 * 2
def baseEnd_116168 : Nat := 53022240596983756325119

theorem tailTrace_116168 : CollatzResearch.WordTrace tailWord_116168 prefixEnd_116168 53022240596983756325119 := by
  unfold tailWord_116168
  simp only [CollatzResearch.WordTrace]
  refine ⟨2118497521575325379986579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2824663362100433839982105 2118497521575325379986579)
  ·
    refine ⟨3177746282362988069979869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2118497521575325379986579 3177746282362988069979869)
    ·
      refine ⟨1191654855886120526242451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3177746282362988069979869 1191654855886120526242451)
      ·
        refine ⟨1787482283829180789363677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1191654855886120526242451 1787482283829180789363677)
        ·
          refine ⟨670305856435942796011379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1787482283829180789363677 670305856435942796011379)
          ·
            refine ⟨1005458784653914194017069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670305856435942796011379 1005458784653914194017069)
            ·
              refine ⟨377047044245217822756401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1005458784653914194017069 377047044245217822756401)
              ·
                refine ⟨282785283183913367067301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377047044245217822756401 282785283183913367067301)
                ·
                  refine ⟨53022240596983756325119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 282785283183913367067301 53022240596983756325119)
                  ·
                    rfl

theorem cell20_116168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_116168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116168 prefixEnd_116168 := by exact prefixLift 116168
  have htrace : WordTrace (prefixWord ++ tailWord_116168) baseStart_116168 baseEnd_116168 := by
    simpa [prefixWord, tailWord_116168, baseEnd_116168] using wordTrace_append hprefix tailTrace_116168
  have hstable : (prefixWord ++ tailWord_116168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116168).length < 2 ^ (prefixWord ++ tailWord_116168).sum := by decide
  have hdescent : baseEnd_116168 < baseStart_116168 := by decide
  rcases family_descends (prefixWord ++ tailWord_116168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116185 : List Nat := [1, 2, 1, 2, 4, 2, 1, 5, 2]
def baseStart_116185 : Nat := 118140960795 + 116185 * 2 ^ 59
def prefixEnd_116185 : Nat := 4983230072969 + 3 ^ 40 * 116185 * 2
def baseEnd_116185 : Nat := 53029999860207252758383

theorem tailTrace_116185 : CollatzResearch.WordTrace tailWord_116185 prefixEnd_116185 53029999860207252758383 := by
  unfold tailWord_116185
  simp only [CollatzResearch.WordTrace]
  refine ⟨4237615084089062663342009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2825076722726041775561339 4237615084089062663342009)
  ·
    refine ⟨3178211313066796997506507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4237615084089062663342009 3178211313066796997506507)
    ·
      refine ⟨4767316969600195496259761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3178211313066796997506507 4767316969600195496259761)
      ·
        refine ⟨3575487727200146622194821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4767316969600195496259761 3575487727200146622194821)
        ·
          refine ⟨670403948850027491661529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3575487727200146622194821 670403948850027491661529)
          ·
            refine ⟨502802961637520618746147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670403948850027491661529 502802961637520618746147)
            ·
              refine ⟨754204442456280928119221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502802961637520618746147 754204442456280928119221)
              ·
                refine ⟨70706666480276337011177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 754204442456280928119221 70706666480276337011177)
                ·
                  refine ⟨53029999860207252758383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70706666480276337011177 53029999860207252758383)
                  ·
                    rfl

theorem cell20_116185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 2].length) (baseStart_116185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116185 prefixEnd_116185 := by exact prefixLift 116185
  have htrace : WordTrace (prefixWord ++ tailWord_116185) baseStart_116185 baseEnd_116185 := by
    simpa [prefixWord, tailWord_116185, baseEnd_116185] using wordTrace_append hprefix tailTrace_116185
  have hstable : (prefixWord ++ tailWord_116185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116185).length < 2 ^ (prefixWord ++ tailWord_116185).sum := by decide
  have hdescent : baseEnd_116185 < baseStart_116185 := by decide
  rcases family_descends (prefixWord ++ tailWord_116185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116199 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 5]
def baseStart_116199 : Nat := 118140960795 + 116199 * 2 ^ 59
def prefixEnd_116199 : Nat := 4983230072969 + 3 ^ 40 * 116199 * 2
def baseEnd_116199 : Nat := 53036389841685426291659

theorem tailTrace_116199 : CollatzResearch.WordTrace tailWord_116199 prefixEnd_116199 53036389841685426291659 := by
  unfold tailWord_116199
  simp only [CollatzResearch.WordTrace]
  refine ⟨4238125706038343054351651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2825417137358895369567767 4238125706038343054351651)
  ·
    refine ⟨6357188559057514581527477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4238125706038343054351651 6357188559057514581527477)
    ·
      refine ⟨595986427411641992018201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6357188559057514581527477 595986427411641992018201)
      ·
        refine ⟨446989820558731494013651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595986427411641992018201 446989820558731494013651)
        ·
          refine ⟨670484730838097241020477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446989820558731494013651 670484730838097241020477)
          ·
            refine ⟨251431774064286465382679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 670484730838097241020477 251431774064286465382679)
            ·
              refine ⟨377147661096429698074019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251431774064286465382679 377147661096429698074019)
              ·
                refine ⟨565721491644644547111029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377147661096429698074019 565721491644644547111029)
                ·
                  refine ⟨53036389841685426291659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 565721491644644547111029 53036389841685426291659)
                  ·
                    rfl

theorem cell20_116199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 5].length) (baseStart_116199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116199 prefixEnd_116199 := by exact prefixLift 116199
  have htrace : WordTrace (prefixWord ++ tailWord_116199) baseStart_116199 baseEnd_116199 := by
    simpa [prefixWord, tailWord_116199, baseEnd_116199] using wordTrace_append hprefix tailTrace_116199
  have hstable : (prefixWord ++ tailWord_116199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116199).length < 2 ^ (prefixWord ++ tailWord_116199).sum := by decide
  have hdescent : baseEnd_116199 < baseStart_116199 := by decide
  rcases family_descends (prefixWord ++ tailWord_116199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116216 : List Nat := [2, 1, 2, 1, 1, 6, 3, 1, 3]
def baseStart_116216 : Nat := 118140960795 + 116216 * 2 ^ 59
def prefixEnd_116216 : Nat := 4983230072969 + 3 ^ 40 * 116216 * 2
def baseEnd_116216 : Nat := 53044149104908922724923

theorem tailTrace_116216 : CollatzResearch.WordTrace tailWord_116216 prefixEnd_116216 53044149104908922724923 := by
  unfold tailWord_116216
  simp only [CollatzResearch.WordTrace]
  refine ⟨2119372873488377478860251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2825830497984503305147001 2119372873488377478860251)
  ·
    refine ⟨3179059310232566218290377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2119372873488377478860251 3179059310232566218290377)
    ·
      refine ⟨2384294482674424663717783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3179059310232566218290377 2384294482674424663717783)
      ·
        refine ⟨3576441724011636995576675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2384294482674424663717783 3576441724011636995576675)
        ·
          refine ⟨5364662586017455493365013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3576441724011636995576675 5364662586017455493365013)
          ·
            refine ⟨251468558719568226251485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5364662586017455493365013 251468558719568226251485)
            ·
              refine ⟨94300709519838084844307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251468558719568226251485 94300709519838084844307)
              ·
                refine ⟨141451064279757127266461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94300709519838084844307 141451064279757127266461)
                ·
                  refine ⟨53044149104908922724923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141451064279757127266461 53044149104908922724923)
                  ·
                    rfl

theorem cell20_116216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 3].length) (baseStart_116216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116216 prefixEnd_116216 := by exact prefixLift 116216
  have htrace : WordTrace (prefixWord ++ tailWord_116216) baseStart_116216 baseEnd_116216 := by
    simpa [prefixWord, tailWord_116216, baseEnd_116216] using wordTrace_append hprefix tailTrace_116216
  have hstable : (prefixWord ++ tailWord_116216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116216).length < 2 ^ (prefixWord ++ tailWord_116216).sum := by decide
  have hdescent : baseEnd_116216 < baseStart_116216 := by decide
  rcases family_descends (prefixWord ++ tailWord_116216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116226 : List Nat := [3, 4, 1, 2, 1, 3, 2, 4]
def baseStart_116226 : Nat := 118140960795 + 116226 * 2 ^ 59
def prefixEnd_116226 : Nat := 4983230072969 + 3 ^ 40 * 116226 * 2
def baseEnd_116226 : Nat := 17682904459131110797183

theorem tailTrace_116226 : CollatzResearch.WordTrace tailWord_116226 prefixEnd_116226 17682904459131110797183 := by
  unfold tailWord_116226
  simp only [CollatzResearch.WordTrace]
  refine ⟨1059777619235131666396133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2826073651293684443723021 1059777619235131666396133)
  ·
    refine ⟨198708303606587187449275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1059777619235131666396133 198708303606587187449275)
    ·
      refine ⟨298062455409880781173913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198708303606587187449275 298062455409880781173913)
      ·
        refine ⟨223546841557410585880435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298062455409880781173913 223546841557410585880435)
        ·
          refine ⟨335320262336115878820653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223546841557410585880435 335320262336115878820653)
          ·
            refine ⟨125745098376043454557745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335320262336115878820653 125745098376043454557745)
            ·
              refine ⟨94308823782032590918309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125745098376043454557745 94308823782032590918309)
              ·
                refine ⟨17682904459131110797183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94308823782032590918309 17682904459131110797183)
                ·
                  rfl

theorem cell20_116226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_116226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116226 prefixEnd_116226 := by exact prefixLift 116226
  have htrace : WordTrace (prefixWord ++ tailWord_116226) baseStart_116226 baseEnd_116226 := by
    simpa [prefixWord, tailWord_116226, baseEnd_116226] using wordTrace_append hprefix tailTrace_116226
  have hstable : (prefixWord ++ tailWord_116226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116226).length < 2 ^ (prefixWord ++ tailWord_116226).sum := by decide
  have hdescent : baseEnd_116226 < baseStart_116226 := by decide
  rcases family_descends (prefixWord ++ tailWord_116226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116227 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 6]
def baseStart_116227 : Nat := 118140960795 + 116227 * 2 ^ 59
def prefixEnd_116227 : Nat := 4983230072969 + 3 ^ 40 * 116227 * 2
def baseEnd_116227 : Nat := 53049169804641773358211

theorem tailTrace_116227 : CollatzResearch.WordTrace tailWord_116227 prefixEnd_116227 53049169804641773358211 := by
  unfold tailWord_116227
  simp only [CollatzResearch.WordTrace]
  refine ⟨4239146949936903836370935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2826097966624602557580623 4239146949936903836370935)
  ·
    refine ⟨6358720424905355754556403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4239146949936903836370935 6358720424905355754556403)
    ·
      refine ⟨9538080637358033631834605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6358720424905355754556403 9538080637358033631834605)
      ·
        refine ⟨3576780239009262611937977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9538080637358033631834605 3576780239009262611937977)
        ·
          refine ⟨2682585179256946958953483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3576780239009262611937977 2682585179256946958953483)
          ·
            refine ⟨4023877768885420438430225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2682585179256946958953483 4023877768885420438430225)
            ·
              refine ⟨3017908326664065328822669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4023877768885420438430225 3017908326664065328822669)
              ·
                refine ⟨1131715622499024498308501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3017908326664065328822669 1131715622499024498308501)
                ·
                  refine ⟨53049169804641773358211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1131715622499024498308501 53049169804641773358211)
                  ·
                    rfl

theorem cell20_116227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_116227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116227 prefixEnd_116227 := by exact prefixLift 116227
  have htrace : WordTrace (prefixWord ++ tailWord_116227) baseStart_116227 baseEnd_116227 := by
    simpa [prefixWord, tailWord_116227, baseEnd_116227] using wordTrace_append hprefix tailTrace_116227
  have hstable : (prefixWord ++ tailWord_116227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116227).length < 2 ^ (prefixWord ++ tailWord_116227).sum := by decide
  have hdescent : baseEnd_116227 < baseStart_116227 := by decide
  rcases family_descends (prefixWord ++ tailWord_116227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116275 : List Nat := [1, 1, 1, 2, 4, 4, 1, 3, 3]
def baseStart_116275 : Nat := 118140960795 + 116275 * 2 ^ 59
def prefixEnd_116275 : Nat := 4983230072969 + 3 ^ 40 * 116275 * 2
def baseEnd_116275 : Nat := 53071078312566939758015

theorem tailTrace_116275 : CollatzResearch.WordTrace tailWord_116275 prefixEnd_116275 53071078312566939758015 := by
  unfold tailWord_116275
  simp only [CollatzResearch.WordTrace]
  refine ⟨4240897653763008034118279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2827265102508672022745519 4240897653763008034118279)
  ·
    refine ⟨6361346480644512051177419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4240897653763008034118279 6361346480644512051177419)
    ·
      refine ⟨9542019720966768076766129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6361346480644512051177419 9542019720966768076766129)
      ·
        refine ⟨7156514790725076057574597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9542019720966768076766129 7156514790725076057574597)
        ·
          refine ⟨1341846523260951760795237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7156514790725076057574597 1341846523260951760795237)
          ·
            refine ⟨251596223111428455149107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1341846523260951760795237 251596223111428455149107)
            ·
              refine ⟨377394334667142682723661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251596223111428455149107 377394334667142682723661)
              ·
                refine ⟨141522875500178506021373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 377394334667142682723661 141522875500178506021373)
                ·
                  refine ⟨53071078312566939758015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141522875500178506021373 53071078312566939758015)
                  ·
                    rfl

theorem cell20_116275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 3].length) (baseStart_116275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116275 prefixEnd_116275 := by exact prefixLift 116275
  have htrace : WordTrace (prefixWord ++ tailWord_116275) baseStart_116275 baseEnd_116275 := by
    simpa [prefixWord, tailWord_116275, baseEnd_116275] using wordTrace_append hprefix tailTrace_116275
  have hstable : (prefixWord ++ tailWord_116275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116275).length < 2 ^ (prefixWord ++ tailWord_116275).sum := by decide
  have hdescent : baseEnd_116275 < baseStart_116275 := by decide
  rcases family_descends (prefixWord ++ tailWord_116275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116289 : List Nat := [1, 2, 5, 1, 1, 1, 1, 8]
def baseStart_116289 : Nat := 118140960795 + 116289 * 2 ^ 59
def prefixEnd_116289 : Nat := 4983230072969 + 3 ^ 40 * 116289 * 2
def baseEnd_116289 : Nat := 17692489431348371097097

theorem tailTrace_116289 : CollatzResearch.WordTrace tailWord_116289 prefixEnd_116289 17692489431348371097097 := by
  unfold tailWord_116289
  simp only [CollatzResearch.WordTrace]
  refine ⟨4241408275712288425127921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2827605517141525616751947 4241408275712288425127921)
  ·
    refine ⟨3181056206784216318845941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4241408275712288425127921 3181056206784216318845941)
    ·
      refine ⟨298224019386020279891807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3181056206784216318845941 298224019386020279891807)
      ·
        refine ⟨447336029079030419837711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298224019386020279891807 447336029079030419837711)
        ·
          refine ⟨671004043618545629756567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447336029079030419837711 671004043618545629756567)
          ·
            refine ⟨1006506065427818444634851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671004043618545629756567 1006506065427818444634851)
            ·
              refine ⟨1509759098141727666952277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006506065427818444634851 1509759098141727666952277)
              ·
                refine ⟨17692489431348371097097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1509759098141727666952277 17692489431348371097097)
                ·
                  rfl

theorem cell20_116289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 8].length) (baseStart_116289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116289 prefixEnd_116289 := by exact prefixLift 116289
  have htrace : WordTrace (prefixWord ++ tailWord_116289) baseStart_116289 baseEnd_116289 := by
    simpa [prefixWord, tailWord_116289, baseEnd_116289] using wordTrace_append hprefix tailTrace_116289
  have hstable : (prefixWord ++ tailWord_116289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116289).length < 2 ^ (prefixWord ++ tailWord_116289).sum := by decide
  have hdescent : baseEnd_116289 < baseStart_116289 := by decide
  rcases family_descends (prefixWord ++ tailWord_116289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116316 : List Nat := [2, 2, 4, 1, 2, 2, 1, 4, 2]
def baseStart_116316 : Nat := 118140960795 + 116316 * 2 ^ 59
def prefixEnd_116316 : Nat := 4983230072969 + 3 ^ 40 * 116316 * 2
def baseEnd_116316 : Nat := 53089791829753019391181

theorem tailTrace_116316 : CollatzResearch.WordTrace tailWord_116316 prefixEnd_116316 53089791829753019391181 := by
  unfold tailWord_116316
  simp only [CollatzResearch.WordTrace]
  refine ⟨2121196523307236018180401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2828262031076314690907201 2121196523307236018180401)
  ·
    refine ⟨1590897392480427013635301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2121196523307236018180401 1590897392480427013635301)
    ·
      refine ⟨298293261090080065056619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1590897392480427013635301 298293261090080065056619)
      ·
        refine ⟨447439891635120097584929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298293261090080065056619 447439891635120097584929)
        ·
          refine ⟨335579918726340073188697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447439891635120097584929 335579918726340073188697)
          ·
            refine ⟨251684939044755054891523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335579918726340073188697 251684939044755054891523)
            ·
              refine ⟨377527408567132582337285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251684939044755054891523 377527408567132582337285)
              ·
                refine ⟨70786389106337359188241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 377527408567132582337285 70786389106337359188241)
                ·
                  refine ⟨53089791829753019391181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70786389106337359188241 53089791829753019391181)
                  ·
                    rfl

theorem cell20_116316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_116316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116316 prefixEnd_116316 := by exact prefixLift 116316
  have htrace : WordTrace (prefixWord ++ tailWord_116316) baseStart_116316 baseEnd_116316 := by
    simpa [prefixWord, tailWord_116316, baseEnd_116316] using wordTrace_append hprefix tailTrace_116316
  have hstable : (prefixWord ++ tailWord_116316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116316).length < 2 ^ (prefixWord ++ tailWord_116316).sum := by decide
  have hdescent : baseEnd_116316 < baseStart_116316 := by decide
  rcases family_descends (prefixWord ++ tailWord_116316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116327 : List Nat := [1, 1, 5, 1, 1, 1, 5, 5]
def baseStart_116327 : Nat := 118140960795 + 116327 * 2 ^ 59
def prefixEnd_116327 : Nat := 4983230072969 + 3 ^ 40 * 116327 * 2
def baseEnd_116327 : Nat := 17698270843161956674823

theorem tailTrace_116327 : CollatzResearch.WordTrace tailWord_116327 prefixEnd_116327 17698270843161956674823 := by
  unfold tailWord_116327
  simp only [CollatzResearch.WordTrace]
  refine ⟨4242794249574620915011235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2828529499716413943340823 4242794249574620915011235)
  ·
    refine ⟨6364191374361931372516853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4242794249574620915011235 6364191374361931372516853)
    ·
      refine ⟨596642941346431066173455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6364191374361931372516853 596642941346431066173455)
      ·
        refine ⟨894964412019646599260183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596642941346431066173455 894964412019646599260183)
        ·
          refine ⟨1342446618029469898890275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 894964412019646599260183 1342446618029469898890275)
          ·
            refine ⟨2013669927044204848335413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1342446618029469898890275 2013669927044204848335413)
            ·
              refine ⟨188781555660394204531445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2013669927044204848335413 188781555660394204531445)
              ·
                refine ⟨17698270843161956674823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 188781555660394204531445 17698270843161956674823)
                ·
                  rfl

theorem cell20_116327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 5].length) (baseStart_116327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116327 prefixEnd_116327 := by exact prefixLift 116327
  have htrace : WordTrace (prefixWord ++ tailWord_116327) baseStart_116327 baseEnd_116327 := by
    simpa [prefixWord, tailWord_116327, baseEnd_116327] using wordTrace_append hprefix tailTrace_116327
  have hstable : (prefixWord ++ tailWord_116327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116327).length < 2 ^ (prefixWord ++ tailWord_116327).sum := by decide
  have hdescent : baseEnd_116327 < baseStart_116327 := by decide
  rcases family_descends (prefixWord ++ tailWord_116327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116375 : List Nat := [1, 1, 3, 3, 2, 2, 2, 4, 2]
def baseStart_116375 : Nat := 118140960795 + 116375 * 2 ^ 59
def prefixEnd_116375 : Nat := 4983230072969 + 3 ^ 40 * 116375 * 2
def baseEnd_116375 : Nat := 53116721037411036424273

theorem tailTrace_116375 : CollatzResearch.WordTrace tailWord_116375 prefixEnd_116375 53116721037411036424273 := by
  unfold tailWord_116375
  simp only [CollatzResearch.WordTrace]
  refine ⟨4244544953400725112758579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2829696635600483408505719 4244544953400725112758579)
  ·
    refine ⟨6366817430101087669137869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4244544953400725112758579 6366817430101087669137869)
    ·
      refine ⟨2387556536287907875926701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6366817430101087669137869 2387556536287907875926701)
      ·
        refine ⟨895333701107965453472513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2387556536287907875926701 895333701107965453472513)
        ·
          refine ⟨671500275830974090104385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 895333701107965453472513 671500275830974090104385)
          ·
            refine ⟨503625206873230567578289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 671500275830974090104385 503625206873230567578289)
            ·
              refine ⟨377718905154922925683717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503625206873230567578289 377718905154922925683717)
              ·
                refine ⟨70822294716548048565697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 377718905154922925683717 70822294716548048565697)
                ·
                  refine ⟨53116721037411036424273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70822294716548048565697 53116721037411036424273)
                  ·
                    rfl

theorem cell20_116375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 2].length) (baseStart_116375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116375 prefixEnd_116375 := by exact prefixLift 116375
  have htrace : WordTrace (prefixWord ++ tailWord_116375) baseStart_116375 baseEnd_116375 := by
    simpa [prefixWord, tailWord_116375, baseEnd_116375] using wordTrace_append hprefix tailTrace_116375
  have hstable : (prefixWord ++ tailWord_116375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116375).length < 2 ^ (prefixWord ++ tailWord_116375).sum := by decide
  have hdescent : baseEnd_116375 < baseStart_116375 := by decide
  rcases family_descends (prefixWord ++ tailWord_116375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116406 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_116406 : Nat := 118140960795 + 116406 * 2 ^ 59
def prefixEnd_116406 : Nat := 4983230072969 + 3 ^ 40 * 116406 * 2
def baseEnd_116406 : Nat := 53130870282112706390813

theorem tailTrace_116406 : CollatzResearch.WordTrace tailWord_116406 prefixEnd_116406 53130870282112706390813 := by
  unfold tailWord_116406
  simp only [CollatzResearch.WordTrace]
  refine ⟨265354726018026087946067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2830450410858944938091381 265354726018026087946067)
  ·
    refine ⟨398032089027039131919101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265354726018026087946067 398032089027039131919101)
    ·
      refine ⟨149262033385139674469663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 398032089027039131919101 149262033385139674469663)
      ·
        refine ⟨223893050077709511704495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149262033385139674469663 223893050077709511704495)
        ·
          refine ⟨335839575116564267556743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223893050077709511704495 335839575116564267556743)
          ·
            refine ⟨503759362674846401335115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335839575116564267556743 503759362674846401335115)
            ·
              refine ⟨755639044012269602002673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503759362674846401335115 755639044012269602002673)
              ·
                refine ⟨566729283009202201502005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 755639044012269602002673 566729283009202201502005)
                ·
                  refine ⟨53130870282112706390813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 566729283009202201502005 53130870282112706390813)
                  ·
                    rfl

theorem cell20_116406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_116406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116406 prefixEnd_116406 := by exact prefixLift 116406
  have htrace : WordTrace (prefixWord ++ tailWord_116406) baseStart_116406 baseEnd_116406 := by
    simpa [prefixWord, tailWord_116406, baseEnd_116406] using wordTrace_append hprefix tailTrace_116406
  have hstable : (prefixWord ++ tailWord_116406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116406).length < 2 ^ (prefixWord ++ tailWord_116406).sum := by decide
  have hdescent : baseEnd_116406 < baseStart_116406 := by decide
  rcases family_descends (prefixWord ++ tailWord_116406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116410 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 5]
def baseStart_116410 : Nat := 118140960795 + 116410 * 2 ^ 59
def prefixEnd_116410 : Nat := 4983230072969 + 3 ^ 40 * 116410 * 2
def baseEnd_116410 : Nat := 53132695991106470257463

theorem tailTrace_116410 : CollatzResearch.WordTrace tailWord_116410 prefixEnd_116410 53132695991106470257463 := by
  unfold tailWord_116410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1061455377068481522570671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2830547672182617393521789 1061455377068481522570671)
  ·
    refine ⟨1592183065602722283856007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1061455377068481522570671 1592183065602722283856007)
    ·
      refine ⟨2388274598404083425784011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1592183065602722283856007 2388274598404083425784011)
      ·
        refine ⟨3582411897606125138676017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2388274598404083425784011 3582411897606125138676017)
        ·
          refine ⟨2686808923204593854007013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3582411897606125138676017 2686808923204593854007013)
          ·
            refine ⟨503776673100861347626315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2686808923204593854007013 503776673100861347626315)
            ·
              refine ⟨755665009651292021439473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503776673100861347626315 755665009651292021439473)
              ·
                refine ⟨566748757238469016079605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 755665009651292021439473 566748757238469016079605)
                ·
                  refine ⟨53132695991106470257463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 566748757238469016079605 53132695991106470257463)
                  ·
                    rfl

theorem cell20_116410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_116410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116410 prefixEnd_116410 := by exact prefixLift 116410
  have htrace : WordTrace (prefixWord ++ tailWord_116410) baseStart_116410 baseEnd_116410 := by
    simpa [prefixWord, tailWord_116410, baseEnd_116410] using wordTrace_append hprefix tailTrace_116410
  have hstable : (prefixWord ++ tailWord_116410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116410).length < 2 ^ (prefixWord ++ tailWord_116410).sum := by decide
  have hdescent : baseEnd_116410 < baseStart_116410 := by decide
  rcases family_descends (prefixWord ++ tailWord_116410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116430 : List Nat := [4, 1, 1, 1, 3, 1, 5, 2, 2]
def baseStart_116430 : Nat := 118140960795 + 116430 * 2 ^ 59
def prefixEnd_116430 : Nat := 4983230072969 + 3 ^ 40 * 116430 * 2
def baseEnd_116430 : Nat := 53141824536075289590715

theorem tailTrace_116430 : CollatzResearch.WordTrace tailWord_116430 prefixEnd_116430 53141824536075289590715 := by
  unfold tailWord_116430
  simp only [CollatzResearch.WordTrace]
  refine ⟨530818871025183688251343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2831033978800979670673829 530818871025183688251343)
  ·
    refine ⟨796228306537775532377015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 530818871025183688251343 796228306537775532377015)
    ·
      refine ⟨1194342459806663298565523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 796228306537775532377015 1194342459806663298565523)
      ·
        refine ⟨1791513689709994947848285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1194342459806663298565523 1791513689709994947848285)
        ·
          refine ⟨671817633641248105443107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1791513689709994947848285 671817633641248105443107)
          ·
            refine ⟨1007726450461872158164661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671817633641248105443107 1007726450461872158164661)
            ·
              refine ⟨94474354730800514827937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1007726450461872158164661 94474354730800514827937)
              ·
                refine ⟨70855766048100386120953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94474354730800514827937 70855766048100386120953)
                ·
                  refine ⟨53141824536075289590715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70855766048100386120953 53141824536075289590715)
                  ·
                    rfl

theorem cell20_116430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_116430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116430 prefixEnd_116430 := by exact prefixLift 116430
  have htrace : WordTrace (prefixWord ++ tailWord_116430) baseStart_116430 baseEnd_116430 := by
    simpa [prefixWord, tailWord_116430, baseEnd_116430] using wordTrace_append hprefix tailTrace_116430
  have hstable : (prefixWord ++ tailWord_116430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116430).length < 2 ^ (prefixWord ++ tailWord_116430).sum := by decide
  have hdescent : baseEnd_116430 < baseStart_116430 := by decide
  rcases family_descends (prefixWord ++ tailWord_116430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116441 : List Nat := [1, 2, 1, 2, 3, 4, 2, 5]
def baseStart_116441 : Nat := 118140960795 + 116441 * 2 ^ 59
def prefixEnd_116441 : Nat := 4983230072969 + 3 ^ 40 * 116441 * 2
def baseEnd_116441 : Nat := 17715615078602713408001

theorem tailTrace_116441 : CollatzResearch.WordTrace tailWord_116441 prefixEnd_116441 17715615078602713408001 := by
  unfold tailWord_116441
  simp only [CollatzResearch.WordTrace]
  refine ⟨4246952171161618384661177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2831301447441078923107451 4246952171161618384661177)
  ·
    refine ⟨3185214128371213788495883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4246952171161618384661177 3185214128371213788495883)
    ·
      refine ⟨4777821192556820682743825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3185214128371213788495883 4777821192556820682743825)
      ·
        refine ⟨3583365894417615512057869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4777821192556820682743825 3583365894417615512057869)
        ·
          refine ⟨1343762210406605817021701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3583365894417615512057869 1343762210406605817021701)
          ·
            refine ⟨251955414451238590691569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1343762210406605817021701 251955414451238590691569)
            ·
              refine ⟨188966560838428943018677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251955414451238590691569 188966560838428943018677)
              ·
                refine ⟨17715615078602713408001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 188966560838428943018677 17715615078602713408001)
                ·
                  rfl

theorem cell20_116441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 5].length) (baseStart_116441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116441 prefixEnd_116441 := by exact prefixLift 116441
  have htrace : WordTrace (prefixWord ++ tailWord_116441) baseStart_116441 baseEnd_116441 := by
    simpa [prefixWord, tailWord_116441, baseEnd_116441] using wordTrace_append hprefix tailTrace_116441
  have hstable : (prefixWord ++ tailWord_116441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116441).length < 2 ^ (prefixWord ++ tailWord_116441).sum := by decide
  have hdescent : baseEnd_116441 < baseStart_116441 := by decide
  rcases family_descends (prefixWord ++ tailWord_116441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116482 : List Nat := [3, 4, 1, 1, 1, 1, 4, 2, 3]
def baseStart_116482 : Nat := 118140960795 + 116482 * 2 ^ 59
def prefixEnd_116482 : Nat := 4983230072969 + 3 ^ 40 * 116482 * 2
def baseEnd_116482 : Nat := 53165558752994219857169

theorem tailTrace_116482 : CollatzResearch.WordTrace tailWord_116482 prefixEnd_116482 53165558752994219857169 := by
  unfold tailWord_116482
  simp only [CollatzResearch.WordTrace]
  refine ⟨1062111891003270596725925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2832298376008721591269133 1062111891003270596725925)
  ·
    refine ⟨199145979563113236886111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1062111891003270596725925 199145979563113236886111)
    ·
      refine ⟨298718969344669855329167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199145979563113236886111 298718969344669855329167)
      ·
        refine ⟨448078454017004782993751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298718969344669855329167 448078454017004782993751)
        ·
          refine ⟨672117681025507174490627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448078454017004782993751 672117681025507174490627)
          ·
            refine ⟨1008176521538260761735941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672117681025507174490627 1008176521538260761735941)
            ·
              refine ⟨189033097788423892825489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1008176521538260761735941 189033097788423892825489)
              ·
                refine ⟨141774823341317919619117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189033097788423892825489 141774823341317919619117)
                ·
                  refine ⟨53165558752994219857169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141774823341317919619117 53165558752994219857169)
                  ·
                    rfl

theorem cell20_116482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_116482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116482 prefixEnd_116482 := by exact prefixLift 116482
  have htrace : WordTrace (prefixWord ++ tailWord_116482) baseStart_116482 baseEnd_116482 := by
    simpa [prefixWord, tailWord_116482, baseEnd_116482] using wordTrace_append hprefix tailTrace_116482
  have hstable : (prefixWord ++ tailWord_116482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116482).length < 2 ^ (prefixWord ++ tailWord_116482).sum := by decide
  have hdescent : baseEnd_116482 < baseStart_116482 := by decide
  rcases family_descends (prefixWord ++ tailWord_116482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116503 : List Nat := [1, 1, 3, 4, 2, 1, 2, 3, 3]
def baseStart_116503 : Nat := 118140960795 + 116503 * 2 ^ 59
def prefixEnd_116503 : Nat := 4983230072969 + 3 ^ 40 * 116503 * 2
def baseEnd_116503 : Nat := 53175143725211480157083

theorem tailTrace_116503 : CollatzResearch.WordTrace tailWord_116503 prefixEnd_116503 53175143725211480157083 := by
  unfold tailWord_116503
  simp only [CollatzResearch.WordTrace]
  refine ⟨4249213496937002973418163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2832808997958001982278775 4249213496937002973418163)
  ·
    refine ⟨6373820245405504460127245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4249213496937002973418163 6373820245405504460127245)
    ·
      refine ⟨2390182592027064172547717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6373820245405504460127245 2390182592027064172547717)
      ·
        refine ⟨448159236005074532352697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2390182592027064172547717 448159236005074532352697)
        ·
          refine ⟨336119427003805899264523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448159236005074532352697 336119427003805899264523)
          ·
            refine ⟨504179140505708848896785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336119427003805899264523 504179140505708848896785)
            ·
              refine ⟨378134355379281636672589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504179140505708848896785 378134355379281636672589)
              ·
                refine ⟨141800383267230613752221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 378134355379281636672589 141800383267230613752221)
                ·
                  refine ⟨53175143725211480157083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141800383267230613752221 53175143725211480157083)
                  ·
                    rfl

theorem cell20_116503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 3].length) (baseStart_116503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116503 prefixEnd_116503 := by exact prefixLift 116503
  have htrace : WordTrace (prefixWord ++ tailWord_116503) baseStart_116503 baseEnd_116503 := by
    simpa [prefixWord, tailWord_116503, baseEnd_116503] using wordTrace_append hprefix tailTrace_116503
  have hstable : (prefixWord ++ tailWord_116503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116503).length < 2 ^ (prefixWord ++ tailWord_116503).sum := by decide
  have hdescent : baseEnd_116503 < baseStart_116503 := by decide
  rcases family_descends (prefixWord ++ tailWord_116503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116534 : List Nat := [5, 1, 2, 2, 1, 2, 7]
def baseStart_116534 : Nat := 118140960795 + 116534 * 2 ^ 59
def prefixEnd_116534 : Nat := 4983230072969 + 3 ^ 40 * 116534 * 2
def baseEnd_116534 : Nat := 5909921441101461124847

theorem tailTrace_116534 : CollatzResearch.WordTrace tailWord_116534 prefixEnd_116534 5909921441101461124847 := by
  unfold tailWord_116534
  simp only [CollatzResearch.WordTrace]
  refine ⟨265646509989043454237291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2833562773216463511864437 265646509989043454237291)
  ·
    refine ⟨398469764983565181355937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265646509989043454237291 398469764983565181355937)
    ·
      refine ⟨298852323737673886016953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398469764983565181355937 298852323737673886016953)
      ·
        refine ⟨224139242803255414512715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298852323737673886016953 224139242803255414512715)
        ·
          refine ⟨336208864204883121769073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224139242803255414512715 336208864204883121769073)
          ·
            refine ⟨252156648153662341326805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336208864204883121769073 252156648153662341326805)
            ·
              refine ⟨5909921441101461124847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 252156648153662341326805 5909921441101461124847)
              ·
                rfl

theorem cell20_116534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 7].length) (baseStart_116534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116534 prefixEnd_116534 := by exact prefixLift 116534
  have htrace : WordTrace (prefixWord ++ tailWord_116534) baseStart_116534 baseEnd_116534 := by
    simpa [prefixWord, tailWord_116534, baseEnd_116534] using wordTrace_append hprefix tailTrace_116534
  have hstable : (prefixWord ++ tailWord_116534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116534).length < 2 ^ (prefixWord ++ tailWord_116534).sum := by decide
  have hdescent : baseEnd_116534 < baseStart_116534 := by decide
  rcases family_descends (prefixWord ++ tailWord_116534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116537 : List Nat := [1, 2, 1, 7, 1, 2, 1, 2, 3]
def baseStart_116537 : Nat := 118140960795 + 116537 * 2 ^ 59
def prefixEnd_116537 : Nat := 4983230072969 + 3 ^ 40 * 116537 * 2
def baseEnd_116537 : Nat := 53190662251658473023611

theorem tailTrace_116537 : CollatzResearch.WordTrace tailWord_116537 prefixEnd_116537 53190662251658473023611 := by
  unfold tailWord_116537
  simp only [CollatzResearch.WordTrace]
  refine ⟨4250453578813826780155865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2833635719209217853437243 4250453578813826780155865)
  ·
    refine ⟨3187840184110370085116899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4250453578813826780155865 3187840184110370085116899)
    ·
      refine ⟨4781760276165555127675349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3187840184110370085116899 4781760276165555127675349)
      ·
        refine ⟨112072506472630198304891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 4781760276165555127675349 112072506472630198304891)
        ·
          refine ⟨168108759708945297457337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112072506472630198304891 168108759708945297457337)
          ·
            refine ⟨126081569781708973093003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168108759708945297457337 126081569781708973093003)
            ·
              refine ⟨189122354672563459639505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126081569781708973093003 189122354672563459639505)
              ·
                refine ⟨141841766004422594729629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189122354672563459639505 141841766004422594729629)
                ·
                  refine ⟨53190662251658473023611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141841766004422594729629 53190662251658473023611)
                  ·
                    rfl

theorem cell20_116537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 3].length) (baseStart_116537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116537 prefixEnd_116537 := by exact prefixLift 116537
  have htrace : WordTrace (prefixWord ++ tailWord_116537) baseStart_116537 baseEnd_116537 := by
    simpa [prefixWord, tailWord_116537, baseEnd_116537] using wordTrace_append hprefix tailTrace_116537
  have hstable : (prefixWord ++ tailWord_116537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116537).length < 2 ^ (prefixWord ++ tailWord_116537).sum := by decide
  have hdescent : baseEnd_116537 < baseStart_116537 := by decide
  rcases family_descends (prefixWord ++ tailWord_116537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116541 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 5]
def baseStart_116541 : Nat := 118140960795 + 116541 * 2 ^ 59
def prefixEnd_116541 : Nat := 4983230072969 + 3 ^ 40 * 116541 * 2
def baseEnd_116541 : Nat := 53192487960652236890261

theorem tailTrace_116541 : CollatzResearch.WordTrace tailWord_116541 prefixEnd_116541 53192487960652236890261 := by
  unfold tailWord_116541
  simp only [CollatzResearch.WordTrace]
  refine ⟨4250599470799335463301477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2833732980532890308867651 4250599470799335463301477)
  ·
    refine ⟨796987400774875399369027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4250599470799335463301477 796987400774875399369027)
    ·
      refine ⟨1195481101162313099053541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 796987400774875399369027 1195481101162313099053541)
      ·
        refine ⟨224152706467933706072539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1195481101162313099053541 224152706467933706072539)
        ·
          refine ⟨336229059701900559108809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224152706467933706072539 336229059701900559108809)
          ·
            refine ⟨252171794776425419331607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336229059701900559108809 252171794776425419331607)
            ·
              refine ⟨378257692164638128997411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252171794776425419331607 378257692164638128997411)
              ·
                refine ⟨567386538246957193496117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378257692164638128997411 567386538246957193496117)
                ·
                  refine ⟨53192487960652236890261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 567386538246957193496117 53192487960652236890261)
                  ·
                    rfl

theorem cell20_116541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_116541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116541 prefixEnd_116541 := by exact prefixLift 116541
  have htrace : WordTrace (prefixWord ++ tailWord_116541) baseStart_116541 baseEnd_116541 := by
    simpa [prefixWord, tailWord_116541, baseEnd_116541] using wordTrace_append hprefix tailTrace_116541
  have hstable : (prefixWord ++ tailWord_116541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116541).length < 2 ^ (prefixWord ++ tailWord_116541).sum := by decide
  have hdescent : baseEnd_116541 < baseStart_116541 := by decide
  rcases family_descends (prefixWord ++ tailWord_116541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116569 : List Nat := [1, 2, 1, 2, 2, 3, 1, 4, 4]
def baseStart_116569 : Nat := 118140960795 + 116569 * 2 ^ 59
def prefixEnd_116569 : Nat := 4983230072969 + 3 ^ 40 * 116569 * 2
def baseEnd_116569 : Nat := 53205267923608583956813

theorem tailTrace_116569 : CollatzResearch.WordTrace tailWord_116569 prefixEnd_116569 53205267923608583956813 := by
  unfold tailWord_116569
  simp only [CollatzResearch.WordTrace]
  refine ⟨4251620714697896245320761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2834413809798597496880507 4251620714697896245320761)
  ·
    refine ⟨3188715536023422183990571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4251620714697896245320761 3188715536023422183990571)
    ·
      refine ⟨4783073304035133275985857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3188715536023422183990571 4783073304035133275985857)
      ·
        refine ⟨3587304978026349956989393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4783073304035133275985857 3587304978026349956989393)
        ·
          refine ⟨2690478733519762467742045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3587304978026349956989393 2690478733519762467742045)
          ·
            refine ⟨1008929525069910925403267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2690478733519762467742045 1008929525069910925403267)
            ·
              refine ⟨1513394287604866388104901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1008929525069910925403267 1513394287604866388104901)
              ·
                refine ⟨283761428925912447769669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1513394287604866388104901 283761428925912447769669)
                ·
                  refine ⟨53205267923608583956813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 283761428925912447769669 53205267923608583956813)
                  ·
                    rfl

theorem cell20_116569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_116569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116569 prefixEnd_116569 := by exact prefixLift 116569
  have htrace : WordTrace (prefixWord ++ tailWord_116569) baseStart_116569 baseEnd_116569 := by
    simpa [prefixWord, tailWord_116569, baseEnd_116569] using wordTrace_append hprefix tailTrace_116569
  have hstable : (prefixWord ++ tailWord_116569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116569).length < 2 ^ (prefixWord ++ tailWord_116569).sum := by decide
  have hdescent : baseEnd_116569 < baseStart_116569 := by decide
  rcases family_descends (prefixWord ++ tailWord_116569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116572 : List Nat := [2, 2, 4, 2, 2, 1, 1, 6]
def baseStart_116572 : Nat := 118140960795 + 116572 * 2 ^ 59
def prefixEnd_116572 : Nat := 4983230072969 + 3 ^ 40 * 116572 * 2
def baseEnd_116572 : Nat := 17735545735117968952267

theorem tailTrace_116572 : CollatzResearch.WordTrace tailWord_116572 prefixEnd_116572 17735545735117968952267 := by
  unfold tailWord_116572
  simp only [CollatzResearch.WordTrace]
  refine ⟨2125865066843513878839985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2834486755791351838453313 2125865066843513878839985)
  ·
    refine ⟨1594398800132635409129989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2125865066843513878839985 1594398800132635409129989)
    ·
      refine ⟨298949775024869139211873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1594398800132635409129989 298949775024869139211873)
      ·
        refine ⟨224212331268651854408905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298949775024869139211873 224212331268651854408905)
        ·
          refine ⟨168159248451488890806679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224212331268651854408905 168159248451488890806679)
          ·
            refine ⟨252238872677233336210019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168159248451488890806679 252238872677233336210019)
            ·
              refine ⟨378358309015850004315029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252238872677233336210019 378358309015850004315029)
              ·
                refine ⟨17735545735117968952267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 378358309015850004315029 17735545735117968952267)
                ·
                  rfl

theorem cell20_116572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 6].length) (baseStart_116572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116572 prefixEnd_116572 := by exact prefixLift 116572
  have htrace : WordTrace (prefixWord ++ tailWord_116572) baseStart_116572 baseEnd_116572 := by
    simpa [prefixWord, tailWord_116572, baseEnd_116572] using wordTrace_append hprefix tailTrace_116572
  have hstable : (prefixWord ++ tailWord_116572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116572).length < 2 ^ (prefixWord ++ tailWord_116572).sum := by decide
  have hdescent : baseEnd_116572 < baseStart_116572 := by decide
  rcases family_descends (prefixWord ++ tailWord_116572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116648 : List Nat := [2, 1, 6, 2, 1, 8]
def baseStart_116648 : Nat := 118140960795 + 116648 * 2 ^ 59
def prefixEnd_116648 : Nat := 4983230072969 + 3 ^ 40 * 116648 * 2
def baseEnd_116648 : Nat := 1971900950971682234191

theorem tailTrace_116648 : CollatzResearch.WordTrace tailWord_116648 prefixEnd_116648 1971900950971682234191 := by
  unfold tailWord_116648
  simp only [CollatzResearch.WordTrace]
  refine ⟨2127251040705846368723299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2836334720941128491631065 2127251040705846368723299)
  ·
    refine ⟨3190876561058769553084949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2127251040705846368723299 3190876561058769553084949)
    ·
      refine ⟨149572338799629822800857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3190876561058769553084949 149572338799629822800857)
      ·
        refine ⟨112179254099722367100643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149572338799629822800857 112179254099722367100643)
        ·
          refine ⟨168268881149583550650965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112179254099722367100643 168268881149583550650965)
          ·
            refine ⟨1971900950971682234191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 168268881149583550650965 1971900950971682234191)
            ·
              rfl

theorem cell20_116648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 8].length) (baseStart_116648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116648 prefixEnd_116648 := by exact prefixLift 116648
  have htrace : WordTrace (prefixWord ++ tailWord_116648) baseStart_116648 baseEnd_116648 := by
    simpa [prefixWord, tailWord_116648, baseEnd_116648] using wordTrace_append hprefix tailTrace_116648
  have hstable : (prefixWord ++ tailWord_116648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116648).length < 2 ^ (prefixWord ++ tailWord_116648).sum := by decide
  have hdescent : baseEnd_116648 < baseStart_116648 := by decide
  rcases family_descends (prefixWord ++ tailWord_116648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116654 : List Nat := [4, 1, 5, 1, 1, 1, 1, 4, 2]
def baseStart_116654 : Nat := 118140960795 + 116654 * 2 ^ 59
def prefixEnd_116654 : Nat := 4983230072969 + 3 ^ 40 * 116654 * 2
def baseEnd_116654 : Nat := 53244064239726066123133

theorem tailTrace_116654 : CollatzResearch.WordTrace tailWord_116654 prefixEnd_116654 53244064239726066123133 := by
  unfold tailWord_116654
  simp only [CollatzResearch.WordTrace]
  refine ⟨531840114923744470270627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2836480612926637174776677 531840114923744470270627)
  ·
    refine ⟨797760172385616705405941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 531840114923744470270627 797760172385616705405941)
    ·
      refine ⟨74790016161151566131807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 797760172385616705405941 74790016161151566131807)
      ·
        refine ⟨112185024241727349197711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74790016161151566131807 112185024241727349197711)
        ·
          refine ⟨168277536362591023796567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112185024241727349197711 168277536362591023796567)
          ·
            refine ⟨252416304543886535694851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168277536362591023796567 252416304543886535694851)
            ·
              refine ⟨378624456815829803542277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252416304543886535694851 378624456815829803542277)
              ·
                refine ⟨70992085652968088164177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 378624456815829803542277 70992085652968088164177)
                ·
                  refine ⟨53244064239726066123133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70992085652968088164177 53244064239726066123133)
                  ·
                    rfl

theorem cell20_116654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_116654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116654 prefixEnd_116654 := by exact prefixLift 116654
  have htrace : WordTrace (prefixWord ++ tailWord_116654) baseStart_116654 baseEnd_116654 := by
    simpa [prefixWord, tailWord_116654, baseEnd_116654] using wordTrace_append hprefix tailTrace_116654
  have hstable : (prefixWord ++ tailWord_116654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116654).length < 2 ^ (prefixWord ++ tailWord_116654).sum := by decide
  have hdescent : baseEnd_116654 < baseStart_116654 := by decide
  rcases family_descends (prefixWord ++ tailWord_116654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116669 : List Nat := [1, 4, 1, 2, 3, 1, 3, 5]
def baseStart_116669 : Nat := 118140960795 + 116669 * 2 ^ 59
def prefixEnd_116669 : Nat := 4983230072969 + 3 ^ 40 * 116669 * 2
def baseEnd_116669 : Nat := 17750303549484226874357

theorem tailTrace_116669 : CollatzResearch.WordTrace tailWord_116669 prefixEnd_116669 17750303549484226874357 := by
  unfold tailWord_116669
  simp only [CollatzResearch.WordTrace]
  refine ⟨4255268014335613323961061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2836845342890408882640707 4255268014335613323961061)
  ·
    refine ⟨797862752687927498242699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4255268014335613323961061 797862752687927498242699)
    ·
      refine ⟨1196794129031891247364049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 797862752687927498242699 1196794129031891247364049)
      ·
        refine ⟨897595596773918435523037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1196794129031891247364049 897595596773918435523037)
        ·
          refine ⟨336598348790219413321139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 897595596773918435523037 336598348790219413321139)
          ·
            refine ⟨504897523185329119981709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336598348790219413321139 504897523185329119981709)
            ·
              refine ⟨189336571194498419993141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 504897523185329119981709 189336571194498419993141)
              ·
                refine ⟨17750303549484226874357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 189336571194498419993141 17750303549484226874357)
                ·
                  rfl

theorem cell20_116669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 5].length) (baseStart_116669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116669 prefixEnd_116669 := by exact prefixLift 116669
  have htrace : WordTrace (prefixWord ++ tailWord_116669) baseStart_116669 baseEnd_116669 := by
    simpa [prefixWord, tailWord_116669, baseEnd_116669] using wordTrace_append hprefix tailTrace_116669
  have hstable : (prefixWord ++ tailWord_116669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116669).length < 2 ^ (prefixWord ++ tailWord_116669).sum := by decide
  have hdescent : baseEnd_116669 < baseStart_116669 := by decide
  rcases family_descends (prefixWord ++ tailWord_116669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116683 : List Nat := [1, 1, 1, 1, 3, 4, 3, 2, 4]
def baseStart_116683 : Nat := 118140960795 + 116683 * 2 ^ 59
def prefixEnd_116683 : Nat := 4983230072969 + 3 ^ 40 * 116683 * 2
def baseEnd_116683 : Nat := 53257300629930854156347

theorem tailTrace_116683 : CollatzResearch.WordTrace tailWord_116683 prefixEnd_116683 53257300629930854156347 := by
  unfold tailWord_116683
  simp only [CollatzResearch.WordTrace]
  refine ⟨4255778636284893714970703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2837185757523262476647135 4255778636284893714970703)
  ·
    refine ⟨6383667954427340572456055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4255778636284893714970703 6383667954427340572456055)
    ·
      refine ⟨9575501931641010858684083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6383667954427340572456055 9575501931641010858684083)
      ·
        refine ⟨14363252897461516288026125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9575501931641010858684083 14363252897461516288026125)
        ·
          refine ⟨5386219836548068608009797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14363252897461516288026125 5386219836548068608009797)
          ·
            refine ⟨1009916219352762864001837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5386219836548068608009797 1009916219352762864001837)
            ·
              refine ⟨378718582257286074000689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1009916219352762864001837 378718582257286074000689)
              ·
                refine ⟨284038936692964555500517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378718582257286074000689 284038936692964555500517)
                ·
                  refine ⟨53257300629930854156347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 284038936692964555500517 53257300629930854156347)
                  ·
                    rfl

theorem cell20_116683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 4].length) (baseStart_116683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116683 prefixEnd_116683 := by exact prefixLift 116683
  have htrace : WordTrace (prefixWord ++ tailWord_116683) baseStart_116683 baseEnd_116683 := by
    simpa [prefixWord, tailWord_116683, baseEnd_116683] using wordTrace_append hprefix tailTrace_116683
  have hstable : (prefixWord ++ tailWord_116683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116683).length < 2 ^ (prefixWord ++ tailWord_116683).sum := by decide
  have hdescent : baseEnd_116683 < baseStart_116683 := by decide
  rcases family_descends (prefixWord ++ tailWord_116683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116706 : List Nat := [3, 3, 3, 1, 3, 1, 1, 2, 3]
def baseStart_116706 : Nat := 118140960795 + 116706 * 2 ^ 59
def prefixEnd_116706 : Nat := 4983230072969 + 3 ^ 40 * 116706 * 2
def baseEnd_116706 : Nat := 53267798456644996389587

theorem tailTrace_116706 : CollatzResearch.WordTrace tailWord_116706 prefixEnd_116706 53267798456644996389587 := by
  unfold tailWord_116706
  simp only [CollatzResearch.WordTrace]
  refine ⟨1064154378800392160764493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2837745010134379095371981 1064154378800392160764493)
  ·
    refine ⟨399057892050147060286685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1064154378800392160764493 399057892050147060286685)
    ·
      refine ⟨149646709518805147607507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399057892050147060286685 149646709518805147607507)
      ·
        refine ⟨224470064278207721411261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149646709518805147607507 224470064278207721411261)
        ·
          refine ⟨84176274104327895529223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224470064278207721411261 84176274104327895529223)
          ·
            refine ⟨126264411156491843293835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84176274104327895529223 126264411156491843293835)
            ·
              refine ⟨189396616734737764940753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126264411156491843293835 189396616734737764940753)
              ·
                refine ⟨142047462551053323705565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189396616734737764940753 142047462551053323705565)
                ·
                  refine ⟨53267798456644996389587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142047462551053323705565 53267798456644996389587)
                  ·
                    rfl

theorem cell20_116706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_116706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116706 prefixEnd_116706 := by exact prefixLift 116706
  have htrace : WordTrace (prefixWord ++ tailWord_116706) baseStart_116706 baseEnd_116706 := by
    simpa [prefixWord, tailWord_116706, baseEnd_116706] using wordTrace_append hprefix tailTrace_116706
  have hstable : (prefixWord ++ tailWord_116706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116706).length < 2 ^ (prefixWord ++ tailWord_116706).sum := by decide
  have hdescent : baseEnd_116706 < baseStart_116706 := by decide
  rcases family_descends (prefixWord ++ tailWord_116706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116714 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 5]
def baseStart_116714 : Nat := 118140960795 + 116714 * 2 ^ 59
def prefixEnd_116714 : Nat := 4983230072969 + 3 ^ 40 * 116714 * 2
def baseEnd_116714 : Nat := 53271449874632524122887

theorem tailTrace_116714 : CollatzResearch.WordTrace tailWord_116714 prefixEnd_116714 53271449874632524122887 := by
  unfold tailWord_116714
  simp only [CollatzResearch.WordTrace]
  refine ⟨1064227324793146502337299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2837939532781724006232797 1064227324793146502337299)
  ·
    refine ⟨1596340987189719753505949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1064227324793146502337299 1596340987189719753505949)
    ·
      refine ⟨598627870196144907564731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1596340987189719753505949 598627870196144907564731)
      ·
        refine ⟨897941805294217361347097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598627870196144907564731 897941805294217361347097)
        ·
          refine ⟨673456353970663021010323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 897941805294217361347097 673456353970663021010323)
          ·
            refine ⟨1010184530955994531515485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673456353970663021010323 1010184530955994531515485)
            ·
              refine ⟨378819199108497949318307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1010184530955994531515485 378819199108497949318307)
              ·
                refine ⟨568228798662746923977461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378819199108497949318307 568228798662746923977461)
                ·
                  refine ⟨53271449874632524122887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 568228798662746923977461 53271449874632524122887)
                  ·
                    rfl

theorem cell20_116714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_116714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116714 prefixEnd_116714 := by exact prefixLift 116714
  have htrace : WordTrace (prefixWord ++ tailWord_116714) baseStart_116714 baseEnd_116714 := by
    simpa [prefixWord, tailWord_116714, baseEnd_116714] using wordTrace_append hprefix tailTrace_116714
  have hstable : (prefixWord ++ tailWord_116714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116714).length < 2 ^ (prefixWord ++ tailWord_116714).sum := by decide
  have hdescent : baseEnd_116714 < baseStart_116714 := by decide
  rcases family_descends (prefixWord ++ tailWord_116714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116772 : List Nat := [2, 3, 1, 4, 3, 1, 1, 1, 4]
def baseStart_116772 : Nat := 118140960795 + 116772 * 2 ^ 59
def prefixEnd_116772 : Nat := 4983230072969 + 3 ^ 40 * 116772 * 2
def baseEnd_116772 : Nat := 53297922655042100189317

theorem tailTrace_116772 : CollatzResearch.WordTrace tailWord_116772 prefixEnd_116772 53297922655042100189317 := by
  unfold tailWord_116772
  simp only [CollatzResearch.WordTrace]
  refine ⟨2129512366481230957480285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2839349821974974609973713 2129512366481230957480285)
  ·
    refine ⟨798567137430461609055107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2129512366481230957480285 798567137430461609055107)
    ·
      refine ⟨1197850706145692413582661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 798567137430461609055107 1197850706145692413582661)
      ·
        refine ⟨224597007402317327546749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1197850706145692413582661 224597007402317327546749)
        ·
          refine ⟨84223877775868997830031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224597007402317327546749 84223877775868997830031)
          ·
            refine ⟨126335816663803496745047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84223877775868997830031 126335816663803496745047)
            ·
              refine ⟨189503724995705245117571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126335816663803496745047 189503724995705245117571)
              ·
                refine ⟨284255587493557867676357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189503724995705245117571 284255587493557867676357)
                ·
                  refine ⟨53297922655042100189317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 284255587493557867676357 53297922655042100189317)
                  ·
                    rfl

theorem cell20_116772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_116772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116772 prefixEnd_116772 := by exact prefixLift 116772
  have htrace : WordTrace (prefixWord ++ tailWord_116772) baseStart_116772 baseEnd_116772 := by
    simpa [prefixWord, tailWord_116772, baseEnd_116772] using wordTrace_append hprefix tailTrace_116772
  have hstable : (prefixWord ++ tailWord_116772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116772).length < 2 ^ (prefixWord ++ tailWord_116772).sum := by decide
  have hdescent : baseEnd_116772 < baseStart_116772 := by decide
  rcases family_descends (prefixWord ++ tailWord_116772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116786 : List Nat := [3, 2, 1, 1, 2, 5, 2, 1, 3]
def baseStart_116786 : Nat := 118140960795 + 116786 * 2 ^ 59
def prefixEnd_116786 : Nat := 4983230072969 + 3 ^ 40 * 116786 * 2
def baseEnd_116786 : Nat := 53304312636520273722593

theorem tailTrace_116786 : CollatzResearch.WordTrace tailWord_116786 prefixEnd_116786 53304312636520273722593 := by
  unfold tailWord_116786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1064883838727935576492553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2839690236607828203980141 1064883838727935576492553)
  ·
    refine ⟨798662879045951682369415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1064883838727935576492553 798662879045951682369415)
    ·
      refine ⟨1197994318568927523554123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 798662879045951682369415 1197994318568927523554123)
      ·
        refine ⟨1796991477853391285331185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1197994318568927523554123 1796991477853391285331185)
        ·
          refine ⟨1347743608390043463998389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1796991477853391285331185 1347743608390043463998389)
          ·
            refine ⟨126350963286566574749849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1347743608390043463998389 126350963286566574749849)
            ·
              refine ⟨94763222464924931062387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126350963286566574749849 94763222464924931062387)
              ·
                refine ⟨142144833697387396593581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94763222464924931062387 142144833697387396593581)
                ·
                  refine ⟨53304312636520273722593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142144833697387396593581 53304312636520273722593)
                  ·
                    rfl

theorem cell20_116786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_116786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116786 prefixEnd_116786 := by exact prefixLift 116786
  have htrace : WordTrace (prefixWord ++ tailWord_116786) baseStart_116786 baseEnd_116786 := by
    simpa [prefixWord, tailWord_116786, baseEnd_116786] using wordTrace_append hprefix tailTrace_116786
  have hstable : (prefixWord ++ tailWord_116786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116786).length < 2 ^ (prefixWord ++ tailWord_116786).sum := by decide
  have hdescent : baseEnd_116786 < baseStart_116786 := by decide
  rcases family_descends (prefixWord ++ tailWord_116786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116797 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 6]
def baseStart_116797 : Nat := 118140960795 + 116797 * 2 ^ 59
def prefixEnd_116797 : Nat := 4983230072969 + 3 ^ 40 * 116797 * 2
def baseEnd_116797 : Nat := 53309333336253124355881

theorem tailTrace_116797 : CollatzResearch.WordTrace tailWord_116797 prefixEnd_116797 53309333336253124355881 := by
  unfold tailWord_116797
  simp only [CollatzResearch.WordTrace]
  refine ⟨4259936557871891184620645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2839957705247927456413763 4259936557871891184620645)
  ·
    refine ⟨798738104600979597116371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4259936557871891184620645 798738104600979597116371)
    ·
      refine ⟨1198107156901469395674557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 798738104600979597116371 1198107156901469395674557)
      ·
        refine ⟨449290183838051023377959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1198107156901469395674557 449290183838051023377959)
        ·
          refine ⟨673935275757076535066939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449290183838051023377959 673935275757076535066939)
          ·
            refine ⟨1010902913635614802600409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673935275757076535066939 1010902913635614802600409)
            ·
              refine ⟨758177185226711101950307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1010902913635614802600409 758177185226711101950307)
              ·
                refine ⟨1137265777840066652925461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758177185226711101950307 1137265777840066652925461)
                ·
                  refine ⟨53309333336253124355881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1137265777840066652925461 53309333336253124355881)
                  ·
                    rfl

theorem cell20_116797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_116797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116797 prefixEnd_116797 := by exact prefixLift 116797
  have htrace : WordTrace (prefixWord ++ tailWord_116797) baseStart_116797 baseEnd_116797 := by
    simpa [prefixWord, tailWord_116797, baseEnd_116797] using wordTrace_append hprefix tailTrace_116797
  have hstable : (prefixWord ++ tailWord_116797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116797).length < 2 ^ (prefixWord ++ tailWord_116797).sum := by decide
  have hdescent : baseEnd_116797 < baseStart_116797 := by decide
  rcases family_descends (prefixWord ++ tailWord_116797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116869 : List Nat := [1, 3, 1, 1, 5, 2, 2, 3, 2]
def baseStart_116869 : Nat := 118140960795 + 116869 * 2 ^ 59
def prefixEnd_116869 : Nat := 4983230072969 + 3 ^ 40 * 116869 * 2
def baseEnd_116869 : Nat := 53342196098140873955587

theorem tailTrace_116869 : CollatzResearch.WordTrace tailWord_116869 prefixEnd_116869 53342196098140873955587 := by
  unfold tailWord_116869
  simp only [CollatzResearch.WordTrace]
  refine ⟨4262562613611047481241661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2841708409074031654161107 4262562613611047481241661)
  ·
    refine ⟨1598460980104142805465623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4262562613611047481241661 1598460980104142805465623)
    ·
      refine ⟨2397691470156214208198435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1598460980104142805465623 2397691470156214208198435)
      ·
        refine ⟨3596537205234321312297653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2397691470156214208198435 3596537205234321312297653)
        ·
          refine ⟨337175362990717623027905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3596537205234321312297653 337175362990717623027905)
          ·
            refine ⟨252881522243038217270929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337175362990717623027905 252881522243038217270929)
            ·
              refine ⟨189661141682278662953197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252881522243038217270929 189661141682278662953197)
              ·
                refine ⟨71122928130854498607449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189661141682278662953197 71122928130854498607449)
                ·
                  refine ⟨53342196098140873955587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71122928130854498607449 53342196098140873955587)
                  ·
                    rfl

theorem cell20_116869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_116869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116869 prefixEnd_116869 := by exact prefixLift 116869
  have htrace : WordTrace (prefixWord ++ tailWord_116869) baseStart_116869 baseEnd_116869 := by
    simpa [prefixWord, tailWord_116869, baseEnd_116869] using wordTrace_append hprefix tailTrace_116869
  have hstable : (prefixWord ++ tailWord_116869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116869).length < 2 ^ (prefixWord ++ tailWord_116869).sum := by decide
  have hdescent : baseEnd_116869 < baseStart_116869 := by decide
  rcases family_descends (prefixWord ++ tailWord_116869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116900 : List Nat := [2, 3, 1, 2, 4, 1, 3, 1, 3]
def baseStart_116900 : Nat := 118140960795 + 116900 * 2 ^ 59
def prefixEnd_116900 : Nat := 4983230072969 + 3 ^ 40 * 116900 * 2
def baseEnd_116900 : Nat := 53356345342842543922127

theorem tailTrace_116900 : CollatzResearch.WordTrace tailWord_116900 prefixEnd_116900 53356345342842543922127 := by
  unfold tailWord_116900
  simp only [CollatzResearch.WordTrace]
  refine ⟨2131846638249369887810077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2842462184332493183746769 2131846638249369887810077)
  ·
    refine ⟨799442489343513707928779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2131846638249369887810077 799442489343513707928779)
    ·
      refine ⟨1199163734015270561893169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 799442489343513707928779 1199163734015270561893169)
      ·
        refine ⟨899372800511452921419877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1199163734015270561893169 899372800511452921419877)
        ·
          refine ⟨168632400095897422766227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 899372800511452921419877 168632400095897422766227)
          ·
            refine ⟨252948600143846134149341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168632400095897422766227 252948600143846134149341)
            ·
              refine ⟨94855725053942300306003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252948600143846134149341 94855725053942300306003)
              ·
                refine ⟨142283587580913450459005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94855725053942300306003 142283587580913450459005)
                ·
                  refine ⟨53356345342842543922127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142283587580913450459005 53356345342842543922127)
                  ·
                    rfl

theorem cell20_116900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_116900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116900 prefixEnd_116900 := by exact prefixLift 116900
  have htrace : WordTrace (prefixWord ++ tailWord_116900) baseStart_116900 baseEnd_116900 := by
    simpa [prefixWord, tailWord_116900, baseEnd_116900] using wordTrace_append hprefix tailTrace_116900
  have hstable : (prefixWord ++ tailWord_116900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116900).length < 2 ^ (prefixWord ++ tailWord_116900).sum := by decide
  have hdescent : baseEnd_116900 < baseStart_116900 := by decide
  rcases family_descends (prefixWord ++ tailWord_116900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116910 : List Nat := [4, 1, 4, 2, 1, 2, 2, 4]
def baseStart_116910 : Nat := 118140960795 + 116910 * 2 ^ 59
def prefixEnd_116910 : Nat := 4983230072969 + 3 ^ 40 * 116910 * 2
def baseEnd_116910 : Nat := 17786969871775651196251

theorem tailTrace_116910 : CollatzResearch.WordTrace tailWord_116910 prefixEnd_116910 17786969871775651196251 := by
  unfold tailWord_116910
  simp only [CollatzResearch.WordTrace]
  refine ⟨533007250807813935435523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2842705337641674322322789 533007250807813935435523)
  ·
    refine ⟨799510876211720903153285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 533007250807813935435523 799510876211720903153285)
    ·
      refine ⟨149908289289697669341241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 799510876211720903153285 149908289289697669341241)
      ·
        refine ⟨112431216967273252005931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149908289289697669341241 112431216967273252005931)
        ·
          refine ⟨168646825450909878008897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112431216967273252005931 168646825450909878008897)
          ·
            refine ⟨126485119088182408506673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168646825450909878008897 126485119088182408506673)
            ·
              refine ⟨94863839316136806380005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126485119088182408506673 94863839316136806380005)
              ·
                refine ⟨17786969871775651196251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94863839316136806380005 17786969871775651196251)
                ·
                  rfl

theorem cell20_116910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_116910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116910 prefixEnd_116910 := by exact prefixLift 116910
  have htrace : WordTrace (prefixWord ++ tailWord_116910) baseStart_116910 baseEnd_116910 := by
    simpa [prefixWord, tailWord_116910, baseEnd_116910] using wordTrace_append hprefix tailTrace_116910
  have hstable : (prefixWord ++ tailWord_116910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116910).length < 2 ^ (prefixWord ++ tailWord_116910).sum := by decide
  have hdescent : baseEnd_116910 < baseStart_116910 := by decide
  rcases family_descends (prefixWord ++ tailWord_116910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116924 : List Nat := [2, 2, 2, 3, 3, 2, 1, 3, 2]
def baseStart_116924 : Nat := 118140960795 + 116924 * 2 ^ 59
def prefixEnd_116924 : Nat := 4983230072969 + 3 ^ 40 * 116924 * 2
def baseEnd_116924 : Nat := 53367299596805127122029

theorem tailTrace_116924 : CollatzResearch.WordTrace tailWord_116924 prefixEnd_116924 53367299596805127122029 := by
  unfold tailWord_116924
  simp only [CollatzResearch.WordTrace]
  refine ⟨2132284314205895937246913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2843045752274527916329217 2132284314205895937246913)
  ·
    refine ⟨1599213235654421952935185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2132284314205895937246913 1599213235654421952935185)
    ·
      refine ⟨1199409926740816464701389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1599213235654421952935185 1199409926740816464701389)
      ·
        refine ⟨449778722527806174263021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1199409926740816464701389 449778722527806174263021)
        ·
          refine ⟨168667020947927315348633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449778722527806174263021 168667020947927315348633)
          ·
            refine ⟨126500265710945486511475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168667020947927315348633 126500265710945486511475)
            ·
              refine ⟨189750398566418229767213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126500265710945486511475 189750398566418229767213)
              ·
                refine ⟨71156399462406836162705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189750398566418229767213 71156399462406836162705)
                ·
                  refine ⟨53367299596805127122029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71156399462406836162705 53367299596805127122029)
                  ·
                    rfl

theorem cell20_116924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_116924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116924 prefixEnd_116924 := by exact prefixLift 116924
  have htrace : WordTrace (prefixWord ++ tailWord_116924) baseStart_116924 baseEnd_116924 := by
    simpa [prefixWord, tailWord_116924, baseEnd_116924] using wordTrace_append hprefix tailTrace_116924
  have hstable : (prefixWord ++ tailWord_116924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116924).length < 2 ^ (prefixWord ++ tailWord_116924).sum := by decide
  have hdescent : baseEnd_116924 < baseStart_116924 := by decide
  rcases family_descends (prefixWord ++ tailWord_116924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116942 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_116942 : Nat := 118140960795 + 116942 * 2 ^ 59
def prefixEnd_116942 : Nat := 4983230072969 + 3 ^ 40 * 116942 * 2
def baseEnd_116942 : Nat := 53375515287277064521955

theorem tailTrace_116942 : CollatzResearch.WordTrace tailWord_116942 prefixEnd_116942 53375515287277064521955 := by
  unfold tailWord_116942
  simp only [CollatzResearch.WordTrace]
  refine ⟨533153142793322618581135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2843483428231053965766053 533153142793322618581135)
  ·
    refine ⟨799729714189983927871703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 533153142793322618581135 799729714189983927871703)
    ·
      refine ⟨1199594571284975891807555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 799729714189983927871703 1199594571284975891807555)
      ·
        refine ⟨1799391856927463837711333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1199594571284975891807555 1799391856927463837711333)
        ·
          refine ⟨337385973173899469570875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1799391856927463837711333 337385973173899469570875)
          ·
            refine ⟨506078959760849204356313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337385973173899469570875 506078959760849204356313)
            ·
              refine ⟨379559219820636903267235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506078959760849204356313 379559219820636903267235)
              ·
                refine ⟨569338829730955354900853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379559219820636903267235 569338829730955354900853)
                ·
                  refine ⟨53375515287277064521955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 569338829730955354900853 53375515287277064521955)
                  ·
                    rfl

theorem cell20_116942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_116942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_116942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_116942 prefixEnd_116942 := by exact prefixLift 116942
  have htrace : WordTrace (prefixWord ++ tailWord_116942) baseStart_116942 baseEnd_116942 := by
    simpa [prefixWord, tailWord_116942, baseEnd_116942] using wordTrace_append hprefix tailTrace_116942
  have hstable : (prefixWord ++ tailWord_116942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116942).length < 2 ^ (prefixWord ++ tailWord_116942).sum := by decide
  have hdescent : baseEnd_116942 < baseStart_116942 := by decide
  rcases family_descends (prefixWord ++ tailWord_116942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117000 : List Nat := [2, 1, 3, 2, 3, 3, 2, 2, 2]
def baseStart_117000 : Nat := 118140960795 + 117000 * 2 ^ 59
def prefixEnd_117000 : Nat := 4983230072969 + 3 ^ 40 * 117000 * 2
def baseEnd_117000 : Nat := 53401988067686640588385

theorem tailTrace_117000 : CollatzResearch.WordTrace tailWord_117000 prefixEnd_117000 53401988067686640588385 := by
  unfold tailWord_117000
  simp only [CollatzResearch.WordTrace]
  refine ⟨2133670288068228427130227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2844893717424304569506969 2133670288068228427130227)
  ·
    refine ⟨3200505432102342640695341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2133670288068228427130227 3200505432102342640695341)
    ·
      refine ⟨1200189537038378490260753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3200505432102342640695341 1200189537038378490260753)
      ·
        refine ⟨900142152778783867695565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1200189537038378490260753 900142152778783867695565)
        ·
          refine ⟨337553307292043950385837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 900142152778783867695565 337553307292043950385837)
          ·
            refine ⟨126582490234516481394689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 337553307292043950385837 126582490234516481394689)
            ·
              refine ⟨94936867675887361046017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126582490234516481394689 94936867675887361046017)
              ·
                refine ⟨71202650756915520784513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94936867675887361046017 71202650756915520784513)
                ·
                  refine ⟨53401988067686640588385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71202650756915520784513 53401988067686640588385)
                  ·
                    rfl

theorem cell20_117000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 2].length) (baseStart_117000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117000 prefixEnd_117000 := by exact prefixLift 117000
  have htrace : WordTrace (prefixWord ++ tailWord_117000) baseStart_117000 baseEnd_117000 := by
    simpa [prefixWord, tailWord_117000, baseEnd_117000] using wordTrace_append hprefix tailTrace_117000
  have hstable : (prefixWord ++ tailWord_117000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117000).length < 2 ^ (prefixWord ++ tailWord_117000).sum := by decide
  have hdescent : baseEnd_117000 < baseStart_117000 := by decide
  rcases family_descends (prefixWord ++ tailWord_117000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117004 : List Nat := [2, 2, 1, 2, 2, 2, 3, 4, 2]
def baseStart_117004 : Nat := 118140960795 + 117004 * 2 ^ 59
def prefixEnd_117004 : Nat := 4983230072969 + 3 ^ 40 * 117004 * 2
def baseEnd_117004 : Nat := 53403813776680404455035

theorem tailTrace_117004 : CollatzResearch.WordTrace tailWord_117004 prefixEnd_117004 53403813776680404455035 := by
  unfold tailWord_117004
  simp only [CollatzResearch.WordTrace]
  refine ⟨2133743234060982768703033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2844990978747977024937377 2133743234060982768703033)
  ·
    refine ⟨1600307425545737076527275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2133743234060982768703033 1600307425545737076527275)
    ·
      refine ⟨2400461138318605614790913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1600307425545737076527275 2400461138318605614790913)
      ·
        refine ⟨1800345853738954211093185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2400461138318605614790913 1800345853738954211093185)
        ·
          refine ⟨1350259390304215658319889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1800345853738954211093185 1350259390304215658319889)
          ·
            refine ⟨1012694542728161743739917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1350259390304215658319889 1012694542728161743739917)
            ·
              refine ⟨379760453523060653902469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1012694542728161743739917 379760453523060653902469)
              ·
                refine ⟨71205085035573872606713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 379760453523060653902469 71205085035573872606713)
                ·
                  refine ⟨53403813776680404455035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71205085035573872606713 53403813776680404455035)
                  ·
                    rfl

theorem cell20_117004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_117004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117004 prefixEnd_117004 := by exact prefixLift 117004
  have htrace : WordTrace (prefixWord ++ tailWord_117004) baseStart_117004 baseEnd_117004 := by
    simpa [prefixWord, tailWord_117004, baseEnd_117004] using wordTrace_append hprefix tailTrace_117004
  have hstable : (prefixWord ++ tailWord_117004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117004).length < 2 ^ (prefixWord ++ tailWord_117004).sum := by decide
  have hdescent : baseEnd_117004 < baseStart_117004 := by decide
  rcases family_descends (prefixWord ++ tailWord_117004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117063 : List Nat := [1, 1, 4, 1, 2, 2, 4, 1, 4]
def baseStart_117063 : Nat := 118140960795 + 117063 * 2 ^ 59
def prefixEnd_117063 : Nat := 4983230072969 + 3 ^ 40 * 117063 * 2
def baseEnd_117063 : Nat := 53430742984338421488127

theorem tailTrace_117063 : CollatzResearch.WordTrace tailWord_117063 prefixEnd_117063 53430742984338421488127 := by
  unfold tailWord_117063
  simp only [CollatzResearch.WordTrace]
  refine ⟨4269638374908218613803843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2846425583272145742535895 4269638374908218613803843)
  ·
    refine ⟨6404457562362327920705765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4269638374908218613803843 6404457562362327920705765)
    ·
      refine ⟨1200835792942936485132331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6404457562362327920705765 1200835792942936485132331)
      ·
        refine ⟨1801253689414404727698497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1200835792942936485132331 1801253689414404727698497)
        ·
          refine ⟨1350940267060803545773873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1801253689414404727698497 1350940267060803545773873)
          ·
            refine ⟨1013205200295602659330405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1350940267060803545773873 1013205200295602659330405)
            ·
              refine ⟨189975975055425498624451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1013205200295602659330405 189975975055425498624451)
              ·
                refine ⟨284963962583138247936677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189975975055425498624451 284963962583138247936677)
                ·
                  refine ⟨53430742984338421488127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 284963962583138247936677 53430742984338421488127)
                  ·
                    rfl

theorem cell20_117063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 4].length) (baseStart_117063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117063 prefixEnd_117063 := by exact prefixLift 117063
  have htrace : WordTrace (prefixWord ++ tailWord_117063) baseStart_117063 baseEnd_117063 := by
    simpa [prefixWord, tailWord_117063, baseEnd_117063] using wordTrace_append hprefix tailTrace_117063
  have hstable : (prefixWord ++ tailWord_117063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117063).length < 2 ^ (prefixWord ++ tailWord_117063).sum := by decide
  have hdescent : baseEnd_117063 < baseStart_117063 := by decide
  rcases family_descends (prefixWord ++ tailWord_117063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117073 : List Nat := [1, 2, 2, 1, 4, 3, 3, 1, 3]
def baseStart_117073 : Nat := 118140960795 + 117073 * 2 ^ 59
def prefixEnd_117073 : Nat := 4983230072969 + 3 ^ 40 * 117073 * 2
def baseEnd_117073 : Nat := 53435307256822831154753

theorem tailTrace_117073 : CollatzResearch.WordTrace tailWord_117073 prefixEnd_117073 53435307256822831154753 := by
  unfold tailWord_117073
  simp only [CollatzResearch.WordTrace]
  refine ⟨4270003104871990321667873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2846668736581326881111915 4270003104871990321667873)
  ·
    refine ⟨3202502328653992741250905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4270003104871990321667873 3202502328653992741250905)
    ·
      refine ⟨2401876746490494555938179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3202502328653992741250905 2401876746490494555938179)
      ·
        refine ⟨3602815119735741833907269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2401876746490494555938179 3602815119735741833907269)
        ·
          refine ⟨675527834950451593857613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3602815119735741833907269 675527834950451593857613)
          ·
            refine ⟨253322938106419347696605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 675527834950451593857613 253322938106419347696605)
            ·
              refine ⟨94996101789907255386227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253322938106419347696605 94996101789907255386227)
              ·
                refine ⟨142494152684860883079341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94996101789907255386227 142494152684860883079341)
                ·
                  refine ⟨53435307256822831154753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142494152684860883079341 53435307256822831154753)
                  ·
                    rfl

theorem cell20_117073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 3].length) (baseStart_117073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117073 prefixEnd_117073 := by exact prefixLift 117073
  have htrace : WordTrace (prefixWord ++ tailWord_117073) baseStart_117073 baseEnd_117073 := by
    simpa [prefixWord, tailWord_117073, baseEnd_117073] using wordTrace_append hprefix tailTrace_117073
  have hstable : (prefixWord ++ tailWord_117073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117073).length < 2 ^ (prefixWord ++ tailWord_117073).sum := by decide
  have hdescent : baseEnd_117073 < baseStart_117073 := by decide
  rcases family_descends (prefixWord ++ tailWord_117073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117115 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 5]
def baseStart_117115 : Nat := 118140960795 + 117115 * 2 ^ 59
def prefixEnd_117115 : Nat := 4983230072969 + 3 ^ 40 * 117115 * 2
def baseEnd_117115 : Nat := 53454477201257351754581

theorem tailTrace_117115 : CollatzResearch.WordTrace tailWord_117115 prefixEnd_117115 53454477201257351754581 := by
  unfold tailWord_117115
  simp only [CollatzResearch.WordTrace]
  refine ⟨4271534970719831494696799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2847689980479887663131199 4271534970719831494696799)
  ·
    refine ⟨6407302456079747242045199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4271534970719831494696799 6407302456079747242045199)
    ·
      refine ⟨9610953684119620863067799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6407302456079747242045199 9610953684119620863067799)
      ·
        refine ⟨14416430526179431294601699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9610953684119620863067799 14416430526179431294601699)
        ·
          refine ⟨21624645789269146941902549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14416430526179431294601699 21624645789269146941902549)
          ·
            refine ⟨506827635685995631450841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 21624645789269146941902549 506827635685995631450841)
            ·
              refine ⟨380120726764496723588131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506827635685995631450841 380120726764496723588131)
              ·
                refine ⟨570181090146745085382197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380120726764496723588131 570181090146745085382197)
                ·
                  refine ⟨53454477201257351754581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 570181090146745085382197 53454477201257351754581)
                  ·
                    rfl

theorem cell20_117115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 5].length) (baseStart_117115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117115 prefixEnd_117115 := by exact prefixLift 117115
  have htrace : WordTrace (prefixWord ++ tailWord_117115) baseStart_117115 baseEnd_117115 := by
    simpa [prefixWord, tailWord_117115, baseEnd_117115] using wordTrace_append hprefix tailTrace_117115
  have hstable : (prefixWord ++ tailWord_117115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117115).length < 2 ^ (prefixWord ++ tailWord_117115).sum := by decide
  have hdescent : baseEnd_117115 < baseStart_117115 := by decide
  rcases family_descends (prefixWord ++ tailWord_117115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117132 : List Nat := [2, 2, 1, 2, 1, 5, 1, 3, 3]
def baseStart_117132 : Nat := 118140960795 + 117132 * 2 ^ 59
def prefixEnd_117132 : Nat := 4983230072969 + 3 ^ 40 * 117132 * 2
def baseEnd_117132 : Nat := 53462236464480848187845

theorem tailTrace_117132 : CollatzResearch.WordTrace tailWord_117132 prefixEnd_117132 53462236464480848187845 := by
  unfold tailWord_117132
  simp only [CollatzResearch.WordTrace]
  refine ⟨2136077505829121699032825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2848103341105495598710433 2136077505829121699032825)
  ·
    refine ⟨1602058129371841274274619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2136077505829121699032825 1602058129371841274274619)
    ·
      refine ⟨2403087194057761911411929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1602058129371841274274619 2403087194057761911411929)
      ·
        refine ⟨1802315395543321433558947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2403087194057761911411929 1802315395543321433558947)
        ·
          refine ⟨2703473093314982150338421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1802315395543321433558947 2703473093314982150338421)
          ·
            refine ⟨253450602498279576594227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2703473093314982150338421 253450602498279576594227)
            ·
              refine ⟨380175903747419364891341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253450602498279576594227 380175903747419364891341)
              ·
                refine ⟨142565963905282261834253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 380175903747419364891341 142565963905282261834253)
                ·
                  refine ⟨53462236464480848187845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142565963905282261834253 53462236464480848187845)
                  ·
                    rfl

theorem cell20_117132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_117132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117132 prefixEnd_117132 := by exact prefixLift 117132
  have htrace : WordTrace (prefixWord ++ tailWord_117132) baseStart_117132 baseEnd_117132 := by
    simpa [prefixWord, tailWord_117132, baseEnd_117132] using wordTrace_append hprefix tailTrace_117132
  have hstable : (prefixWord ++ tailWord_117132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117132).length < 2 ^ (prefixWord ++ tailWord_117132).sum := by decide
  have hdescent : baseEnd_117132 < baseStart_117132 := by decide
  rcases family_descends (prefixWord ++ tailWord_117132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117146 : List Nat := [3, 1, 1, 4, 1, 2, 2, 6]
def baseStart_117146 : Nat := 118140960795 + 117146 * 2 ^ 59
def prefixEnd_117146 : Nat := 4983230072969 + 3 ^ 40 * 117146 * 2
def baseEnd_117146 : Nat := 17822875481986340573707

theorem tailTrace_117146 : CollatzResearch.WordTrace tailWord_117146 prefixEnd_117146 17822875481986340573707 := by
  unfold tailWord_117146
  simp only [CollatzResearch.WordTrace]
  refine ⟨1068166408401880947268823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2848443755738349192716861 1068166408401880947268823)
  ·
    refine ⟨1602249612602821420903235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1068166408401880947268823 1602249612602821420903235)
    ·
      refine ⟨2403374418904232131354853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1602249612602821420903235 2403374418904232131354853)
      ·
        refine ⟨450632703544543524629035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2403374418904232131354853 450632703544543524629035)
        ·
          refine ⟨675949055316815286943553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450632703544543524629035 675949055316815286943553)
          ·
            refine ⟨506961791487611465207665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 675949055316815286943553 506961791487611465207665)
            ·
              refine ⟨380221343615708598905749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506961791487611465207665 380221343615708598905749)
              ·
                refine ⟨17822875481986340573707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 380221343615708598905749 17822875481986340573707)
                ·
                  rfl

theorem cell20_117146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_117146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117146 prefixEnd_117146 := by exact prefixLift 117146
  have htrace : WordTrace (prefixWord ++ tailWord_117146) baseStart_117146 baseEnd_117146 := by
    simpa [prefixWord, tailWord_117146, baseEnd_117146] using wordTrace_append hprefix tailTrace_117146
  have hstable : (prefixWord ++ tailWord_117146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117146).length < 2 ^ (prefixWord ++ tailWord_117146).sum := by decide
  have hdescent : baseEnd_117146 < baseStart_117146 := by decide
  rcases family_descends (prefixWord ++ tailWord_117146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117170 : List Nat := [3, 2, 1, 1, 1, 1, 6, 2, 3]
def baseStart_117170 : Nat := 118140960795 + 117170 * 2 ^ 59
def prefixEnd_117170 : Nat := 4983230072969 + 3 ^ 40 * 117170 * 2
def baseEnd_117170 : Nat := 53479580699921604921023

theorem tailTrace_117170 : CollatzResearch.WordTrace tailWord_117170 prefixEnd_117170 53479580699921604921023 := by
  unfold tailWord_117170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1068385246380143971987241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2849027323680383925299309 1068385246380143971987241)
  ·
    refine ⟨801288934785107978990431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1068385246380143971987241 801288934785107978990431)
    ·
      refine ⟨1201933402177661968485647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 801288934785107978990431 1201933402177661968485647)
      ·
        refine ⟨1802900103266492952728471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1201933402177661968485647 1802900103266492952728471)
        ·
          refine ⟨2704350154899739429092707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1802900103266492952728471 2704350154899739429092707)
          ·
            refine ⟨4056525232349609143639061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2704350154899739429092707 4056525232349609143639061)
            ·
              refine ⟨190149620266387928608081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4056525232349609143639061 190149620266387928608081)
              ·
                refine ⟨142612215199790946456061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190149620266387928608081 142612215199790946456061)
                ·
                  refine ⟨53479580699921604921023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142612215199790946456061 53479580699921604921023)
                  ·
                    rfl

theorem cell20_117170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_117170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117170 prefixEnd_117170 := by exact prefixLift 117170
  have htrace : WordTrace (prefixWord ++ tailWord_117170) baseStart_117170 baseEnd_117170 := by
    simpa [prefixWord, tailWord_117170, baseEnd_117170] using wordTrace_append hprefix tailTrace_117170
  have hstable : (prefixWord ++ tailWord_117170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117170).length < 2 ^ (prefixWord ++ tailWord_117170).sum := by decide
  have hdescent : baseEnd_117170 < baseStart_117170 := by decide
  rcases family_descends (prefixWord ++ tailWord_117170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117173 : List Nat := [1, 3, 3, 2, 3, 1, 1, 4, 2]
def baseStart_117173 : Nat := 118140960795 + 117173 * 2 ^ 59
def prefixEnd_117173 : Nat := 4983230072969 + 3 ^ 40 * 117173 * 2
def baseEnd_117173 : Nat := 53480949981666927821011

theorem tailTrace_117173 : CollatzResearch.WordTrace tailWord_117173 prefixEnd_117173 53480949981666927821011 := by
  unfold tailWord_117173
  simp only [CollatzResearch.WordTrace]
  refine ⟨4273650404509707400308173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2849100269673138266872115 4273650404509707400308173)
  ·
    refine ⟨1602618901691140275115565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4273650404509707400308173 1602618901691140275115565)
    ·
      refine ⟨600982088134177603168337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1602618901691140275115565 600982088134177603168337)
      ·
        refine ⟨450736566100633202376253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 600982088134177603168337 450736566100633202376253)
        ·
          refine ⟨169026212287737450891095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 450736566100633202376253 169026212287737450891095)
          ·
            refine ⟨253539318431606176336643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169026212287737450891095 253539318431606176336643)
            ·
              refine ⟨380308977647409264504965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253539318431606176336643 380308977647409264504965)
              ·
                refine ⟨71307933308889237094681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 380308977647409264504965 71307933308889237094681)
                ·
                  refine ⟨53480949981666927821011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71307933308889237094681 53480949981666927821011)
                  ·
                    rfl

theorem cell20_117173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_117173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117173 prefixEnd_117173 := by exact prefixLift 117173
  have htrace : WordTrace (prefixWord ++ tailWord_117173) baseStart_117173 baseEnd_117173 := by
    simpa [prefixWord, tailWord_117173, baseEnd_117173] using wordTrace_append hprefix tailTrace_117173
  have hstable : (prefixWord ++ tailWord_117173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117173).length < 2 ^ (prefixWord ++ tailWord_117173).sum := by decide
  have hdescent : baseEnd_117173 < baseStart_117173 := by decide
  rcases family_descends (prefixWord ++ tailWord_117173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117218 : List Nat := [3, 3, 3, 2, 1, 1, 7]
def baseStart_117218 : Nat := 118140960795 + 117218 * 2 ^ 59
def prefixEnd_117218 : Nat := 4983230072969 + 3 ^ 40 * 117218 * 2
def baseEnd_117218 : Nat := 5944609911982974591203

theorem tailTrace_117218 : CollatzResearch.WordTrace tailWord_117218 prefixEnd_117218 5944609911982974591203 := by
  unfold tailWord_117218
  simp only [CollatzResearch.WordTrace]
  refine ⟨1068822922336670021424077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2850194459564453390464205 1068822922336670021424077)
  ·
    refine ⟨400808595876251258034029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1068822922336670021424077 400808595876251258034029)
    ·
      refine ⟨150303223453594221762761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400808595876251258034029 150303223453594221762761)
      ·
        refine ⟨112727417590195666322071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150303223453594221762761 112727417590195666322071)
        ·
          refine ⟨169091126385293499483107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112727417590195666322071 169091126385293499483107)
          ·
            refine ⟨253636689577940249224661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169091126385293499483107 253636689577940249224661)
            ·
              refine ⟨5944609911982974591203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 253636689577940249224661 5944609911982974591203)
              ·
                rfl

theorem cell20_117218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 7].length) (baseStart_117218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117218 prefixEnd_117218 := by exact prefixLift 117218
  have htrace : WordTrace (prefixWord ++ tailWord_117218) baseStart_117218 baseEnd_117218 := by
    simpa [prefixWord, tailWord_117218, baseEnd_117218] using wordTrace_append hprefix tailTrace_117218
  have hstable : (prefixWord ++ tailWord_117218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117218).length < 2 ^ (prefixWord ++ tailWord_117218).sum := by decide
  have hdescent : baseEnd_117218 < baseStart_117218 := by decide
  rcases family_descends (prefixWord ++ tailWord_117218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117260 : List Nat := [2, 2, 1, 2, 4, 2, 1, 6]
def baseStart_117260 : Nat := 118140960795 + 117260 * 2 ^ 59
def prefixEnd_117260 : Nat := 4983230072969 + 3 ^ 40 * 117260 * 2
def baseEnd_117260 : Nat := 17840219717427097306885

theorem tailTrace_117260 : CollatzResearch.WordTrace tailWord_117260 prefixEnd_117260 17840219717427097306885 := by
  unfold tailWord_117260
  simp only [CollatzResearch.WordTrace]
  refine ⟨2138411777597260629362617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2851215703463014172483489 2138411777597260629362617)
  ·
    refine ⟨1603808833197945472021963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2138411777597260629362617 1603808833197945472021963)
    ·
      refine ⟨2405713249796918208032945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1603808833197945472021963 2405713249796918208032945)
      ·
        refine ⟨1804284937347688656024709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2405713249796918208032945 1804284937347688656024709)
        ·
          refine ⟨338303425752691623004633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1804284937347688656024709 338303425752691623004633)
          ·
            refine ⟨253727569314518717253475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338303425752691623004633 253727569314518717253475)
            ·
              refine ⟨380591353971778075880213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253727569314518717253475 380591353971778075880213)
              ·
                refine ⟨17840219717427097306885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 380591353971778075880213 17840219717427097306885)
                ·
                  rfl

theorem cell20_117260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_117260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117260 prefixEnd_117260 := by exact prefixLift 117260
  have htrace : WordTrace (prefixWord ++ tailWord_117260) baseStart_117260 baseEnd_117260 := by
    simpa [prefixWord, tailWord_117260, baseEnd_117260] using wordTrace_append hprefix tailTrace_117260
  have hstable : (prefixWord ++ tailWord_117260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117260).length < 2 ^ (prefixWord ++ tailWord_117260).sum := by decide
  have hdescent : baseEnd_117260 < baseStart_117260 := by decide
  rcases family_descends (prefixWord ++ tailWord_117260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117274 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_117274 : Nat := 118140960795 + 117274 * 2 ^ 59
def prefixEnd_117274 : Nat := 4983230072969 + 3 ^ 40 * 117274 * 2
def baseEnd_117274 : Nat := 53527049133759465453931

theorem tailTrace_117274 : CollatzResearch.WordTrace tailWord_117274 prefixEnd_117274 53527049133759465453931 := by
  unfold tailWord_117274
  simp only [CollatzResearch.WordTrace]
  refine ⟨1069333544285950412433719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2851556118095867766489917 1069333544285950412433719)
  ·
    refine ⟨1604000316428925618650579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1069333544285950412433719 1604000316428925618650579)
    ·
      refine ⟨2406000474643388427975869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1604000316428925618650579 2406000474643388427975869)
      ·
        refine ⟨902250177991270660490951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2406000474643388427975869 902250177991270660490951)
        ·
          refine ⟨1353375266986905990736427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902250177991270660490951 1353375266986905990736427)
          ·
            refine ⟨2030062900480358986104641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353375266986905990736427 2030062900480358986104641)
            ·
              refine ⟨1522547175360269239578481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2030062900480358986104641 1522547175360269239578481)
              ·
                refine ⟨1141910381520201929683861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1522547175360269239578481 1141910381520201929683861)
                ·
                  refine ⟨53527049133759465453931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1141910381520201929683861 53527049133759465453931)
                  ·
                    rfl

theorem cell20_117274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_117274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117274 prefixEnd_117274 := by exact prefixLift 117274
  have htrace : WordTrace (prefixWord ++ tailWord_117274) baseStart_117274 baseEnd_117274 := by
    simpa [prefixWord, tailWord_117274, baseEnd_117274] using wordTrace_append hprefix tailTrace_117274
  have hstable : (prefixWord ++ tailWord_117274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117274).length < 2 ^ (prefixWord ++ tailWord_117274).sum := by decide
  have hdescent : baseEnd_117274 < baseStart_117274 := by decide
  rcases family_descends (prefixWord ++ tailWord_117274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117291 : List Nat := [1, 1, 1, 1, 2, 1, 3, 8, 2]
def baseStart_117291 : Nat := 118140960795 + 117291 * 2 ^ 59
def prefixEnd_117291 : Nat := 4983230072969 + 3 ^ 40 * 117291 * 2
def baseEnd_117291 : Nat := 53534808396982961887195

theorem tailTrace_117291 : CollatzResearch.WordTrace tailWord_117291 prefixEnd_117291 53534808396982961887195 := by
  unfold tailWord_117291
  simp only [CollatzResearch.WordTrace]
  refine ⟨4277954218082213553103727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2851969478721475702069151 4277954218082213553103727)
  ·
    refine ⟨6416931327123320329655591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4277954218082213553103727 6416931327123320329655591)
    ·
      refine ⟨9625396990684980494483387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6416931327123320329655591 9625396990684980494483387)
      ·
        refine ⟨14438095486027470741725081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9625396990684980494483387 14438095486027470741725081)
        ·
          refine ⟨10828571614520603056293811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14438095486027470741725081 10828571614520603056293811)
          ·
            refine ⟨16242857421780904584440717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10828571614520603056293811 16242857421780904584440717)
            ·
              refine ⟨6091071533167839219165269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16242857421780904584440717 6091071533167839219165269)
              ·
                refine ⟨71379744529310615849593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6091071533167839219165269 71379744529310615849593)
                ·
                  refine ⟨53534808396982961887195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71379744529310615849593 53534808396982961887195)
                  ·
                    rfl

theorem cell20_117291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 2].length) (baseStart_117291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117291 prefixEnd_117291 := by exact prefixLift 117291
  have htrace : WordTrace (prefixWord ++ tailWord_117291) baseStart_117291 baseEnd_117291 := by
    simpa [prefixWord, tailWord_117291, baseEnd_117291] using wordTrace_append hprefix tailTrace_117291
  have hstable : (prefixWord ++ tailWord_117291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117291).length < 2 ^ (prefixWord ++ tailWord_117291).sum := by decide
  have hdescent : baseEnd_117291 < baseStart_117291 := by decide
  rcases family_descends (prefixWord ++ tailWord_117291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117293 : List Nat := [1, 5, 4, 1, 2, 1, 2, 1, 3]
def baseStart_117293 : Nat := 118140960795 + 117293 * 2 ^ 59
def prefixEnd_117293 : Nat := 4983230072969 + 3 ^ 40 * 117293 * 2
def baseEnd_117293 : Nat := 53535721251479843820521

theorem tailTrace_117293 : CollatzResearch.WordTrace tailWord_117293 prefixEnd_117293 53535721251479843820521 := by
  unfold tailWord_117293
  simp only [CollatzResearch.WordTrace]
  refine ⟨4278027164074967894676533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2852018109383311929784355 4278027164074967894676533)
  ·
    refine ⟨401065046632028240125925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4278027164074967894676533 401065046632028240125925)
    ·
      refine ⟨75199696243505295023611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 401065046632028240125925 75199696243505295023611)
      ·
        refine ⟨112799544365257942535417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75199696243505295023611 112799544365257942535417)
        ·
          refine ⟨84599658273943456901563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112799544365257942535417 84599658273943456901563)
          ·
            refine ⟨126899487410915185352345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84599658273943456901563 126899487410915185352345)
            ·
              refine ⟨95174615558186389014259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126899487410915185352345 95174615558186389014259)
              ·
                refine ⟨142761923337279583521389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95174615558186389014259 142761923337279583521389)
                ·
                  refine ⟨53535721251479843820521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142761923337279583521389 53535721251479843820521)
                  ·
                    rfl

theorem cell20_117293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_117293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117293 prefixEnd_117293 := by exact prefixLift 117293
  have htrace : WordTrace (prefixWord ++ tailWord_117293) baseStart_117293 baseEnd_117293 := by
    simpa [prefixWord, tailWord_117293, baseEnd_117293] using wordTrace_append hprefix tailTrace_117293
  have hstable : (prefixWord ++ tailWord_117293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117293).length < 2 ^ (prefixWord ++ tailWord_117293).sum := by decide
  have hdescent : baseEnd_117293 < baseStart_117293 := by decide
  rcases family_descends (prefixWord ++ tailWord_117293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117312 : List Nat := [2, 1, 1, 2, 2, 2, 2, 4, 4]
def baseStart_117312 : Nat := 118140960795 + 117312 * 2 ^ 59
def prefixEnd_117312 : Nat := 4983230072969 + 3 ^ 40 * 117312 * 2
def baseEnd_117312 : Nat := 53544393369200222187109

theorem tailTrace_117312 : CollatzResearch.WordTrace tailWord_117312 prefixEnd_117312 53544393369200222187109 := by
  unfold tailWord_117312
  simp only [CollatzResearch.WordTrace]
  refine ⟨2139360075503067069809095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2852480100670756093078793 2139360075503067069809095)
  ·
    refine ⟨3209040113254600604713643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2139360075503067069809095 3209040113254600604713643)
    ·
      refine ⟨4813560169881900907070465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3209040113254600604713643 4813560169881900907070465)
      ·
        refine ⟨3610170127411425680302849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4813560169881900907070465 3610170127411425680302849)
        ·
          refine ⟨2707627595558569260227137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3610170127411425680302849 2707627595558569260227137)
          ·
            refine ⟨2030720696668926945170353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2707627595558569260227137 2030720696668926945170353)
            ·
              refine ⟨1523040522501695208877765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2030720696668926945170353 1523040522501695208877765)
              ·
                refine ⟨285570097969067851664581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1523040522501695208877765 285570097969067851664581)
                ·
                  refine ⟨53544393369200222187109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 285570097969067851664581 53544393369200222187109)
                  ·
                    rfl

theorem cell20_117312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_117312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117312 prefixEnd_117312 := by exact prefixLift 117312
  have htrace : WordTrace (prefixWord ++ tailWord_117312) baseStart_117312 baseEnd_117312 := by
    simpa [prefixWord, tailWord_117312, baseEnd_117312] using wordTrace_append hprefix tailTrace_117312
  have hstable : (prefixWord ++ tailWord_117312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117312).length < 2 ^ (prefixWord ++ tailWord_117312).sum := by decide
  have hdescent : baseEnd_117312 < baseStart_117312 := by decide
  rcases family_descends (prefixWord ++ tailWord_117312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117422 : List Nat := [4, 1, 4, 1, 1, 1, 2, 2, 4]
def baseStart_117422 : Nat := 118140960795 + 117422 * 2 ^ 59
def prefixEnd_117422 : Nat := 4983230072969 + 3 ^ 40 * 117422 * 2
def baseEnd_117422 : Nat := 53594600366528728519993

theorem tailTrace_117422 : CollatzResearch.WordTrace tailWord_117422 prefixEnd_117422 53594600366528728519993 := by
  unfold tailWord_117422
  simp only [CollatzResearch.WordTrace]
  refine ⟨535341522575952865765315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2855154787071748617415013 535341522575952865765315)
  ·
    refine ⟨803012283863929298647973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 535341522575952865765315 803012283863929298647973)
    ·
      refine ⟨150564803224486743496495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 803012283863929298647973 150564803224486743496495)
      ·
        refine ⟨225847204836730115244743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150564803224486743496495 225847204836730115244743)
        ·
          refine ⟨338770807255095172867115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225847204836730115244743 338770807255095172867115)
          ·
            refine ⟨508156210882642759300673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338770807255095172867115 508156210882642759300673)
            ·
              refine ⟨381117158161982069475505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 508156210882642759300673 381117158161982069475505)
              ·
                refine ⟨285837868621486552106629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381117158161982069475505 285837868621486552106629)
                ·
                  refine ⟨53594600366528728519993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 285837868621486552106629 53594600366528728519993)
                  ·
                    rfl

theorem cell20_117422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_117422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117422 prefixEnd_117422 := by exact prefixLift 117422
  have htrace : WordTrace (prefixWord ++ tailWord_117422) baseStart_117422 baseEnd_117422 := by
    simpa [prefixWord, tailWord_117422, baseEnd_117422] using wordTrace_append hprefix tailTrace_117422
  have hstable : (prefixWord ++ tailWord_117422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117422).length < 2 ^ (prefixWord ++ tailWord_117422).sum := by decide
  have hdescent : baseEnd_117422 < baseStart_117422 := by decide
  rcases family_descends (prefixWord ++ tailWord_117422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117425 : List Nat := [1, 2, 2, 6, 2, 1, 2, 4]
def baseStart_117425 : Nat := 118140960795 + 117425 * 2 ^ 59
def prefixEnd_117425 : Nat := 4983230072969 + 3 ^ 40 * 117425 * 2
def baseEnd_117425 : Nat := 17865323216091350473327

theorem tailTrace_117425 : CollatzResearch.WordTrace tailWord_117425 prefixEnd_117425 17865323216091350473327 := by
  unfold tailWord_117425
  simp only [CollatzResearch.WordTrace]
  refine ⟨4282841599596754438481729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2855227733064502958987819 4282841599596754438481729)
  ·
    refine ⟨3212131199697565828861297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4282841599596754438481729 3212131199697565828861297)
    ·
      refine ⟨2409098399773174371645973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3212131199697565828861297 2409098399773174371645973)
      ·
        refine ⟨112926487489367548670905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2409098399773174371645973 112926487489367548670905)
        ·
          refine ⟨84694865617025661503179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112926487489367548670905 84694865617025661503179)
          ·
            refine ⟨127042298425538492254769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84694865617025661503179 127042298425538492254769)
            ·
              refine ⟨95281723819153869191077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127042298425538492254769 95281723819153869191077)
              ·
                refine ⟨17865323216091350473327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95281723819153869191077 17865323216091350473327)
                ·
                  rfl

theorem cell20_117425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 4].length) (baseStart_117425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117425 prefixEnd_117425 := by exact prefixLift 117425
  have htrace : WordTrace (prefixWord ++ tailWord_117425) baseStart_117425 baseEnd_117425 := by
    simpa [prefixWord, tailWord_117425, baseEnd_117425] using wordTrace_append hprefix tailTrace_117425
  have hstable : (prefixWord ++ tailWord_117425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117425).length < 2 ^ (prefixWord ++ tailWord_117425).sum := by decide
  have hdescent : baseEnd_117425 < baseStart_117425 := by decide
  rcases family_descends (prefixWord ++ tailWord_117425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117429 : List Nat := [1, 3, 3, 3, 1, 1, 4, 4]
def baseStart_117429 : Nat := 118140960795 + 117429 * 2 ^ 59
def prefixEnd_117429 : Nat := 4983230072969 + 3 ^ 40 * 117429 * 2
def baseEnd_117429 : Nat := 17865931785755938428877

theorem tailTrace_117429 : CollatzResearch.WordTrace tailWord_117429 prefixEnd_117429 17865931785755938428877 := by
  unfold tailWord_117429
  simp only [CollatzResearch.WordTrace]
  refine ⟨4282987491582263121627341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2855324994388175414418227 4282987491582263121627341)
  ·
    refine ⟨1606120309343348670610253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4282987491582263121627341 1606120309343348670610253)
    ·
      refine ⟨602295116003755751478845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1606120309343348670610253 602295116003755751478845)
      ·
        refine ⟨225860668501408406804567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 602295116003755751478845 225860668501408406804567)
        ·
          refine ⟨338791002752112610206851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225860668501408406804567 338791002752112610206851)
          ·
            refine ⟨508186504128168915310277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338791002752112610206851 508186504128168915310277)
            ·
              refine ⟨95284969524031671620677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 508186504128168915310277 95284969524031671620677)
              ·
                refine ⟨17865931785755938428877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95284969524031671620677 17865931785755938428877)
                ·
                  rfl

theorem cell20_117429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 4].length) (baseStart_117429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117429 prefixEnd_117429 := by exact prefixLift 117429
  have htrace : WordTrace (prefixWord ++ tailWord_117429) baseStart_117429 baseEnd_117429 := by
    simpa [prefixWord, tailWord_117429, baseEnd_117429] using wordTrace_append hprefix tailTrace_117429
  have hstable : (prefixWord ++ tailWord_117429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117429).length < 2 ^ (prefixWord ++ tailWord_117429).sum := by decide
  have hdescent : baseEnd_117429 < baseStart_117429 := by decide
  rcases family_descends (prefixWord ++ tailWord_117429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117450 : List Nat := [3, 1, 2, 1, 4, 3, 6]
def baseStart_117450 : Nat := 118140960795 + 117450 * 2 ^ 59
def prefixEnd_117450 : Nat := 4983230072969 + 3 ^ 40 * 117450 * 2
def baseEnd_117450 : Nat := 5956375592165008398505

theorem tailTrace_117450 : CollatzResearch.WordTrace tailWord_117450 prefixEnd_117450 5956375592165008398505 := by
  unfold tailWord_117450
  simp only [CollatzResearch.WordTrace]
  refine ⟨1070938356126545927035451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2855835616337455805427869 1070938356126545927035451)
  ·
    refine ⟨1606407534189818890553177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1070938356126545927035451 1606407534189818890553177)
    ·
      refine ⟨1204805650642364167914883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1606407534189818890553177 1204805650642364167914883)
      ·
        refine ⟨1807208475963546251872325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1204805650642364167914883 1807208475963546251872325)
        ·
          refine ⟨338851589243164922226061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1807208475963546251872325 338851589243164922226061)
          ·
            refine ⟨127069345966186845834773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338851589243164922226061 127069345966186845834773)
            ·
              refine ⟨5956375592165008398505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127069345966186845834773 5956375592165008398505)
              ·
                rfl

theorem cell20_117450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 6].length) (baseStart_117450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117450 prefixEnd_117450 := by exact prefixLift 117450
  have htrace : WordTrace (prefixWord ++ tailWord_117450) baseStart_117450 baseEnd_117450 := by
    simpa [prefixWord, tailWord_117450, baseEnd_117450] using wordTrace_append hprefix tailTrace_117450
  have hstable : (prefixWord ++ tailWord_117450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117450).length < 2 ^ (prefixWord ++ tailWord_117450).sum := by decide
  have hdescent : baseEnd_117450 < baseStart_117450 := by decide
  rcases family_descends (prefixWord ++ tailWord_117450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117457 : List Nat := [1, 2, 2, 1, 2, 3, 2, 4, 3]
def baseStart_117457 : Nat := 118140960795 + 117457 * 2 ^ 59
def prefixEnd_117457 : Nat := 4983230072969 + 3 ^ 40 * 117457 * 2
def baseEnd_117457 : Nat := 53610575320224162353183

theorem tailTrace_117457 : CollatzResearch.WordTrace tailWord_117457 prefixEnd_117457 53610575320224162353183 := by
  unfold tailWord_117457
  simp only [CollatzResearch.WordTrace]
  refine ⟨4284008735480823903646625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2856005823653882602431083 4284008735480823903646625)
  ·
    refine ⟨3213006551610617927734969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4284008735480823903646625 3213006551610617927734969)
    ·
      refine ⟨2409754913707963445801227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3213006551610617927734969 2409754913707963445801227)
      ·
        refine ⟨3614632370561945168701841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2409754913707963445801227 3614632370561945168701841)
        ·
          refine ⟨2710974277921458876526381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3614632370561945168701841 2710974277921458876526381)
          ·
            refine ⟨1016615354220547078697393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2710974277921458876526381 1016615354220547078697393)
            ·
              refine ⟨762461515665410309023045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1016615354220547078697393 762461515665410309023045)
              ·
                refine ⟨142961534187264432941821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 762461515665410309023045 142961534187264432941821)
                ·
                  refine ⟨53610575320224162353183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142961534187264432941821 53610575320224162353183)
                  ·
                    rfl

theorem cell20_117457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 3].length) (baseStart_117457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117457 prefixEnd_117457 := by exact prefixLift 117457
  have htrace : WordTrace (prefixWord ++ tailWord_117457) baseStart_117457 baseEnd_117457 := by
    simpa [prefixWord, tailWord_117457, baseEnd_117457] using wordTrace_append hprefix tailTrace_117457
  have hstable : (prefixWord ++ tailWord_117457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117457).length < 2 ^ (prefixWord ++ tailWord_117457).sum := by decide
  have hdescent : baseEnd_117457 < baseStart_117457 := by decide
  rcases family_descends (prefixWord ++ tailWord_117457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117471 : List Nat := [1, 1, 2, 3, 2, 3, 1, 7]
def baseStart_117471 : Nat := 118140960795 + 117471 * 2 ^ 59
def prefixEnd_117471 : Nat := 4983230072969 + 3 ^ 40 * 117471 * 2
def baseEnd_117471 : Nat := 17872321767234111962153

theorem tailTrace_117471 : CollatzResearch.WordTrace tailWord_117471 prefixEnd_117471 17872321767234111962153 := by
  unfold tailWord_117471
  simp only [CollatzResearch.WordTrace]
  refine ⟨4284519357430104294656267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2856346238286736196437511 4284519357430104294656267)
  ·
    refine ⟨6426779036145156441984401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4284519357430104294656267 6426779036145156441984401)
    ·
      refine ⟨4820084277108867331488301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6426779036145156441984401 4820084277108867331488301)
      ·
        refine ⟨1807531603915825249308113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4820084277108867331488301 1807531603915825249308113)
        ·
          refine ⟨1355648702936868936981085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1807531603915825249308113 1355648702936868936981085)
          ·
            refine ⟨508368263601325851367907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1355648702936868936981085 508368263601325851367907)
            ·
              refine ⟨762552395401988777051861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508368263601325851367907 762552395401988777051861)
              ·
                refine ⟨17872321767234111962153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 762552395401988777051861 17872321767234111962153)
                ·
                  rfl

theorem cell20_117471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 7].length) (baseStart_117471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117471 prefixEnd_117471 := by exact prefixLift 117471
  have htrace : WordTrace (prefixWord ++ tailWord_117471) baseStart_117471 baseEnd_117471 := by
    simpa [prefixWord, tailWord_117471, baseEnd_117471] using wordTrace_append hprefix tailTrace_117471
  have hstable : (prefixWord ++ tailWord_117471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117471).length < 2 ^ (prefixWord ++ tailWord_117471).sum := by decide
  have hdescent : baseEnd_117471 < baseStart_117471 := by decide
  rcases family_descends (prefixWord ++ tailWord_117471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117512 : List Nat := [2, 1, 3, 2, 2, 3, 2, 2, 3]
def baseStart_117512 : Nat := 118140960795 + 117512 * 2 ^ 59
def prefixEnd_117512 : Nat := 4983230072969 + 3 ^ 40 * 117512 * 2
def baseEnd_117512 : Nat := 53635678818888415519625

theorem tailTrace_117512 : CollatzResearch.WordTrace tailWord_117512 prefixEnd_117512 53635678818888415519625 := by
  unfold tailWord_117512
  simp only [CollatzResearch.WordTrace]
  refine ⟨2143007375140784148449395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2857343166854378864599193 2143007375140784148449395)
  ·
    refine ⟨3214511062711176222674093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2143007375140784148449395 3214511062711176222674093)
    ·
      refine ⟨1205441648516691083502785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3214511062711176222674093 1205441648516691083502785)
      ·
        refine ⟨904081236387518312627089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1205441648516691083502785 904081236387518312627089)
        ·
          refine ⟨678060927290638734470317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 904081236387518312627089 678060927290638734470317)
          ·
            refine ⟨254272847733989525426369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 678060927290638734470317 254272847733989525426369)
            ·
              refine ⟨190704635800492144069777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254272847733989525426369 190704635800492144069777)
              ·
                refine ⟨143028476850369108052333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190704635800492144069777 143028476850369108052333)
                ·
                  refine ⟨53635678818888415519625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143028476850369108052333 53635678818888415519625)
                  ·
                    rfl

theorem cell20_117512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 3].length) (baseStart_117512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117512 prefixEnd_117512 := by exact prefixLift 117512
  have htrace : WordTrace (prefixWord ++ tailWord_117512) baseStart_117512 baseEnd_117512 := by
    simpa [prefixWord, tailWord_117512, baseEnd_117512] using wordTrace_append hprefix tailTrace_117512
  have hstable : (prefixWord ++ tailWord_117512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117512).length < 2 ^ (prefixWord ++ tailWord_117512).sum := by decide
  have hdescent : baseEnd_117512 < baseStart_117512 := by decide
  rcases family_descends (prefixWord ++ tailWord_117512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117519 : List Nat := [1, 1, 2, 1, 1, 1, 7, 4, 2]
def baseStart_117519 : Nat := 118140960795 + 117519 * 2 ^ 59
def prefixEnd_117519 : Nat := 4983230072969 + 3 ^ 40 * 117519 * 2
def baseEnd_117519 : Nat := 53638873809627502286263

theorem tailTrace_117519 : CollatzResearch.WordTrace tailWord_117519 prefixEnd_117519 53638873809627502286263 := by
  unfold tailWord_117519
  simp only [CollatzResearch.WordTrace]
  refine ⟨4286270061256208492403611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2857513374170805661602407 4286270061256208492403611)
  ·
    refine ⟨6429405091884312738605417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4286270061256208492403611 6429405091884312738605417)
    ·
      refine ⟨4822053818913234553954063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6429405091884312738605417 4822053818913234553954063)
      ·
        refine ⟨7233080728369851830931095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4822053818913234553954063 7233080728369851830931095)
        ·
          refine ⟨10849621092554777746396643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7233080728369851830931095 10849621092554777746396643)
          ·
            refine ⟨16274431638832166619594965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10849621092554777746396643 16274431638832166619594965)
            ·
              refine ⟨381431991535128905146757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 16274431638832166619594965 381431991535128905146757)
              ·
                refine ⟨71518498412836669715017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 381431991535128905146757 71518498412836669715017)
                ·
                  refine ⟨53638873809627502286263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71518498412836669715017 53638873809627502286263)
                  ·
                    rfl

theorem cell20_117519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 2].length) (baseStart_117519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117519 prefixEnd_117519 := by exact prefixLift 117519
  have htrace : WordTrace (prefixWord ++ tailWord_117519) baseStart_117519 baseEnd_117519 := by
    simpa [prefixWord, tailWord_117519, baseEnd_117519] using wordTrace_append hprefix tailTrace_117519
  have hstable : (prefixWord ++ tailWord_117519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117519).length < 2 ^ (prefixWord ++ tailWord_117519).sum := by decide
  have hdescent : baseEnd_117519 < baseStart_117519 := by decide
  rcases family_descends (prefixWord ++ tailWord_117519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117522 : List Nat := [3, 2, 4, 1, 2, 2, 1, 5]
def baseStart_117522 : Nat := 118140960795 + 117522 * 2 ^ 59
def prefixEnd_117522 : Nat := 4983230072969 + 3 ^ 40 * 117522 * 2
def baseEnd_117522 : Nat := 17880081030457608395417

theorem tailTrace_117522 : CollatzResearch.WordTrace tailWord_117522 prefixEnd_117522 17880081030457608395417 := by
  unfold tailWord_117522
  simp only [CollatzResearch.WordTrace]
  refine ⟨1071594870061335001190705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2857586320163560003175213 1071594870061335001190705)
  ·
    refine ⟨803696152546001250893029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1071594870061335001190705 803696152546001250893029)
    ·
      refine ⟨150693028602375234542443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 803696152546001250893029 150693028602375234542443)
      ·
        refine ⟨226039542903562851813665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150693028602375234542443 226039542903562851813665)
        ·
          refine ⟨169529657177672138860249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226039542903562851813665 169529657177672138860249)
          ·
            refine ⟨127147242883254104145187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169529657177672138860249 127147242883254104145187)
            ·
              refine ⟨190720864324881156217781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127147242883254104145187 190720864324881156217781)
              ·
                refine ⟨17880081030457608395417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190720864324881156217781 17880081030457608395417)
                ·
                  rfl

theorem cell20_117522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_117522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117522 prefixEnd_117522 := by exact prefixLift 117522
  have htrace : WordTrace (prefixWord ++ tailWord_117522) baseStart_117522 baseEnd_117522 := by
    simpa [prefixWord, tailWord_117522, baseEnd_117522] using wordTrace_append hprefix tailTrace_117522
  have hstable : (prefixWord ++ tailWord_117522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117522).length < 2 ^ (prefixWord ++ tailWord_117522).sum := by decide
  have hdescent : baseEnd_117522 < baseStart_117522 := by decide
  rcases family_descends (prefixWord ++ tailWord_117522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117640 : List Nat := [2, 1, 3, 3, 2, 2, 2, 5]
def baseStart_117640 : Nat := 118140960795 + 117640 * 2 ^ 59
def prefixEnd_117640 : Nat := 4983230072969 + 3 ^ 40 * 117640 * 2
def baseEnd_117640 : Nat := 17898033835562953084145

theorem tailTrace_117640 : CollatzResearch.WordTrace tailWord_117640 prefixEnd_117640 17898033835562953084145 := by
  unfold tailWord_117640
  simp only [CollatzResearch.WordTrace]
  refine ⟨2145341646908923078779187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2860455529211897438372249 2145341646908923078779187)
  ·
    refine ⟨3218012470363384618168781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2145341646908923078779187 3218012470363384618168781)
    ·
      refine ⟨1206754676386269231813293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3218012470363384618168781 1206754676386269231813293)
      ·
        refine ⟨452533003644850961929985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1206754676386269231813293 452533003644850961929985)
        ·
          refine ⟨339399752733638221447489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452533003644850961929985 339399752733638221447489)
          ·
            refine ⟨254549814550228666085617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339399752733638221447489 254549814550228666085617)
            ·
              refine ⟨190912360912671499564213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254549814550228666085617 190912360912671499564213)
              ·
                refine ⟨17898033835562953084145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190912360912671499564213 17898033835562953084145)
                ·
                  rfl

theorem cell20_117640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_117640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117640 prefixEnd_117640 := by exact prefixLift 117640
  have htrace : WordTrace (prefixWord ++ tailWord_117640) baseStart_117640 baseEnd_117640 := by
    simpa [prefixWord, tailWord_117640, baseEnd_117640] using wordTrace_append hprefix tailTrace_117640
  have hstable : (prefixWord ++ tailWord_117640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117640).length < 2 ^ (prefixWord ++ tailWord_117640).sum := by decide
  have hdescent : baseEnd_117640 < baseStart_117640 := by decide
  rcases family_descends (prefixWord ++ tailWord_117640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117661 : List Nat := [1, 4, 2, 1, 2, 1, 1, 8]
def baseStart_117661 : Nat := 118140960795 + 117661 * 2 ^ 59
def prefixEnd_117661 : Nat := 4983230072969 + 3 ^ 40 * 117661 * 2
def baseEnd_117661 : Nat := 17901228826302039850783

theorem tailTrace_117661 : CollatzResearch.WordTrace tailWord_117661 prefixEnd_117661 17901228826302039850783 := by
  unfold tailWord_117661
  simp only [CollatzResearch.WordTrace]
  refine ⟨4291449226741766744072837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2860966151161177829381891 4291449226741766744072837)
  ·
    refine ⟨804646730014081264513657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4291449226741766744072837 804646730014081264513657)
    ·
      refine ⟨603485047510560948385243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 804646730014081264513657 603485047510560948385243)
      ·
        refine ⟨905227571265841422577865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603485047510560948385243 905227571265841422577865)
        ·
          refine ⟨678920678449381066933399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 905227571265841422577865 678920678449381066933399)
          ·
            refine ⟨1018381017674071600400099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678920678449381066933399 1018381017674071600400099)
            ·
              refine ⟨1527571526511107400600149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1018381017674071600400099 1527571526511107400600149)
              ·
                refine ⟨17901228826302039850783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1527571526511107400600149 17901228826302039850783)
                ·
                  rfl

theorem cell20_117661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 8].length) (baseStart_117661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117661 prefixEnd_117661 := by exact prefixLift 117661
  have htrace : WordTrace (prefixWord ++ tailWord_117661) baseStart_117661 baseEnd_117661 := by
    simpa [prefixWord, tailWord_117661, baseEnd_117661] using wordTrace_append hprefix tailTrace_117661
  have hstable : (prefixWord ++ tailWord_117661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117661).length < 2 ^ (prefixWord ++ tailWord_117661).sum := by decide
  have hdescent : baseEnd_117661 < baseStart_117661 := by decide
  rcases family_descends (prefixWord ++ tailWord_117661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117675 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 6]
def baseStart_117675 : Nat := 118140960795 + 117675 * 2 ^ 59
def prefixEnd_117675 : Nat := 4983230072969 + 3 ^ 40 * 117675 * 2
def baseEnd_117675 : Nat := 53710076460384293085625

theorem tailTrace_117675 : CollatzResearch.WordTrace tailWord_117675 prefixEnd_117675 53710076460384293085625 := by
  unfold tailWord_117675
  simp only [CollatzResearch.WordTrace]
  refine ⟨4291959848691047135082479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2861306565794031423388319 4291959848691047135082479)
  ·
    refine ⟨6437939773036570702623719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4291959848691047135082479 6437939773036570702623719)
    ·
      refine ⟨9656909659554856053935579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6437939773036570702623719 9656909659554856053935579)
      ·
        refine ⟨14485364489332284080903369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9656909659554856053935579 14485364489332284080903369)
        ·
          refine ⟨10864023366999213060677527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14485364489332284080903369 10864023366999213060677527)
          ·
            refine ⟨16296035050498819591016291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10864023366999213060677527 16296035050498819591016291)
            ·
              refine ⟨24444052575748229386524437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16296035050498819591016291 24444052575748229386524437)
              ·
                refine ⟨1145814964488198252493333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24444052575748229386524437 1145814964488198252493333)
                ·
                  refine ⟨53710076460384293085625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1145814964488198252493333 53710076460384293085625)
                  ·
                    rfl

theorem cell20_117675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_117675 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117675 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117675 prefixEnd_117675 := by exact prefixLift 117675
  have htrace : WordTrace (prefixWord ++ tailWord_117675) baseStart_117675 baseEnd_117675 := by
    simpa [prefixWord, tailWord_117675, baseEnd_117675] using wordTrace_append hprefix tailTrace_117675
  have hstable : (prefixWord ++ tailWord_117675).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117675).length < 2 ^ (prefixWord ++ tailWord_117675).sum := by decide
  have hdescent : baseEnd_117675 < baseStart_117675 := by decide
  rcases family_descends (prefixWord ++ tailWord_117675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117678 : List Nat := [4, 1, 5, 10]
def baseStart_117678 : Nat := 118140960795 + 117678 * 2 ^ 59
def prefixEnd_117678 : Nat := 4983230072969 + 3 ^ 40 * 117678 * 2
def baseEnd_117678 : Nat := 221034756140451094591

theorem tailTrace_117678 : CollatzResearch.WordTrace tailWord_117678 prefixEnd_117678 221034756140451094591 := by
  unfold tailWord_117678
  simp only [CollatzResearch.WordTrace]
  refine ⟨536508658460022330930211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2861379511786785764961125 536508658460022330930211)
  ·
    refine ⟨804762987690033496395317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 536508658460022330930211 804762987690033496395317)
    ·
      refine ⟨75446530095940640287061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 804762987690033496395317 75446530095940640287061)
      ·
        refine ⟨221034756140451094591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 75446530095940640287061 221034756140451094591)
        ·
          rfl

theorem cell20_117678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 10].length) (baseStart_117678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117678 prefixEnd_117678 := by exact prefixLift 117678
  have htrace : WordTrace (prefixWord ++ tailWord_117678) baseStart_117678 baseEnd_117678 := by
    simpa [prefixWord, tailWord_117678, baseEnd_117678] using wordTrace_append hprefix tailTrace_117678
  have hstable : (prefixWord ++ tailWord_117678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117678).length < 2 ^ (prefixWord ++ tailWord_117678).sum := by decide
  have hdescent : baseEnd_117678 < baseStart_117678 := by decide
  rcases family_descends (prefixWord ++ tailWord_117678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117684 : List Nat := [2, 5, 2, 1, 1, 1, 4, 2, 2]
def baseStart_117684 : Nat := 118140960795 + 117684 * 2 ^ 59
def prefixEnd_117684 : Nat := 4983230072969 + 3 ^ 40 * 117684 * 2
def baseEnd_117684 : Nat := 53714184305620261785589

theorem tailTrace_117684 : CollatzResearch.WordTrace tailWord_117684 prefixEnd_117684 53714184305620261785589 := by
  unfold tailWord_117684
  simp only [CollatzResearch.WordTrace]
  refine ⟨2146144052829220836080053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2861525403772294448106737 2146144052829220836080053)
  ·
    refine ⟨201201004952739453382505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2146144052829220836080053 201201004952739453382505)
    ·
      refine ⟨150900753714554590036879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201201004952739453382505 150900753714554590036879)
      ·
        refine ⟨226351130571831885055319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150900753714554590036879 226351130571831885055319)
        ·
          refine ⟨339526695857747827582979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226351130571831885055319 339526695857747827582979)
          ·
            refine ⟨509290043786621741374469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339526695857747827582979 509290043786621741374469)
            ·
              refine ⟨95491883209991576507713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 509290043786621741374469 95491883209991576507713)
              ·
                refine ⟨71618912407493682380785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95491883209991576507713 71618912407493682380785)
                ·
                  refine ⟨53714184305620261785589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71618912407493682380785 53714184305620261785589)
                  ·
                    rfl

theorem cell20_117684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_117684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117684 prefixEnd_117684 := by exact prefixLift 117684
  have htrace : WordTrace (prefixWord ++ tailWord_117684) baseStart_117684 baseEnd_117684 := by
    simpa [prefixWord, tailWord_117684, baseEnd_117684] using wordTrace_append hprefix tailTrace_117684
  have hstable : (prefixWord ++ tailWord_117684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117684).length < 2 ^ (prefixWord ++ tailWord_117684).sum := by decide
  have hdescent : baseEnd_117684 < baseStart_117684 := by decide
  rcases family_descends (prefixWord ++ tailWord_117684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117688 : List Nat := [2, 1, 2, 1, 2, 4, 4, 2, 2]
def baseStart_117688 : Nat := 118140960795 + 117688 * 2 ^ 59
def prefixEnd_117688 : Nat := 4983230072969 + 3 ^ 40 * 117688 * 2
def baseEnd_117688 : Nat := 53716010014614025652239

theorem tailTrace_117688 : CollatzResearch.WordTrace tailWord_117688 prefixEnd_117688 53716010014614025652239 := by
  unfold tailWord_117688
  simp only [CollatzResearch.WordTrace]
  refine ⟨2146216998821975177652859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2861622665095966903537145 2146216998821975177652859)
  ·
    refine ⟨3219325498232962766479289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2146216998821975177652859 3219325498232962766479289)
    ·
      refine ⟨2414494123674722074859467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3219325498232962766479289 2414494123674722074859467)
      ·
        refine ⟨3621741185512083112289201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2414494123674722074859467 3621741185512083112289201)
        ·
          refine ⟨2716305889134062334216901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3621741185512083112289201 2716305889134062334216901)
          ·
            refine ⟨509307354212636687665669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2716305889134062334216901 509307354212636687665669)
            ·
              refine ⟨95495128914869378937313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 509307354212636687665669 95495128914869378937313)
              ·
                refine ⟨71621346686152034202985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95495128914869378937313 71621346686152034202985)
                ·
                  refine ⟨53716010014614025652239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71621346686152034202985 53716010014614025652239)
                  ·
                    rfl

theorem cell20_117688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 2].length) (baseStart_117688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117688 prefixEnd_117688 := by exact prefixLift 117688
  have htrace : WordTrace (prefixWord ++ tailWord_117688) baseStart_117688 baseEnd_117688 := by
    simpa [prefixWord, tailWord_117688, baseEnd_117688] using wordTrace_append hprefix tailTrace_117688
  have hstable : (prefixWord ++ tailWord_117688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117688).length < 2 ^ (prefixWord ++ tailWord_117688).sum := by decide
  have hdescent : baseEnd_117688 < baseStart_117688 := by decide
  rcases family_descends (prefixWord ++ tailWord_117688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117706 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_117706 : Nat := 118140960795 + 117706 * 2 ^ 59
def prefixEnd_117706 : Nat := 4983230072969 + 3 ^ 40 * 117706 * 2
def baseEnd_117706 : Nat := 53724225705085963052165

theorem tailTrace_117706 : CollatzResearch.WordTrace tailWord_117706 prefixEnd_117706 53724225705085963052165 := by
  unfold tailWord_117706
  simp only [CollatzResearch.WordTrace]
  refine ⟨1073272627894684857365243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2862060341052492952973981 1073272627894684857365243)
  ·
    refine ⟨1609908941842027286047865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1073272627894684857365243 1609908941842027286047865)
    ·
      refine ⟨1207431706381520464535899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1609908941842027286047865 1207431706381520464535899)
      ·
        refine ⟨1811147559572280696803849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1207431706381520464535899 1811147559572280696803849)
        ·
          refine ⟨1358360669679210522602887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1811147559572280696803849 1358360669679210522602887)
          ·
            refine ⟨2037541004518815783904331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1358360669679210522602887 2037541004518815783904331)
            ·
              refine ⟨3056311506778223675856497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2037541004518815783904331 3056311506778223675856497)
              ·
                refine ⟨2292233630083667756892373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3056311506778223675856497 2292233630083667756892373)
                ·
                  refine ⟨53724225705085963052165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2292233630083667756892373 53724225705085963052165)
                  ·
                    rfl

theorem cell20_117706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_117706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117706 prefixEnd_117706 := by exact prefixLift 117706
  have htrace : WordTrace (prefixWord ++ tailWord_117706) baseStart_117706 baseEnd_117706 := by
    simpa [prefixWord, tailWord_117706, baseEnd_117706] using wordTrace_append hprefix tailTrace_117706
  have hstable : (prefixWord ++ tailWord_117706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117706).length < 2 ^ (prefixWord ++ tailWord_117706).sum := by decide
  have hdescent : baseEnd_117706 < baseStart_117706 := by decide
  rcases family_descends (prefixWord ++ tailWord_117706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117768 : List Nat := [2, 1, 3, 2, 1, 3, 2, 2, 4]
def baseStart_117768 : Nat := 118140960795 + 117768 * 2 ^ 59
def prefixEnd_117768 : Nat := 4983230072969 + 3 ^ 40 * 117768 * 2
def baseEnd_117768 : Nat := 53752524194489302985245

theorem tailTrace_117768 : CollatzResearch.WordTrace tailWord_117768 prefixEnd_117768 53752524194489302985245 := by
  unfold tailWord_117768
  simp only [CollatzResearch.WordTrace]
  refine ⟨2147675918677062009108979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2863567891569416012145305 2147675918677062009108979)
  ·
    refine ⟨3221513878015593013663469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2147675918677062009108979 3221513878015593013663469)
    ·
      refine ⟨1208067704255847380123801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3221513878015593013663469 1208067704255847380123801)
      ·
        refine ⟨906050778191885535092851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1208067704255847380123801 906050778191885535092851)
        ·
          refine ⟨1359076167287828302639277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906050778191885535092851 1359076167287828302639277)
          ·
            refine ⟨509653562732935613489729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1359076167287828302639277 509653562732935613489729)
            ·
              refine ⟨382240172049701710117297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509653562732935613489729 382240172049701710117297)
              ·
                refine ⟨286680129037276282587973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382240172049701710117297 286680129037276282587973)
                ·
                  refine ⟨53752524194489302985245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 286680129037276282587973 53752524194489302985245)
                  ·
                    rfl

theorem cell20_117768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_117768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117768 prefixEnd_117768 := by exact prefixLift 117768
  have htrace : WordTrace (prefixWord ++ tailWord_117768) baseStart_117768 baseEnd_117768 := by
    simpa [prefixWord, tailWord_117768, baseEnd_117768] using wordTrace_append hprefix tailTrace_117768
  have hstable : (prefixWord ++ tailWord_117768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117768).length < 2 ^ (prefixWord ++ tailWord_117768).sum := by decide
  have hdescent : baseEnd_117768 < baseStart_117768 := by decide
  rcases family_descends (prefixWord ++ tailWord_117768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117785 : List Nat := [1, 2, 1, 2, 1, 1, 7, 3, 2]
def baseStart_117785 : Nat := 118140960795 + 117785 * 2 ^ 59
def prefixEnd_117785 : Nat := 4983230072969 + 3 ^ 40 * 117785 * 2
def baseEnd_117785 : Nat := 53760283457712799418509

theorem tailTrace_117785 : CollatzResearch.WordTrace tailWord_117785 prefixEnd_117785 53760283457712799418509 := by
  unfold tailWord_117785
  simp only [CollatzResearch.WordTrace]
  refine ⟨4295971878292535921586809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2863981252195023947724539 4295971878292535921586809)
  ·
    refine ⟨3221978908719401941190107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4295971878292535921586809 3221978908719401941190107)
    ·
      refine ⟨4832968363079102911785161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3221978908719401941190107 4832968363079102911785161)
      ·
        refine ⟨3624726272309327183838871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4832968363079102911785161 3624726272309327183838871)
        ·
          refine ⟨5437089408463990775758307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3624726272309327183838871 5437089408463990775758307)
          ·
            refine ⟨8155634112695986163637461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5437089408463990775758307 8155634112695986163637461)
            ·
              refine ⟨191147674516312175710253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 8155634112695986163637461 191147674516312175710253)
              ·
                refine ⟨71680377943617065891345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191147674516312175710253 71680377943617065891345)
                ·
                  refine ⟨53760283457712799418509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71680377943617065891345 53760283457712799418509)
                  ·
                    rfl

theorem cell20_117785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 2].length) (baseStart_117785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117785 prefixEnd_117785 := by exact prefixLift 117785
  have htrace : WordTrace (prefixWord ++ tailWord_117785) baseStart_117785 baseEnd_117785 := by
    simpa [prefixWord, tailWord_117785, baseEnd_117785] using wordTrace_append hprefix tailTrace_117785
  have hstable : (prefixWord ++ tailWord_117785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117785).length < 2 ^ (prefixWord ++ tailWord_117785).sum := by decide
  have hdescent : baseEnd_117785 < baseStart_117785 := by decide
  rcases family_descends (prefixWord ++ tailWord_117785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117802 : List Nat := [3, 1, 4, 1, 3, 2, 1, 1, 4]
def baseStart_117802 : Nat := 118140960795 + 117802 * 2 ^ 59
def prefixEnd_117802 : Nat := 4983230072969 + 3 ^ 40 * 117802 * 2
def baseEnd_117802 : Nat := 53768042720936295851773

theorem tailTrace_117802 : CollatzResearch.WordTrace tailWord_117802 prefixEnd_117802 53768042720936295851773 := by
  unfold tailWord_117802
  simp only [CollatzResearch.WordTrace]
  refine ⟨1074147979807736956238915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2864394612820631883303773 1074147979807736956238915)
  ·
    refine ⟨1611221969711605434358373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1074147979807736956238915 1611221969711605434358373)
    ·
      refine ⟨302104119320926018942195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1611221969711605434358373 302104119320926018942195)
      ·
        refine ⟨453156178981389028413293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302104119320926018942195 453156178981389028413293)
        ·
          refine ⟨169933567118020885654985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 453156178981389028413293 169933567118020885654985)
          ·
            refine ⟨127450175338515664241239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169933567118020885654985 127450175338515664241239)
            ·
              refine ⟨191175263007773496361859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127450175338515664241239 191175263007773496361859)
              ·
                refine ⟨286762894511660244542789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191175263007773496361859 286762894511660244542789)
                ·
                  refine ⟨53768042720936295851773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 286762894511660244542789 53768042720936295851773)
                  ·
                    rfl

theorem cell20_117802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_117802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117802 prefixEnd_117802 := by exact prefixLift 117802
  have htrace : WordTrace (prefixWord ++ tailWord_117802) baseStart_117802 baseEnd_117802 := by
    simpa [prefixWord, tailWord_117802, baseEnd_117802] using wordTrace_append hprefix tailTrace_117802
  have hstable : (prefixWord ++ tailWord_117802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117802).length < 2 ^ (prefixWord ++ tailWord_117802).sum := by decide
  have hdescent : baseEnd_117802 < baseStart_117802 := by decide
  rcases family_descends (prefixWord ++ tailWord_117802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117812 : List Nat := [2, 5, 1, 2, 1, 3, 2, 1, 3]
def baseStart_117812 : Nat := 118140960795 + 117812 * 2 ^ 59
def prefixEnd_117812 : Nat := 4983230072969 + 3 ^ 40 * 117812 * 2
def baseEnd_117812 : Nat := 53772606993420705518399

theorem tailTrace_117812 : CollatzResearch.WordTrace tailWord_117812 prefixEnd_117812 53772606993420705518399 := by
  unfold tailWord_117812
  simp only [CollatzResearch.WordTrace]
  refine ⟨2148478324597359766409845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2864637766129813021879793 2148478324597359766409845)
  ·
    refine ⟨201419842931002478100923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2148478324597359766409845 201419842931002478100923)
    ·
      refine ⟨302129764396503717151385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201419842931002478100923 302129764396503717151385)
      ·
        refine ⟨226597323297377787863539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302129764396503717151385 226597323297377787863539)
        ·
          refine ⟨339895984946066681795309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226597323297377787863539 339895984946066681795309)
          ·
            refine ⟨127460994354775005673241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 339895984946066681795309 127460994354775005673241)
            ·
              refine ⟨95595745766081254254931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127460994354775005673241 95595745766081254254931)
              ·
                refine ⟨143393618649121881382397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95595745766081254254931 143393618649121881382397)
                ·
                  refine ⟨53772606993420705518399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143393618649121881382397 53772606993420705518399)
                  ·
                    rfl

theorem cell20_117812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_117812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117812 prefixEnd_117812 := by exact prefixLift 117812
  have htrace : WordTrace (prefixWord ++ tailWord_117812) baseStart_117812 baseEnd_117812 := by
    simpa [prefixWord, tailWord_117812, baseEnd_117812] using wordTrace_append hprefix tailTrace_117812
  have hstable : (prefixWord ++ tailWord_117812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117812).length < 2 ^ (prefixWord ++ tailWord_117812).sum := by decide
  have hdescent : baseEnd_117812 < baseStart_117812 := by decide
  rcases family_descends (prefixWord ++ tailWord_117812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117816 : List Nat := [2, 1, 2, 1, 5, 1, 4, 1, 3]
def baseStart_117816 : Nat := 118140960795 + 117816 * 2 ^ 59
def prefixEnd_117816 : Nat := 4983230072969 + 3 ^ 40 * 117816 * 2
def baseEnd_117816 : Nat := 53774432702414469385049

theorem tailTrace_117816 : CollatzResearch.WordTrace tailWord_117816 prefixEnd_117816 53774432702414469385049 := by
  unfold tailWord_117816
  simp only [CollatzResearch.WordTrace]
  refine ⟨2148551270590114107982651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2864735027453485477310201 2148551270590114107982651)
  ·
    refine ⟨3222826905885171161973977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2148551270590114107982651 3222826905885171161973977)
    ·
      refine ⟨2417120179413878371480483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3222826905885171161973977 2417120179413878371480483)
      ·
        refine ⟨3625680269120817557220725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2417120179413878371480483 3625680269120817557220725)
        ·
          refine ⟨339907525230076645989443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3625680269120817557220725 339907525230076645989443)
          ·
            refine ⟨509861287845114968984165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339907525230076645989443 509861287845114968984165)
            ·
              refine ⟨95598991470959056684531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 509861287845114968984165 95598991470959056684531)
              ·
                refine ⟨143398487206438585026797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95598991470959056684531 143398487206438585026797)
                ·
                  refine ⟨53774432702414469385049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143398487206438585026797 53774432702414469385049)
                  ·
                    rfl

theorem cell20_117816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 3].length) (baseStart_117816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117816 prefixEnd_117816 := by exact prefixLift 117816
  have htrace : WordTrace (prefixWord ++ tailWord_117816) baseStart_117816 baseEnd_117816 := by
    simpa [prefixWord, tailWord_117816, baseEnd_117816] using wordTrace_append hprefix tailTrace_117816
  have hstable : (prefixWord ++ tailWord_117816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117816).length < 2 ^ (prefixWord ++ tailWord_117816).sum := by decide
  have hdescent : baseEnd_117816 < baseStart_117816 := by decide
  rcases family_descends (prefixWord ++ tailWord_117816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117827 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 6]
def baseStart_117827 : Nat := 118140960795 + 117827 * 2 ^ 59
def prefixEnd_117827 : Nat := 4983230072969 + 3 ^ 40 * 117827 * 2
def baseEnd_117827 : Nat := 53779453402147320018337

theorem tailTrace_117827 : CollatzResearch.WordTrace tailWord_117827 prefixEnd_117827 53779453402147320018337 := by
  unfold tailWord_117827
  simp only [CollatzResearch.WordTrace]
  refine ⟨4297503744140377094615735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2865002496093584729743823 4297503744140377094615735)
  ·
    refine ⟨6446255616210565641923603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4297503744140377094615735 6446255616210565641923603)
    ·
      refine ⟨9669383424315848462885405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6446255616210565641923603 9669383424315848462885405)
      ·
        refine ⟨3626018784118443173582027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9669383424315848462885405 3626018784118443173582027)
        ·
          refine ⟨5439028176177664760373041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3626018784118443173582027 5439028176177664760373041)
          ·
            refine ⟨4079271132133248570279781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5439028176177664760373041 4079271132133248570279781)
            ·
              refine ⟨764863337274984106927459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4079271132133248570279781 764863337274984106927459)
              ·
                refine ⟨1147295005912476160391189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764863337274984106927459 1147295005912476160391189)
                ·
                  refine ⟨53779453402147320018337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1147295005912476160391189 53779453402147320018337)
                  ·
                    rfl

theorem cell20_117827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_117827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117827 prefixEnd_117827 := by exact prefixLift 117827
  have htrace : WordTrace (prefixWord ++ tailWord_117827) baseStart_117827 baseEnd_117827 := by
    simpa [prefixWord, tailWord_117827, baseEnd_117827] using wordTrace_append hprefix tailTrace_117827
  have hstable : (prefixWord ++ tailWord_117827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117827).length < 2 ^ (prefixWord ++ tailWord_117827).sum := by decide
  have hdescent : baseEnd_117827 < baseStart_117827 := by decide
  rcases family_descends (prefixWord ++ tailWord_117827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117853 : List Nat := [1, 4, 4, 1, 3, 1, 2, 2, 2]
def baseStart_117853 : Nat := 118140960795 + 117853 * 2 ^ 59
def prefixEnd_117853 : Nat := 4983230072969 + 3 ^ 40 * 117853 * 2
def baseEnd_117853 : Nat := 53791320510606785151565

theorem tailTrace_117853 : CollatzResearch.WordTrace tailWord_117853 prefixEnd_117853 53791320510606785151565 := by
  unfold tailWord_117853
  simp only [CollatzResearch.WordTrace]
  refine ⟨4298452042046183535062213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2865634694697455690041475 4298452042046183535062213)
  ·
    refine ⟨805959757883659412824165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4298452042046183535062213 805959757883659412824165)
    ·
      refine ⟨151117454603186139904531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 805959757883659412824165 151117454603186139904531)
      ·
        refine ⟨226676181904779209856797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151117454603186139904531 226676181904779209856797)
        ·
          refine ⟨85003568214292203696299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226676181904779209856797 85003568214292203696299)
          ·
            refine ⟨127505352321438305544449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85003568214292203696299 127505352321438305544449)
            ·
              refine ⟨95629014241078729158337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127505352321438305544449 95629014241078729158337)
              ·
                refine ⟨71721760680809046868753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95629014241078729158337 71721760680809046868753)
                ·
                  refine ⟨53791320510606785151565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71721760680809046868753 53791320510606785151565)
                  ·
                    rfl

theorem cell20_117853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_117853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117853 prefixEnd_117853 := by exact prefixLift 117853
  have htrace : WordTrace (prefixWord ++ tailWord_117853) baseStart_117853 baseEnd_117853 := by
    simpa [prefixWord, tailWord_117853, baseEnd_117853] using wordTrace_append hprefix tailTrace_117853
  have hstable : (prefixWord ++ tailWord_117853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117853).length < 2 ^ (prefixWord ++ tailWord_117853).sum := by decide
  have hdescent : baseEnd_117853 < baseStart_117853 := by decide
  rcases family_descends (prefixWord ++ tailWord_117853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117861 : List Nat := [1, 3, 1, 3, 2, 1, 3, 4, 2]
def baseStart_117861 : Nat := 118140960795 + 117861 * 2 ^ 59
def prefixEnd_117861 : Nat := 4983230072969 + 3 ^ 40 * 117861 * 2
def baseEnd_117861 : Nat := 53794971928594312884865

theorem tailTrace_117861 : CollatzResearch.WordTrace tailWord_117861 prefixEnd_117861 53794971928594312884865 := by
  unfold tailWord_117861
  simp only [CollatzResearch.WordTrace]
  refine ⟨4298743826017200901353437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2865829217344800600902291 4298743826017200901353437)
  ·
    refine ⟨1612028934756450338007539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4298743826017200901353437 1612028934756450338007539)
    ·
      refine ⟨2418043402134675507011309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1612028934756450338007539 2418043402134675507011309)
      ·
        refine ⟨906766275800503315129241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2418043402134675507011309 906766275800503315129241)
        ·
          refine ⟨680074706850377486346931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 906766275800503315129241 680074706850377486346931)
          ·
            refine ⟨1020112060275566229520397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680074706850377486346931 1020112060275566229520397)
            ·
              refine ⟨382542022603337336070149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1020112060275566229520397 382542022603337336070149)
              ·
                refine ⟨71726629238125750513153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 382542022603337336070149 71726629238125750513153)
                ·
                  refine ⟨53794971928594312884865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71726629238125750513153 53794971928594312884865)
                  ·
                    rfl

theorem cell20_117861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_117861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117861 prefixEnd_117861 := by exact prefixLift 117861
  have htrace : WordTrace (prefixWord ++ tailWord_117861) baseStart_117861 baseEnd_117861 := by
    simpa [prefixWord, tailWord_117861, baseEnd_117861] using wordTrace_append hprefix tailTrace_117861
  have hstable : (prefixWord ++ tailWord_117861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117861).length < 2 ^ (prefixWord ++ tailWord_117861).sum := by decide
  have hdescent : baseEnd_117861 < baseStart_117861 := by decide
  rcases family_descends (prefixWord ++ tailWord_117861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117864 : List Nat := [2, 1, 4, 4, 2, 1, 1, 5]
def baseStart_117864 : Nat := 118140960795 + 117864 * 2 ^ 59
def prefixEnd_117864 : Nat := 4983230072969 + 3 ^ 40 * 117864 * 2
def baseEnd_117864 : Nat := 17932113736779878594951

theorem tailTrace_117864 : CollatzResearch.WordTrace tailWord_117864 prefixEnd_117864 17932113736779878594951 := by
  unfold tailWord_117864
  simp only [CollatzResearch.WordTrace]
  refine ⟨2149426622503166206856323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2865902163337554942475097 2149426622503166206856323)
  ·
    refine ⟨3224139933754749310284485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2149426622503166206856323 3224139933754749310284485)
    ·
      refine ⟨604526237579015495678341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3224139933754749310284485 604526237579015495678341)
      ·
        refine ⟨113348669546065405439689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 604526237579015495678341 113348669546065405439689)
        ·
          refine ⟨85011502159549054079767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113348669546065405439689 85011502159549054079767)
          ·
            refine ⟨127517253239323581119651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85011502159549054079767 127517253239323581119651)
            ·
              refine ⟨191275879858985371679477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127517253239323581119651 191275879858985371679477)
              ·
                refine ⟨17932113736779878594951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191275879858985371679477 17932113736779878594951)
                ·
                  rfl

theorem cell20_117864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 5].length) (baseStart_117864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117864 prefixEnd_117864 := by exact prefixLift 117864
  have htrace : WordTrace (prefixWord ++ tailWord_117864) baseStart_117864 baseEnd_117864 := by
    simpa [prefixWord, tailWord_117864, baseEnd_117864] using wordTrace_append hprefix tailTrace_117864
  have hstable : (prefixWord ++ tailWord_117864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117864).length < 2 ^ (prefixWord ++ tailWord_117864).sum := by decide
  have hdescent : baseEnd_117864 < baseStart_117864 := by decide
  rcases family_descends (prefixWord ++ tailWord_117864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117920 : List Nat := [2, 1, 1, 4, 2, 1, 4, 1, 4]
def baseStart_117920 : Nat := 118140960795 + 117920 * 2 ^ 59
def prefixEnd_117920 : Nat := 4983230072969 + 3 ^ 40 * 117920 * 2
def baseEnd_117920 : Nat := 53821901136252329917957

theorem tailTrace_117920 : CollatzResearch.WordTrace tailWord_117920 prefixEnd_117920 53821901136252329917957 := by
  unfold tailWord_117920
  simp only [CollatzResearch.WordTrace]
  refine ⟨2150447866401726988875607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2867263821868969318500809 2150447866401726988875607)
  ·
    refine ⟨3225671799602590483313411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2150447866401726988875607 3225671799602590483313411)
    ·
      refine ⟨4838507699403885724970117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3225671799602590483313411 4838507699403885724970117)
      ·
        refine ⟨907220193638228573431897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4838507699403885724970117 907220193638228573431897)
        ·
          refine ⟨680415145228671430073923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 907220193638228573431897 680415145228671430073923)
          ·
            refine ⟨1020622717843007145110885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680415145228671430073923 1020622717843007145110885)
            ·
              refine ⟨191366759595563839708291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1020622717843007145110885 191366759595563839708291)
              ·
                refine ⟨287050139393345759562437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191366759595563839708291 287050139393345759562437)
                ·
                  refine ⟨53821901136252329917957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 287050139393345759562437 53821901136252329917957)
                  ·
                    rfl

theorem cell20_117920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_117920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_117920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_117920 prefixEnd_117920 := by exact prefixLift 117920
  have htrace : WordTrace (prefixWord ++ tailWord_117920) baseStart_117920 baseEnd_117920 := by
    simpa [prefixWord, tailWord_117920, baseEnd_117920] using wordTrace_append hprefix tailTrace_117920
  have hstable : (prefixWord ++ tailWord_117920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117920).length < 2 ^ (prefixWord ++ tailWord_117920).sum := by decide
  have hdescent : baseEnd_117920 < baseStart_117920 := by decide
  rcases family_descends (prefixWord ++ tailWord_117920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118024 : List Nat := [2, 1, 3, 2, 12]
def baseStart_118024 : Nat := 118140960795 + 118024 * 2 ^ 59
def prefixEnd_118024 : Nat := 4983230072969 + 3 ^ 40 * 118024 * 2
def baseEnd_118024 : Nat := 665053945309755437665

theorem tailTrace_118024 : CollatzResearch.WordTrace tailWord_118024 prefixEnd_118024 665053945309755437665 := by
  unfold tailWord_118024
  simp only [CollatzResearch.WordTrace]
  refine ⟨2152344462213339869768563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2869792616284453159691417 2152344462213339869768563)
  ·
    refine ⟨3228516693320009804652845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2152344462213339869768563 3228516693320009804652845)
    ·
      refine ⟨1210693759995003676744817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3228516693320009804652845 1210693759995003676744817)
      ·
        refine ⟨908020319996252757558613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1210693759995003676744817 908020319996252757558613)
        ·
          refine ⟨665053945309755437665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 908020319996252757558613 665053945309755437665)
          ·
            rfl

theorem cell20_118024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 12].length) (baseStart_118024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118024 prefixEnd_118024 := by exact prefixLift 118024
  have htrace : WordTrace (prefixWord ++ tailWord_118024) baseStart_118024 baseEnd_118024 := by
    simpa [prefixWord, tailWord_118024, baseEnd_118024] using wordTrace_append hprefix tailTrace_118024
  have hstable : (prefixWord ++ tailWord_118024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118024).length < 2 ^ (prefixWord ++ tailWord_118024).sum := by decide
  have hdescent : baseEnd_118024 < baseStart_118024 := by decide
  rcases family_descends (prefixWord ++ tailWord_118024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118027 : List Nat := [1, 1, 1, 1, 5, 4, 2, 2, 3]
def baseStart_118027 : Nat := 118140960795 + 118027 * 2 ^ 59
def prefixEnd_118027 : Nat := 4983230072969 + 3 ^ 40 * 118027 * 2
def baseEnd_118027 : Nat := 53870738851835513350853

theorem tailTrace_118027 : CollatzResearch.WordTrace tailWord_118027 prefixEnd_118027 53870738851835513350853 := by
  unfold tailWord_118027
  simp only [CollatzResearch.WordTrace]
  refine ⟨4304798343415811251896335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2869865562277207501264223 4304798343415811251896335)
  ·
    refine ⟨6457197515123716877844503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4304798343415811251896335 6457197515123716877844503)
    ·
      refine ⟨9685796272685575316766755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6457197515123716877844503 9685796272685575316766755)
      ·
        refine ⟨14528694409028362975150133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9685796272685575316766755 14528694409028362975150133)
        ·
          refine ⟨1362065100846409028920325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14528694409028362975150133 1362065100846409028920325)
          ·
            refine ⟨255387206408701692922561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1362065100846409028920325 255387206408701692922561)
            ·
              refine ⟨191540404806526269691921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255387206408701692922561 191540404806526269691921)
              ·
                refine ⟨143655303604894702268941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191540404806526269691921 143655303604894702268941)
                ·
                  refine ⟨53870738851835513350853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143655303604894702268941 53870738851835513350853)
                  ·
                    rfl

theorem cell20_118027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 3].length) (baseStart_118027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118027 prefixEnd_118027 := by exact prefixLift 118027
  have htrace : WordTrace (prefixWord ++ tailWord_118027) baseStart_118027 baseEnd_118027 := by
    simpa [prefixWord, tailWord_118027, baseEnd_118027] using wordTrace_append hprefix tailTrace_118027
  have hstable : (prefixWord ++ tailWord_118027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118027).length < 2 ^ (prefixWord ++ tailWord_118027).sum := by decide
  have hdescent : baseEnd_118027 < baseStart_118027 := by decide
  rcases family_descends (prefixWord ++ tailWord_118027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118030 : List Nat := [4, 1, 1, 2, 1, 3, 4, 2, 2]
def baseStart_118030 : Nat := 118140960795 + 118030 * 2 ^ 59
def prefixEnd_118030 : Nat := 4983230072969 + 3 ^ 40 * 118030 * 2
def baseEnd_118030 : Nat := 53872108133580836250841

theorem tailTrace_118030 : CollatzResearch.WordTrace tailWord_118030 prefixEnd_118030 53872108133580836250841 := by
  unfold tailWord_118030
  simp only [CollatzResearch.WordTrace]
  refine ⟨538113470300617845531943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2869938508269961842837029 538113470300617845531943)
  ·
    refine ⟨807170205450926768297915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 538113470300617845531943 807170205450926768297915)
    ·
      refine ⟨1210755308176390152446873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 807170205450926768297915 1210755308176390152446873)
      ·
        refine ⟨908066481132292614335155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1210755308176390152446873 908066481132292614335155)
        ·
          refine ⟨1362099721698438921502733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908066481132292614335155 1362099721698438921502733)
          ·
            refine ⟨510787395636914595563525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1362099721698438921502733 510787395636914595563525)
            ·
              refine ⟨95772636681921486668161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 510787395636914595563525 95772636681921486668161)
              ·
                refine ⟨71829477511441115001121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95772636681921486668161 71829477511441115001121)
                ·
                  refine ⟨53872108133580836250841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71829477511441115001121 53872108133580836250841)
                  ·
                    rfl

theorem cell20_118030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_118030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118030 prefixEnd_118030 := by exact prefixLift 118030
  have htrace : WordTrace (prefixWord ++ tailWord_118030) baseStart_118030 baseEnd_118030 := by
    simpa [prefixWord, tailWord_118030, baseEnd_118030] using wordTrace_append hprefix tailTrace_118030
  have hstable : (prefixWord ++ tailWord_118030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118030).length < 2 ^ (prefixWord ++ tailWord_118030).sum := by decide
  have hdescent : baseEnd_118030 < baseStart_118030 := by decide
  rcases family_descends (prefixWord ++ tailWord_118030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118068 : List Nat := [2, 5, 1, 1, 1, 1, 4, 3, 2]
def baseStart_118068 : Nat := 118140960795 + 118068 * 2 ^ 59
def prefixEnd_118068 : Nat := 4983230072969 + 3 ^ 40 * 118068 * 2
def baseEnd_118068 : Nat := 53889452369021592984019

theorem tailTrace_118068 : CollatzResearch.WordTrace tailWord_118068 prefixEnd_118068 53889452369021592984019 := by
  unfold tailWord_118068
  simp only [CollatzResearch.WordTrace]
  refine ⟨2153146868133637627069429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2870862490844850169425905 2153146868133637627069429)
  ·
    refine ⟨201857518887528527537759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2153146868133637627069429 201857518887528527537759)
    ·
      refine ⟨302786278331292791306639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201857518887528527537759 302786278331292791306639)
      ·
        refine ⟨454179417496939186959959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302786278331292791306639 454179417496939186959959)
        ·
          refine ⟨681269126245408780439939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454179417496939186959959 681269126245408780439939)
          ·
            refine ⟨1021903689368113170659909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681269126245408780439939 1021903689368113170659909)
            ·
              refine ⟨191606941756521219498733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1021903689368113170659909 191606941756521219498733)
              ·
                refine ⟨71852603158695457312025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191606941756521219498733 71852603158695457312025)
                ·
                  refine ⟨53889452369021592984019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71852603158695457312025 53889452369021592984019)
                  ·
                    rfl

theorem cell20_118068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_118068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118068 prefixEnd_118068 := by exact prefixLift 118068
  have htrace : WordTrace (prefixWord ++ tailWord_118068) baseStart_118068 baseEnd_118068 := by
    simpa [prefixWord, tailWord_118068, baseEnd_118068] using wordTrace_append hprefix tailTrace_118068
  have hstable : (prefixWord ++ tailWord_118068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118068).length < 2 ^ (prefixWord ++ tailWord_118068).sum := by decide
  have hdescent : baseEnd_118068 < baseStart_118068 := by decide
  rcases family_descends (prefixWord ++ tailWord_118068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118109 : List Nat := [1, 4, 5, 1, 1, 2, 2, 4]
def baseStart_118109 : Nat := 118140960795 + 118109 * 2 ^ 59
def prefixEnd_118109 : Nat := 4983230072969 + 3 ^ 40 * 118109 * 2
def baseEnd_118109 : Nat := 17969388628735890872395

theorem tailTrace_118109 : CollatzResearch.WordTrace tailWord_118109 prefixEnd_118109 17969388628735890872395 := by
  unfold tailWord_118109
  simp only [CollatzResearch.WordTrace]
  refine ⟨4307789129118739256381381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2871859419412492837587587 4307789129118739256381381)
  ·
    refine ⟨807710461709763610571509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4307789129118739256381381 807710461709763610571509)
    ·
      refine ⟨75722855785290338491079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 807710461709763610571509 75722855785290338491079)
      ·
        refine ⟨113584283677935507736619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75722855785290338491079 113584283677935507736619)
        ·
          refine ⟨170376425516903261604929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113584283677935507736619 170376425516903261604929)
          ·
            refine ⟨127782319137677446203697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170376425516903261604929 127782319137677446203697)
            ·
              refine ⟨95836739353258084652773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127782319137677446203697 95836739353258084652773)
              ·
                refine ⟨17969388628735890872395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95836739353258084652773 17969388628735890872395)
                ·
                  rfl

theorem cell20_118109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 4].length) (baseStart_118109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118109 prefixEnd_118109 := by exact prefixLift 118109
  have htrace : WordTrace (prefixWord ++ tailWord_118109) baseStart_118109 baseEnd_118109 := by
    simpa [prefixWord, tailWord_118109, baseEnd_118109] using wordTrace_append hprefix tailTrace_118109
  have hstable : (prefixWord ++ tailWord_118109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118109).length < 2 ^ (prefixWord ++ tailWord_118109).sum := by decide
  have hdescent : baseEnd_118109 < baseStart_118109 := by decide
  rcases family_descends (prefixWord ++ tailWord_118109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118124 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 5]
def baseStart_118124 : Nat := 118140960795 + 118124 * 2 ^ 59
def prefixEnd_118124 : Nat := 4983230072969 + 3 ^ 40 * 118124 * 2
def baseEnd_118124 : Nat := 53915012294934287117123

theorem tailTrace_118124 : CollatzResearch.WordTrace tailWord_118124 prefixEnd_118124 53915012294934287117123 := by
  unfold tailWord_118124
  simp only [CollatzResearch.WordTrace]
  refine ⟨2154168112032198409088713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2872224149376264545451617 2154168112032198409088713)
  ·
    refine ⟨1615626084024148806816535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2154168112032198409088713 1615626084024148806816535)
    ·
      refine ⟨2423439126036223210224803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1615626084024148806816535 2423439126036223210224803)
      ·
        refine ⟨3635158689054334815337205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2423439126036223210224803 3635158689054334815337205)
        ·
          refine ⟨340796127098843888937863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3635158689054334815337205 340796127098843888937863)
          ·
            refine ⟨511194190648265833406795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340796127098843888937863 511194190648265833406795)
            ·
              refine ⟨766791285972398750110193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511194190648265833406795 766791285972398750110193)
              ·
                refine ⟨575093464479299062582645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 766791285972398750110193 575093464479299062582645)
                ·
                  refine ⟨53915012294934287117123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 575093464479299062582645 53915012294934287117123)
                  ·
                    rfl

theorem cell20_118124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_118124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118124 prefixEnd_118124 := by exact prefixLift 118124
  have htrace : WordTrace (prefixWord ++ tailWord_118124) baseStart_118124 baseEnd_118124 := by
    simpa [prefixWord, tailWord_118124, baseEnd_118124] using wordTrace_append hprefix tailTrace_118124
  have hstable : (prefixWord ++ tailWord_118124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118124).length < 2 ^ (prefixWord ++ tailWord_118124).sum := by decide
  have hdescent : baseEnd_118124 < baseStart_118124 := by decide
  rcases family_descends (prefixWord ++ tailWord_118124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118148 : List Nat := [2, 3, 2, 1, 1, 3, 3, 1, 4]
def baseStart_118148 : Nat := 118140960795 + 118148 * 2 ^ 59
def prefixEnd_118148 : Nat := 4983230072969 + 3 ^ 40 * 118148 * 2
def baseEnd_118148 : Nat := 53925966548896870317025

theorem tailTrace_118148 : CollatzResearch.WordTrace tailWord_118148 prefixEnd_118148 53925966548896870317025 := by
  unfold tailWord_118148
  simp only [CollatzResearch.WordTrace]
  refine ⟨2154605787988724458525549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2872807717318299278034065 2154605787988724458525549)
  ·
    refine ⟨807977170495771671947081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2154605787988724458525549 807977170495771671947081)
    ·
      refine ⟨605982877871828753960311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 807977170495771671947081 605982877871828753960311)
      ·
        refine ⟨908974316807743130940467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605982877871828753960311 908974316807743130940467)
        ·
          refine ⟨1363461475211614696410701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908974316807743130940467 1363461475211614696410701)
          ·
            refine ⟨511298053204355511154013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1363461475211614696410701 511298053204355511154013)
            ·
              refine ⟨191736769951633316682755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 511298053204355511154013 191736769951633316682755)
              ·
                refine ⟨287605154927449975024133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191736769951633316682755 287605154927449975024133)
                ·
                  refine ⟨53925966548896870317025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 287605154927449975024133 53925966548896870317025)
                  ·
                    rfl

theorem cell20_118148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_118148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118148 prefixEnd_118148 := by exact prefixLift 118148
  have htrace : WordTrace (prefixWord ++ tailWord_118148) baseStart_118148 baseEnd_118148 := by
    simpa [prefixWord, tailWord_118148, baseEnd_118148] using wordTrace_append hprefix tailTrace_118148
  have hstable : (prefixWord ++ tailWord_118148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118148).length < 2 ^ (prefixWord ++ tailWord_118148).sum := by decide
  have hdescent : baseEnd_118148 < baseStart_118148 := by decide
  rcases family_descends (prefixWord ++ tailWord_118148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118158 : List Nat := [4, 1, 1, 4, 2, 1, 1, 3, 3]
def baseStart_118158 : Nat := 118140960795 + 118158 * 2 ^ 59
def prefixEnd_118158 : Nat := 4983230072969 + 3 ^ 40 * 118158 * 2
def baseEnd_118158 : Nat := 53930530821381279983651

theorem tailTrace_118158 : CollatzResearch.WordTrace tailWord_118158 prefixEnd_118158 53930530821381279983651 := by
  unfold tailWord_118158
  simp only [CollatzResearch.WordTrace]
  refine ⟨538697038242652578114391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2873050870627480416610085 538697038242652578114391)
  ·
    refine ⟨808045557363978867171587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 538697038242652578114391 808045557363978867171587)
    ·
      refine ⟨1212068336045968300757381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 808045557363978867171587 1212068336045968300757381)
      ·
        refine ⟨227262813008619056392009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1212068336045968300757381 227262813008619056392009)
        ·
          refine ⟨170447109756464292294007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227262813008619056392009 170447109756464292294007)
          ·
            refine ⟨255670664634696438441011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170447109756464292294007 255670664634696438441011)
            ·
              refine ⟨383505996952044657661517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255670664634696438441011 383505996952044657661517)
              ·
                refine ⟨143814748857016746623069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383505996952044657661517 143814748857016746623069)
                ·
                  refine ⟨53930530821381279983651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143814748857016746623069 53930530821381279983651)
                  ·
                    rfl

theorem cell20_118158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_118158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118158 prefixEnd_118158 := by exact prefixLift 118158
  have htrace : WordTrace (prefixWord ++ tailWord_118158) baseStart_118158 baseEnd_118158 := by
    simpa [prefixWord, tailWord_118158, baseEnd_118158] using wordTrace_append hprefix tailTrace_118158
  have hstable : (prefixWord ++ tailWord_118158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118158).length < 2 ^ (prefixWord ++ tailWord_118158).sum := by decide
  have hdescent : baseEnd_118158 < baseStart_118158 := by decide
  rcases family_descends (prefixWord ++ tailWord_118158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118176 : List Nat := [2, 1, 1, 4, 1, 2, 1, 8]
def baseStart_118176 : Nat := 118140960795 + 118176 * 2 ^ 59
def prefixEnd_118176 : Nat := 4983230072969 + 3 ^ 40 * 118176 * 2
def baseEnd_118176 : Nat := 17979582170617739127859

theorem tailTrace_118176 : CollatzResearch.WordTrace tailWord_118176 prefixEnd_118176 17979582170617739127859 := by
  unfold tailWord_118176
  simp only [CollatzResearch.WordTrace]
  refine ⟨2155116409938004849535191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2873488546584006466046921 2155116409938004849535191)
  ·
    refine ⟨3232674614907007274302787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2155116409938004849535191 3232674614907007274302787)
    ·
      refine ⟨4849011922360510911454181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3232674614907007274302787 4849011922360510911454181)
      ·
        refine ⟨909189735442595795897659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4849011922360510911454181 909189735442595795897659)
        ·
          refine ⟨1363784603163893693846489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 909189735442595795897659 1363784603163893693846489)
          ·
            refine ⟨1022838452372920270384867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1363784603163893693846489 1022838452372920270384867)
            ·
              refine ⟨1534257678559380405577301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1022838452372920270384867 1534257678559380405577301)
              ·
                refine ⟨17979582170617739127859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1534257678559380405577301 17979582170617739127859)
                ·
                  rfl

theorem cell20_118176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_118176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118176 prefixEnd_118176 := by exact prefixLift 118176
  have htrace : WordTrace (prefixWord ++ tailWord_118176) baseStart_118176 baseEnd_118176 := by
    simpa [prefixWord, tailWord_118176, baseEnd_118176] using wordTrace_append hprefix tailTrace_118176
  have hstable : (prefixWord ++ tailWord_118176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118176).length < 2 ^ (prefixWord ++ tailWord_118176).sum := by decide
  have hdescent : baseEnd_118176 < baseStart_118176 := by decide
  rcases family_descends (prefixWord ++ tailWord_118176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118200 : List Nat := [2, 1, 2, 1, 2, 2, 3, 4, 3]
def baseStart_118200 : Nat := 118140960795 + 118200 * 2 ^ 59
def prefixEnd_118200 : Nat := 4983230072969 + 3 ^ 40 * 118200 * 2
def baseEnd_118200 : Nat := 53949700765815800583479

theorem tailTrace_118200 : CollatzResearch.WordTrace tailWord_118200 prefixEnd_118200 53949700765815800583479 := by
  unfold tailWord_118200
  simp only [CollatzResearch.WordTrace]
  refine ⟨2155554085894530898972027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2874072114526041198629369 2155554085894530898972027)
  ·
    refine ⟨3233331128841796348458041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2155554085894530898972027 3233331128841796348458041)
    ·
      refine ⟨2424998346631347261343531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3233331128841796348458041 2424998346631347261343531)
      ·
        refine ⟨3637497519947020892015297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2424998346631347261343531 3637497519947020892015297)
        ·
          refine ⟨2728123139960265669011473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3637497519947020892015297 2728123139960265669011473)
          ·
            refine ⟨2046092354970199251758605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2728123139960265669011473 2046092354970199251758605)
            ·
              refine ⟨767284633113824719409477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2046092354970199251758605 767284633113824719409477)
              ·
                refine ⟨143865868708842134889277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 767284633113824719409477 143865868708842134889277)
                ·
                  refine ⟨53949700765815800583479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143865868708842134889277 53949700765815800583479)
                  ·
                    rfl

theorem cell20_118200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 3].length) (baseStart_118200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118200 prefixEnd_118200 := by exact prefixLift 118200
  have htrace : WordTrace (prefixWord ++ tailWord_118200) baseStart_118200 baseEnd_118200 := by
    simpa [prefixWord, tailWord_118200, baseEnd_118200] using wordTrace_append hprefix tailTrace_118200
  have hstable : (prefixWord ++ tailWord_118200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118200).length < 2 ^ (prefixWord ++ tailWord_118200).sum := by decide
  have hdescent : baseEnd_118200 < baseStart_118200 := by decide
  rcases family_descends (prefixWord ++ tailWord_118200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118241 : List Nat := [1, 2, 3, 1, 2, 4, 2, 3, 2]
def baseStart_118241 : Nat := 118140960795 + 118241 * 2 ^ 59
def prefixEnd_118241 : Nat := 4983230072969 + 3 ^ 40 * 118241 * 2
def baseEnd_118241 : Nat := 53968414283001880216645

theorem tailTrace_118241 : CollatzResearch.WordTrace tailWord_118241 prefixEnd_118241 53968414283001880216645 := by
  unfold tailWord_118241
  simp only [CollatzResearch.WordTrace]
  refine ⟨4312603564640525800186577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2875069043093683866791051 4312603564640525800186577)
  ·
    refine ⟨3234452673480394350139933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4312603564640525800186577 3234452673480394350139933)
    ·
      refine ⟨1212919752555147881302475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3234452673480394350139933 1212919752555147881302475)
      ·
        refine ⟨1819379628832721821953713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1212919752555147881302475 1819379628832721821953713)
        ·
          refine ⟨1364534721624541366465285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1819379628832721821953713 1364534721624541366465285)
          ·
            refine ⟨255850260304601506212241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1364534721624541366465285 255850260304601506212241)
            ·
              refine ⟨191887695228451129659181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255850260304601506212241 191887695228451129659181)
              ·
                refine ⟨71957885710669173622193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191887695228451129659181 71957885710669173622193)
                ·
                  refine ⟨53968414283001880216645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71957885710669173622193 53968414283001880216645)
                  ·
                    rfl

theorem cell20_118241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 2].length) (baseStart_118241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118241 prefixEnd_118241 := by exact prefixLift 118241
  have htrace : WordTrace (prefixWord ++ tailWord_118241) baseStart_118241 baseEnd_118241 := by
    simpa [prefixWord, tailWord_118241, baseEnd_118241] using wordTrace_append hprefix tailTrace_118241
  have hstable : (prefixWord ++ tailWord_118241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118241).length < 2 ^ (prefixWord ++ tailWord_118241).sum := by decide
  have hdescent : baseEnd_118241 < baseStart_118241 := by decide
  rcases family_descends (prefixWord ++ tailWord_118241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118262 : List Nat := [5, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_118262 : Nat := 118140960795 + 118262 * 2 ^ 59
def prefixEnd_118262 : Nat := 4983230072969 + 3 ^ 40 * 118262 * 2
def baseEnd_118262 : Nat := 53977999255219140516559

theorem tailTrace_118262 : CollatzResearch.WordTrace tailWord_118262 prefixEnd_118262 53977999255219140516559 := by
  unfold tailWord_118262
  simp only [CollatzResearch.WordTrace]
  refine ⟨269585593597777899168815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2875579665042964257800693 269585593597777899168815)
  ·
    refine ⟨404378390396666848753223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269585593597777899168815 404378390396666848753223)
    ·
      refine ⟨606567585595000273129835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404378390396666848753223 606567585595000273129835)
      ·
        refine ⟨909851378392500409694753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606567585595000273129835 909851378392500409694753)
        ·
          refine ⟨682388533794375307271065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 909851378392500409694753 682388533794375307271065)
          ·
            refine ⟨511791400345781480453299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682388533794375307271065 511791400345781480453299)
            ·
              refine ⟨767687100518672220679949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511791400345781480453299 767687100518672220679949)
              ·
                refine ⟨287882662694502082754981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 767687100518672220679949 287882662694502082754981)
                ·
                  refine ⟨53977999255219140516559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 287882662694502082754981 53977999255219140516559)
                  ·
                    rfl

theorem cell20_118262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_118262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118262 prefixEnd_118262 := by exact prefixLift 118262
  have htrace : WordTrace (prefixWord ++ tailWord_118262) baseStart_118262 baseEnd_118262 := by
    simpa [prefixWord, tailWord_118262, baseEnd_118262] using wordTrace_append hprefix tailTrace_118262
  have hstable : (prefixWord ++ tailWord_118262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118262).length < 2 ^ (prefixWord ++ tailWord_118262).sum := by decide
  have hdescent : baseEnd_118262 < baseStart_118262 := by decide
  rcases family_descends (prefixWord ++ tailWord_118262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118278 : List Nat := [6, 2, 1, 1, 3, 1, 2, 4]
def baseStart_118278 : Nat := 118140960795 + 118278 * 2 ^ 59
def prefixEnd_118278 : Nat := 4983230072969 + 3 ^ 40 * 118278 * 2
def baseEnd_118278 : Nat := 17995100697064731994387

theorem tailTrace_118278 : CollatzResearch.WordTrace tailWord_118278 prefixEnd_118278 17995100697064731994387 := by
  unfold tailWord_118278
  simp only [CollatzResearch.WordTrace]
  refine ⟨134811033297077534977609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2875968710337654079522325 134811033297077534977609)
  ·
    refine ⟨101108274972808151233207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134811033297077534977609 101108274972808151233207)
    ·
      refine ⟨151662412459212226849811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101108274972808151233207 151662412459212226849811)
      ·
        refine ⟨227493618688818340274717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151662412459212226849811 227493618688818340274717)
        ·
          refine ⟨85310107008306877603019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227493618688818340274717 85310107008306877603019)
          ·
            refine ⟨127965160512460316404529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85310107008306877603019 127965160512460316404529)
            ·
              refine ⟨95973870384345237303397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127965160512460316404529 95973870384345237303397)
              ·
                refine ⟨17995100697064731994387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95973870384345237303397 17995100697064731994387)
                ·
                  rfl

theorem cell20_118278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_118278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118278 prefixEnd_118278 := by exact prefixLift 118278
  have htrace : WordTrace (prefixWord ++ tailWord_118278) baseStart_118278 baseEnd_118278 := by
    simpa [prefixWord, tailWord_118278, baseEnd_118278] using wordTrace_append hprefix tailTrace_118278
  have hstable : (prefixWord ++ tailWord_118278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118278).length < 2 ^ (prefixWord ++ tailWord_118278).sum := by decide
  have hdescent : baseEnd_118278 < baseStart_118278 := by decide
  rcases family_descends (prefixWord ++ tailWord_118278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118292 : List Nat := [2, 4, 3, 1, 3, 1, 1, 3, 2]
def baseStart_118292 : Nat := 118140960795 + 118292 * 2 ^ 59
def prefixEnd_118292 : Nat := 4983230072969 + 3 ^ 40 * 118292 * 2
def baseEnd_118292 : Nat := 53991692072672369516437

theorem tailTrace_118292 : CollatzResearch.WordTrace tailWord_118292 prefixEnd_118292 53991692072672369516437 := by
  unfold tailWord_118292
  simp only [CollatzResearch.WordTrace]
  refine ⟨2157231843727880755146565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2876309124970507673528753 2157231843727880755146565)
  ·
    refine ⟨404480970698977641589981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2157231843727880755146565 404480970698977641589981)
    ·
      refine ⟨151680364012116615596243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404480970698977641589981 151680364012116615596243)
      ·
        refine ⟨227520546018174923394365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151680364012116615596243 227520546018174923394365)
        ·
          refine ⟨85320204756815596272887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227520546018174923394365 85320204756815596272887)
          ·
            refine ⟨127980307135223394409331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85320204756815596272887 127980307135223394409331)
            ·
              refine ⟨191970460702835091613997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127980307135223394409331 191970460702835091613997)
              ·
                refine ⟨71988922763563159355249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191970460702835091613997 71988922763563159355249)
                ·
                  refine ⟨53991692072672369516437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71988922763563159355249 53991692072672369516437)
                  ·
                    rfl

theorem cell20_118292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_118292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118292 prefixEnd_118292 := by exact prefixLift 118292
  have htrace : WordTrace (prefixWord ++ tailWord_118292) baseStart_118292 baseEnd_118292 := by
    simpa [prefixWord, tailWord_118292, baseEnd_118292] using wordTrace_append hprefix tailTrace_118292
  have hstable : (prefixWord ++ tailWord_118292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118292).length < 2 ^ (prefixWord ++ tailWord_118292).sum := by decide
  have hdescent : baseEnd_118292 < baseStart_118292 := by decide
  rcases family_descends (prefixWord ++ tailWord_118292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118296 : List Nat := [2, 1, 2, 3, 4, 2, 1, 3, 2]
def baseStart_118296 : Nat := 118140960795 + 118296 * 2 ^ 59
def prefixEnd_118296 : Nat := 4983230072969 + 3 ^ 40 * 118296 * 2
def baseEnd_118296 : Nat := 53993517781666133383087

theorem tailTrace_118296 : CollatzResearch.WordTrace tailWord_118296 prefixEnd_118296 53993517781666133383087 := by
  unfold tailWord_118296
  simp only [CollatzResearch.WordTrace]
  refine ⟨2157304789720635096719371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2876406386294180128959161 2157304789720635096719371)
  ·
    refine ⟨3235957184580952645079057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2157304789720635096719371 3235957184580952645079057)
    ·
      refine ⟨2426967888435714483809293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3235957184580952645079057 2426967888435714483809293)
      ·
        refine ⟨910112958163392931428485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2426967888435714483809293 910112958163392931428485)
        ·
          refine ⟨170646179655636174642841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 910112958163392931428485 170646179655636174642841)
          ·
            refine ⟨127984634741727130982131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170646179655636174642841 127984634741727130982131)
            ·
              refine ⟨191976952112590696473197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127984634741727130982131 191976952112590696473197)
              ·
                refine ⟨71991357042221511177449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191976952112590696473197 71991357042221511177449)
                ·
                  refine ⟨53993517781666133383087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71991357042221511177449 53993517781666133383087)
                  ·
                    rfl

theorem cell20_118296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 2].length) (baseStart_118296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118296 prefixEnd_118296 := by exact prefixLift 118296
  have htrace : WordTrace (prefixWord ++ tailWord_118296) baseStart_118296 baseEnd_118296 := by
    simpa [prefixWord, tailWord_118296, baseEnd_118296] using wordTrace_append hprefix tailTrace_118296
  have hstable : (prefixWord ++ tailWord_118296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118296).length < 2 ^ (prefixWord ++ tailWord_118296).sum := by decide
  have hdescent : baseEnd_118296 < baseStart_118296 := by decide
  rcases family_descends (prefixWord ++ tailWord_118296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118307 : List Nat := [1, 1, 1, 4, 5, 2, 6]
def baseStart_118307 : Nat := 118140960795 + 118307 * 2 ^ 59
def prefixEnd_118307 : Nat := 4983230072969 + 3 ^ 40 * 118307 * 2
def baseEnd_118307 : Nat := 5999837609044331557375

theorem tailTrace_118307 : CollatzResearch.WordTrace tailWord_118307 prefixEnd_118307 5999837609044331557375 := by
  unfold tailWord_118307
  simp only [CollatzResearch.WordTrace]
  refine ⟨4315010782401419072089175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2876673854934279381392783 4315010782401419072089175)
  ·
    refine ⟨6472516173602128608133763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4315010782401419072089175 6472516173602128608133763)
    ·
      refine ⟨9708774260403192912200645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6472516173602128608133763 9708774260403192912200645)
      ·
        refine ⟨1820395173825598671037621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9708774260403192912200645 1820395173825598671037621)
        ·
          refine ⟨170662047546149875409777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1820395173825598671037621 170662047546149875409777)
          ·
            refine ⟨127996535659612406557333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170662047546149875409777 127996535659612406557333)
            ·
              refine ⟨5999837609044331557375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127996535659612406557333 5999837609044331557375)
              ·
                rfl

theorem cell20_118307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 6].length) (baseStart_118307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118307 prefixEnd_118307 := by exact prefixLift 118307
  have htrace : WordTrace (prefixWord ++ tailWord_118307) baseStart_118307 baseEnd_118307 := by
    simpa [prefixWord, tailWord_118307, baseEnd_118307] using wordTrace_append hprefix tailTrace_118307
  have hstable : (prefixWord ++ tailWord_118307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118307).length < 2 ^ (prefixWord ++ tailWord_118307).sum := by decide
  have hdescent : baseEnd_118307 < baseStart_118307 := by decide
  rcases family_descends (prefixWord ++ tailWord_118307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118314 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 5]
def baseStart_118314 : Nat := 118140960795 + 118314 * 2 ^ 59
def prefixEnd_118314 : Nat := 4983230072969 + 3 ^ 40 * 118314 * 2
def baseEnd_118314 : Nat := 54001733472138070783013

theorem tailTrace_118314 : CollatzResearch.WordTrace tailWord_118314 prefixEnd_118314 54001733472138070783013 := by
  unfold tailWord_118314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1078816523344014816898499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2876844062250706178395997 1078816523344014816898499)
  ·
    refine ⟨1618224785016022225347749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1078816523344014816898499 1618224785016022225347749)
    ·
      refine ⟨303417147190504167252703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1618224785016022225347749 303417147190504167252703)
      ·
        refine ⟨455125720785756250879055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303417147190504167252703 455125720785756250879055)
        ·
          refine ⟨682688581178634376318583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455125720785756250879055 682688581178634376318583)
          ·
            refine ⟨1024032871767951564477875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682688581178634376318583 1024032871767951564477875)
            ·
              refine ⟨1536049307651927346716813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024032871767951564477875 1536049307651927346716813)
              ·
                refine ⟨576018490369472755018805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1536049307651927346716813 576018490369472755018805)
                ·
                  refine ⟨54001733472138070783013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 576018490369472755018805 54001733472138070783013)
                  ·
                    rfl

theorem cell20_118314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_118314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118314 prefixEnd_118314 := by exact prefixLift 118314
  have htrace : WordTrace (prefixWord ++ tailWord_118314) baseStart_118314 baseEnd_118314 := by
    simpa [prefixWord, tailWord_118314, baseEnd_118314] using wordTrace_append hprefix tailTrace_118314
  have hstable : (prefixWord ++ tailWord_118314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118314).length < 2 ^ (prefixWord ++ tailWord_118314).sum := by decide
  have hdescent : baseEnd_118314 < baseStart_118314 := by decide
  rcases family_descends (prefixWord ++ tailWord_118314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118328 : List Nat := [2, 1, 2, 1, 4, 2, 1, 7]
def baseStart_118328 : Nat := 118140960795 + 118328 * 2 ^ 59
def prefixEnd_118328 : Nat := 4983230072969 + 3 ^ 40 * 118328 * 2
def baseEnd_118328 : Nat := 18002707817872081438763

theorem tailTrace_118328 : CollatzResearch.WordTrace tailWord_118328 prefixEnd_118328 18002707817872081438763 := by
  unfold tailWord_118328
  simp only [CollatzResearch.WordTrace]
  refine ⟨2157888357662669829301819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2877184476883559772402425 2157888357662669829301819)
  ·
    refine ⟨3236832536494004743952729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2157888357662669829301819 3236832536494004743952729)
    ·
      refine ⟨2427624402370503557964547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3236832536494004743952729 2427624402370503557964547)
      ·
        refine ⟨3641436603555755336946821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2427624402370503557964547 3641436603555755336946821)
        ·
          refine ⟨682769363166704125677529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3641436603555755336946821 682769363166704125677529)
          ·
            refine ⟨512077022375028094258147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682769363166704125677529 512077022375028094258147)
            ·
              refine ⟨768115533562542141387221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512077022375028094258147 768115533562542141387221)
              ·
                refine ⟨18002707817872081438763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 768115533562542141387221 18002707817872081438763)
                ·
                  rfl

theorem cell20_118328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_118328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118328 prefixEnd_118328 := by exact prefixLift 118328
  have htrace : WordTrace (prefixWord ++ tailWord_118328) baseStart_118328 baseEnd_118328 := by
    simpa [prefixWord, tailWord_118328, baseEnd_118328] using wordTrace_append hprefix tailTrace_118328
  have hstable : (prefixWord ++ tailWord_118328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118328).length < 2 ^ (prefixWord ++ tailWord_118328).sum := by decide
  have hdescent : baseEnd_118328 < baseStart_118328 := by decide
  rcases family_descends (prefixWord ++ tailWord_118328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118365 : List Nat := [1, 4, 4, 2, 1, 1, 2, 2, 3]
def baseStart_118365 : Nat := 118140960795 + 118365 * 2 ^ 59
def prefixEnd_118365 : Nat := 4983230072969 + 3 ^ 40 * 118365 * 2
def baseEnd_118365 : Nat := 54025011261808560082805

theorem tailTrace_118365 : CollatzResearch.WordTrace tailWord_118365 prefixEnd_118365 54025011261808560082805 := by
  unfold tailWord_118365
  simp only [CollatzResearch.WordTrace]
  refine ⟨4317126216191294977700549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2878084144127529985133699 4317126216191294977700549)
  ·
    refine ⟨809461165535867808318853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4317126216191294977700549 809461165535867808318853)
    ·
      refine ⟨151773968537975214059785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 809461165535867808318853 151773968537975214059785)
      ·
        refine ⟨113830476403481410544839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151773968537975214059785 113830476403481410544839)
        ·
          refine ⟨170745714605222115817259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113830476403481410544839 170745714605222115817259)
          ·
            refine ⟨256118571907833173725889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170745714605222115817259 256118571907833173725889)
            ·
              refine ⟨192088928930874880294417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256118571907833173725889 192088928930874880294417)
              ·
                refine ⟨144066696698156160220813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192088928930874880294417 144066696698156160220813)
                ·
                  refine ⟨54025011261808560082805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144066696698156160220813 54025011261808560082805)
                  ·
                    rfl

theorem cell20_118365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_118365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118365 prefixEnd_118365 := by exact prefixLift 118365
  have htrace : WordTrace (prefixWord ++ tailWord_118365) baseStart_118365 baseEnd_118365 := by
    simpa [prefixWord, tailWord_118365, baseEnd_118365] using wordTrace_append hprefix tailTrace_118365
  have hstable : (prefixWord ++ tailWord_118365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118365).length < 2 ^ (prefixWord ++ tailWord_118365).sum := by decide
  have hdescent : baseEnd_118365 < baseStart_118365 := by decide
  rcases family_descends (prefixWord ++ tailWord_118365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118372 : List Nat := [2, 3, 1, 1, 2, 5, 2, 2, 2]
def baseStart_118372 : Nat := 118140960795 + 118372 * 2 ^ 59
def prefixEnd_118372 : Nat := 4983230072969 + 3 ^ 40 * 118372 * 2
def baseEnd_118372 : Nat := 54028206252547646849443

theorem tailTrace_118372 : CollatzResearch.WordTrace tailWord_118372 prefixEnd_118372 54028206252547646849443 := by
  unfold tailWord_118372
  simp only [CollatzResearch.WordTrace]
  refine ⟨2158690763582967586602685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2878254351443956782136913 2158690763582967586602685)
  ·
    refine ⟨809509036343612844976007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2158690763582967586602685 809509036343612844976007)
    ·
      refine ⟨1214263554515419267464011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 809509036343612844976007 1214263554515419267464011)
      ·
        refine ⟨1821395331773128901196017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1214263554515419267464011 1821395331773128901196017)
        ·
          refine ⟨1366046498829846675897013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1821395331773128901196017 1366046498829846675897013)
          ·
            refine ⟨128066859265298125865345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1366046498829846675897013 128066859265298125865345)
            ·
              refine ⟨96050144448973594399009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128066859265298125865345 96050144448973594399009)
              ·
                refine ⟨72037608336730195799257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96050144448973594399009 72037608336730195799257)
                ·
                  refine ⟨54028206252547646849443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72037608336730195799257 54028206252547646849443)
                  ·
                    rfl

theorem cell20_118372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_118372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118372 prefixEnd_118372 := by exact prefixLift 118372
  have htrace : WordTrace (prefixWord ++ tailWord_118372) baseStart_118372 baseEnd_118372 := by
    simpa [prefixWord, tailWord_118372, baseEnd_118372] using wordTrace_append hprefix tailTrace_118372
  have hstable : (prefixWord ++ tailWord_118372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118372).length < 2 ^ (prefixWord ++ tailWord_118372).sum := by decide
  have hdescent : baseEnd_118372 < baseStart_118372 := by decide
  rcases family_descends (prefixWord ++ tailWord_118372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118397 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 6]
def baseStart_118397 : Nat := 118140960795 + 118397 * 2 ^ 59
def prefixEnd_118397 : Nat := 4983230072969 + 3 ^ 40 * 118397 * 2
def baseEnd_118397 : Nat := 54039616933758671016007

theorem tailTrace_118397 : CollatzResearch.WordTrace tailWord_118397 prefixEnd_118397 54039616933758671016007 := by
  unfold tailWord_118397
  simp only [CollatzResearch.WordTrace]
  refine ⟨4318293352075364442865445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2878862234716909628576963 4318293352075364442865445)
  ·
    refine ⟨809680003514130833037271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4318293352075364442865445 809680003514130833037271)
    ·
      refine ⟨1214520005271196249555907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 809680003514130833037271 1214520005271196249555907)
      ·
        refine ⟨1821780007906794374333861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1214520005271196249555907 1821780007906794374333861)
        ·
          refine ⟨341583751482523945187599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1821780007906794374333861 341583751482523945187599)
          ·
            refine ⟨512375627223785917781399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341583751482523945187599 512375627223785917781399)
            ·
              refine ⟨768563440835678876672099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512375627223785917781399 768563440835678876672099)
              ·
                refine ⟨1152845161253518315008149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 768563440835678876672099 1152845161253518315008149)
                ·
                  refine ⟨54039616933758671016007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1152845161253518315008149 54039616933758671016007)
                  ·
                    rfl

theorem cell20_118397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_118397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118397 prefixEnd_118397 := by exact prefixLift 118397
  have htrace : WordTrace (prefixWord ++ tailWord_118397) baseStart_118397 baseEnd_118397 := by
    simpa [prefixWord, tailWord_118397, baseEnd_118397] using wordTrace_append hprefix tailTrace_118397
  have hstable : (prefixWord ++ tailWord_118397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118397).length < 2 ^ (prefixWord ++ tailWord_118397).sum := by decide
  have hdescent : baseEnd_118397 < baseStart_118397 := by decide
  rcases family_descends (prefixWord ++ tailWord_118397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118411 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 5]
def baseStart_118411 : Nat := 118140960795 + 118411 * 2 ^ 59
def prefixEnd_118411 : Nat := 4983230072969 + 3 ^ 40 * 118411 * 2
def baseEnd_118411 : Nat := 54046006915236844549283

theorem tailTrace_118411 : CollatzResearch.WordTrace tailWord_118411 prefixEnd_118411 54046006915236844549283 := by
  unfold tailWord_118411
  simp only [CollatzResearch.WordTrace]
  refine ⟨4318803974024644833875087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2879202649349763222583391 4318803974024644833875087)
  ·
    refine ⟨6478205961036967250812631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4318803974024644833875087 6478205961036967250812631)
    ·
      refine ⟨9717308941555450876218947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6478205961036967250812631 9717308941555450876218947)
      ·
        refine ⟨14575963412333176314328421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9717308941555450876218947 14575963412333176314328421)
        ·
          refine ⟨2732993139812470558936579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14575963412333176314328421 2732993139812470558936579)
          ·
            refine ⟨4099489709718705838404869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2732993139812470558936579 4099489709718705838404869)
            ·
              refine ⟨768654320572257344700913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4099489709718705838404869 768654320572257344700913)
              ·
                refine ⟨576490740429193008525685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 768654320572257344700913 576490740429193008525685)
                ·
                  refine ⟨54046006915236844549283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 576490740429193008525685 54046006915236844549283)
                  ·
                    rfl

theorem cell20_118411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_118411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118411 prefixEnd_118411 := by exact prefixLift 118411
  have htrace : WordTrace (prefixWord ++ tailWord_118411) baseStart_118411 baseEnd_118411 := by
    simpa [prefixWord, tailWord_118411, baseEnd_118411] using wordTrace_append hprefix tailTrace_118411
  have hstable : (prefixWord ++ tailWord_118411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118411).length < 2 ^ (prefixWord ++ tailWord_118411).sum := by decide
  have hdescent : baseEnd_118411 < baseStart_118411 := by decide
  rcases family_descends (prefixWord ++ tailWord_118411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118431 : List Nat := [1, 1, 2, 7, 1, 1, 2, 1, 4]
def baseStart_118431 : Nat := 118140960795 + 118431 * 2 ^ 59
def prefixEnd_118431 : Nat := 4983230072969 + 3 ^ 40 * 118431 * 2
def baseEnd_118431 : Nat := 54055135460205663882535

theorem tailTrace_118431 : CollatzResearch.WordTrace tailWord_118431 prefixEnd_118431 54055135460205663882535 := by
  unfold tailWord_118431
  simp only [CollatzResearch.WordTrace]
  refine ⟨4319533433952188249603147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2879688955968125499735431 4319533433952188249603147)
  ·
    refine ⟨6479300150928282374404721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4319533433952188249603147 6479300150928282374404721)
    ·
      refine ⟨4859475113196211780803541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6479300150928282374404721 4859475113196211780803541)
      ·
        refine ⟨113893947965536213612583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 4859475113196211780803541 113893947965536213612583)
        ·
          refine ⟨170840921948304320418875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113893947965536213612583 170840921948304320418875)
          ·
            refine ⟨256261382922456480628313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170840921948304320418875 256261382922456480628313)
            ·
              refine ⟨192196037191842360471235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256261382922456480628313 192196037191842360471235)
              ·
                refine ⟨288294055787763540706853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192196037191842360471235 288294055787763540706853)
                ·
                  refine ⟨54055135460205663882535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 288294055787763540706853 54055135460205663882535)
                  ·
                    rfl

theorem cell20_118431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 4].length) (baseStart_118431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118431 prefixEnd_118431 := by exact prefixLift 118431
  have htrace : WordTrace (prefixWord ++ tailWord_118431) baseStart_118431 baseEnd_118431 := by
    simpa [prefixWord, tailWord_118431, baseEnd_118431] using wordTrace_append hprefix tailTrace_118431
  have hstable : (prefixWord ++ tailWord_118431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118431).length < 2 ^ (prefixWord ++ tailWord_118431).sum := by decide
  have hdescent : baseEnd_118431 < baseStart_118431 := by decide
  rcases family_descends (prefixWord ++ tailWord_118431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118435 : List Nat := [1, 1, 1, 4, 1, 1, 6, 1, 4]
def baseStart_118435 : Nat := 118140960795 + 118435 * 2 ^ 59
def prefixEnd_118435 : Nat := 4983230072969 + 3 ^ 40 * 118435 * 2
def baseEnd_118435 : Nat := 54056961169199427749185

theorem tailTrace_118435 : CollatzResearch.WordTrace tailWord_118435 prefixEnd_118435 54056961169199427749185 := by
  unfold tailWord_118435
  simp only [CollatzResearch.WordTrace]
  refine ⟨4319679325937696932748759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2879786217291797955165839 4319679325937696932748759)
  ·
    refine ⟨6479518988906545399123139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4319679325937696932748759 6479518988906545399123139)
    ·
      refine ⟨9719278483359818098684709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6479518988906545399123139 9719278483359818098684709)
      ·
        refine ⟨1822364715629965893503383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9719278483359818098684709 1822364715629965893503383)
        ·
          refine ⟨2733547073444948840255075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1822364715629965893503383 2733547073444948840255075)
          ·
            refine ⟨4100320610167423260382613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2733547073444948840255075 4100320610167423260382613)
            ·
              refine ⟨192202528601597965330435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4100320610167423260382613 192202528601597965330435)
              ·
                refine ⟨288303792902396947995653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192202528601597965330435 288303792902396947995653)
                ·
                  refine ⟨54056961169199427749185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 288303792902396947995653 54056961169199427749185)
                  ·
                    rfl

theorem cell20_118435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 4].length) (baseStart_118435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118435 prefixEnd_118435 := by exact prefixLift 118435
  have htrace : WordTrace (prefixWord ++ tailWord_118435) baseStart_118435 baseEnd_118435 := by
    simpa [prefixWord, tailWord_118435, baseEnd_118435] using wordTrace_append hprefix tailTrace_118435
  have hstable : (prefixWord ++ tailWord_118435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118435).length < 2 ^ (prefixWord ++ tailWord_118435).sum := by decide
  have hdescent : baseEnd_118435 < baseStart_118435 := by decide
  rcases family_descends (prefixWord ++ tailWord_118435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118476 : List Nat := [2, 2, 1, 5, 3, 1, 6]
def baseStart_118476 : Nat := 118140960795 + 118476 * 2 ^ 59
def prefixEnd_118476 : Nat := 4983230072969 + 3 ^ 40 * 118476 * 2
def baseEnd_118476 : Nat := 6008408298487278598039

theorem tailTrace_118476 : CollatzResearch.WordTrace tailWord_118476 prefixEnd_118476 6008408298487278598039 := by
  unfold tailWord_118476
  simp only [CollatzResearch.WordTrace]
  refine ⟨2160587359394580467495641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2880783145859440623327521 2160587359394580467495641)
  ·
    refine ⟨1620440519545935350621731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2160587359394580467495641 1620440519545935350621731)
    ·
      refine ⟨2430660779318903025932597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1620440519545935350621731 2430660779318903025932597)
      ·
        refine ⟨227874448061147158681181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2430660779318903025932597 227874448061147158681181)
        ·
          refine ⟨85452918022930184505443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227874448061147158681181 85452918022930184505443)
          ·
            refine ⟨128179377034395276758165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85452918022930184505443 128179377034395276758165)
            ·
              refine ⟨6008408298487278598039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128179377034395276758165 6008408298487278598039)
              ·
                rfl

theorem cell20_118476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 6].length) (baseStart_118476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118476 prefixEnd_118476 := by exact prefixLift 118476
  have htrace : WordTrace (prefixWord ++ tailWord_118476) baseStart_118476 baseEnd_118476 := by
    simpa [prefixWord, tailWord_118476, baseEnd_118476] using wordTrace_append hprefix tailTrace_118476
  have hstable : (prefixWord ++ tailWord_118476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118476).length < 2 ^ (prefixWord ++ tailWord_118476).sum := by decide
  have hdescent : baseEnd_118476 < baseStart_118476 := by decide
  rcases family_descends (prefixWord ++ tailWord_118476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118487 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 5]
def baseStart_118487 : Nat := 118140960795 + 118487 * 2 ^ 59
def prefixEnd_118487 : Nat := 4983230072969 + 3 ^ 40 * 118487 * 2
def baseEnd_118487 : Nat := 54080695386118358015639

theorem tailTrace_118487 : CollatzResearch.WordTrace tailWord_118487 prefixEnd_118487 54080695386118358015639 := by
  unfold tailWord_118487
  simp only [CollatzResearch.WordTrace]
  refine ⟨4321575921749309813641715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2881050614499539875761143 4321575921749309813641715)
  ·
    refine ⟨6482363882623964720462573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4321575921749309813641715 6482363882623964720462573)
    ·
      refine ⟨2430886455983986770173465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6482363882623964720462573 2430886455983986770173465)
      ·
        refine ⟨1823164841987990077630099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2430886455983986770173465 1823164841987990077630099)
        ·
          refine ⟨2734747262981985116445149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1823164841987990077630099 2734747262981985116445149)
          ·
            refine ⟨1025530223618244418666931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2734747262981985116445149 1025530223618244418666931)
            ·
              refine ⟨1538295335427366628000397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025530223618244418666931 1538295335427366628000397)
              ·
                refine ⟨576860750785262485500149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1538295335427366628000397 576860750785262485500149)
                ·
                  refine ⟨54080695386118358015639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 576860750785262485500149 54080695386118358015639)
                  ·
                    rfl

theorem cell20_118487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_118487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118487 prefixEnd_118487 := by exact prefixLift 118487
  have htrace : WordTrace (prefixWord ++ tailWord_118487) baseStart_118487 baseEnd_118487 := by
    simpa [prefixWord, tailWord_118487, baseEnd_118487] using wordTrace_append hprefix tailTrace_118487
  have hstable : (prefixWord ++ tailWord_118487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118487).length < 2 ^ (prefixWord ++ tailWord_118487).sum := by decide
  have hdescent : baseEnd_118487 < baseStart_118487 := by decide
  rcases family_descends (prefixWord ++ tailWord_118487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118490 : List Nat := [3, 1, 1, 2, 2, 5, 1, 1, 4]
def baseStart_118490 : Nat := 118140960795 + 118490 * 2 ^ 59
def prefixEnd_118490 : Nat := 4983230072969 + 3 ^ 40 * 118490 * 2
def baseEnd_118490 : Nat := 54082064667863680915627

theorem tailTrace_118490 : CollatzResearch.WordTrace tailWord_118490 prefixEnd_118490 54082064667863680915627 := by
  unfold tailWord_118490
  simp only [CollatzResearch.WordTrace]
  refine ⟨1080421335184610331500231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2881123560492294217333949 1080421335184610331500231)
  ·
    refine ⟨1620632002776915497250347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1080421335184610331500231 1620632002776915497250347)
    ·
      refine ⟨2430948004165373245875521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1620632002776915497250347 2430948004165373245875521)
      ·
        refine ⟨1823211003124029934406641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2430948004165373245875521 1823211003124029934406641)
        ·
          refine ⟨1367408252343022450804981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1823211003124029934406641 1367408252343022450804981)
          ·
            refine ⟨128194523657158354762967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1367408252343022450804981 128194523657158354762967)
            ·
              refine ⟨192291785485737532144451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128194523657158354762967 192291785485737532144451)
              ·
                refine ⟨288437678228606298216677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192291785485737532144451 288437678228606298216677)
                ·
                  refine ⟨54082064667863680915627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 288437678228606298216677 54082064667863680915627)
                  ·
                    rfl

theorem cell20_118490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_118490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118490 prefixEnd_118490 := by exact prefixLift 118490
  have htrace : WordTrace (prefixWord ++ tailWord_118490) baseStart_118490 baseEnd_118490 := by
    simpa [prefixWord, tailWord_118490, baseEnd_118490] using wordTrace_append hprefix tailTrace_118490
  have hstable : (prefixWord ++ tailWord_118490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118490).length < 2 ^ (prefixWord ++ tailWord_118490).sum := by decide
  have hdescent : baseEnd_118490 < baseStart_118490 := by decide
  rcases family_descends (prefixWord ++ tailWord_118490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118497 : List Nat := [1, 2, 3, 1, 5, 1, 2, 5]
def baseStart_118497 : Nat := 118140960795 + 118497 * 2 ^ 59
def prefixEnd_118497 : Nat := 4983230072969 + 3 ^ 40 * 118497 * 2
def baseEnd_118497 : Nat := 18028419886200922560755

theorem tailTrace_118497 : CollatzResearch.WordTrace tailWord_118497 prefixEnd_118497 18028419886200922560755 := by
  unfold tailWord_118497
  simp only [CollatzResearch.WordTrace]
  refine ⟨4321940651713081521505745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2881293767808721014337163 4321940651713081521505745)
  ·
    refine ⟨3241455488784811141129309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4321940651713081521505745 3241455488784811141129309)
    ·
      refine ⟨1215545808294304177923491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3241455488784811141129309 1215545808294304177923491)
      ·
        refine ⟨1823318712441456266885237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1215545808294304177923491 1823318712441456266885237)
        ·
          refine ⟨170936129291386525020491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1823318712441456266885237 170936129291386525020491)
          ·
            refine ⟨256404193937079787530737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170936129291386525020491 256404193937079787530737)
            ·
              refine ⟨192303145452809840648053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256404193937079787530737 192303145452809840648053)
              ·
                refine ⟨18028419886200922560755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192303145452809840648053 18028419886200922560755)
                ·
                  rfl

theorem cell20_118497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 5].length) (baseStart_118497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118497 prefixEnd_118497 := by exact prefixLift 118497
  have htrace : WordTrace (prefixWord ++ tailWord_118497) baseStart_118497 baseEnd_118497 := by
    simpa [prefixWord, tailWord_118497, baseEnd_118497] using wordTrace_append hprefix tailTrace_118497
  have hstable : (prefixWord ++ tailWord_118497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118497).length < 2 ^ (prefixWord ++ tailWord_118497).sum := by decide
  have hdescent : baseEnd_118497 < baseStart_118497 := by decide
  rcases family_descends (prefixWord ++ tailWord_118497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118525 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 5]
def baseStart_118525 : Nat := 118140960795 + 118525 * 2 ^ 59
def prefixEnd_118525 : Nat := 4983230072969 + 3 ^ 40 * 118525 * 2
def baseEnd_118525 : Nat := 54098039621559114748817

theorem tailTrace_118525 : CollatzResearch.WordTrace tailWord_118525 prefixEnd_118525 54098039621559114748817 := by
  unfold tailWord_118525
  simp only [CollatzResearch.WordTrace]
  refine ⟨4322961895611642303525029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2881974597074428202350019 4322961895611642303525029)
  ·
    refine ⟨810555355427182931910943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4322961895611642303525029 810555355427182931910943)
    ·
      refine ⟨1215833033140774397866415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 810555355427182931910943 1215833033140774397866415)
      ·
        refine ⟨1823749549711161596799623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1215833033140774397866415 1823749549711161596799623)
        ·
          refine ⟨2735624324566742395199435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1823749549711161596799623 2735624324566742395199435)
          ·
            refine ⟨4103436486850113592799153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2735624324566742395199435 4103436486850113592799153)
            ·
              refine ⟨3077577365137585194599365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4103436486850113592799153 3077577365137585194599365)
              ·
                refine ⟨577045755963297223987381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3077577365137585194599365 577045755963297223987381)
                ·
                  refine ⟨54098039621559114748817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 577045755963297223987381 54098039621559114748817)
                  ·
                    rfl

theorem cell20_118525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_118525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118525 prefixEnd_118525 := by exact prefixLift 118525
  have htrace : WordTrace (prefixWord ++ tailWord_118525) baseStart_118525 baseEnd_118525 := by
    simpa [prefixWord, tailWord_118525, baseEnd_118525] using wordTrace_append hprefix tailTrace_118525
  have hstable : (prefixWord ++ tailWord_118525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118525).length < 2 ^ (prefixWord ++ tailWord_118525).sum := by decide
  have hdescent : baseEnd_118525 < baseStart_118525 := by decide
  rcases family_descends (prefixWord ++ tailWord_118525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118535 : List Nat := [1, 1, 4, 4, 3, 7]
def baseStart_118535 : Nat := 118140960795 + 118535 * 2 ^ 59
def prefixEnd_118535 : Nat := 4983230072969 + 3 ^ 40 * 118535 * 2
def baseEnd_118535 : Nat := 2003800144223834237609

theorem tailTrace_118535 : CollatzResearch.WordTrace tailWord_118535 prefixEnd_118535 2003800144223834237609 := by
  unfold tailWord_118535
  simp only [CollatzResearch.WordTrace]
  refine ⟨4323326625575414011389059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2882217750383609340926039 4323326625575414011389059)
  ·
    refine ⟨6484989938363121017083589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4323326625575414011389059 6484989938363121017083589)
    ·
      refine ⟨1215935613443085190703173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6484989938363121017083589 1215935613443085190703173)
      ·
        refine ⟨227987927520578473256845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1215935613443085190703173 227987927520578473256845)
        ·
          refine ⟨85495472820216927471317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227987927520578473256845 85495472820216927471317)
          ·
            refine ⟨2003800144223834237609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 85495472820216927471317 2003800144223834237609)
            ·
              rfl

theorem cell20_118535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 7].length) (baseStart_118535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118535 prefixEnd_118535 := by exact prefixLift 118535
  have htrace : WordTrace (prefixWord ++ tailWord_118535) baseStart_118535 baseEnd_118535 := by
    simpa [prefixWord, tailWord_118535, baseEnd_118535] using wordTrace_append hprefix tailTrace_118535
  have hstable : (prefixWord ++ tailWord_118535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118535).length < 2 ^ (prefixWord ++ tailWord_118535).sum := by decide
  have hdescent : baseEnd_118535 < baseStart_118535 := by decide
  rcases family_descends (prefixWord ++ tailWord_118535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118542 : List Nat := [4, 1, 1, 2, 1, 1, 3, 4, 3]
def baseStart_118542 : Nat := 118140960795 + 118542 * 2 ^ 59
def prefixEnd_118542 : Nat := 4983230072969 + 3 ^ 40 * 118542 * 2
def baseEnd_118542 : Nat := 54105798884782611182081

theorem tailTrace_118542 : CollatzResearch.WordTrace tailWord_118542 prefixEnd_118542 54105798884782611182081 := by
  unfold tailWord_118542
  simp only [CollatzResearch.WordTrace]
  refine ⟨540447742068756775861735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2882387957700036137929253 540447742068756775861735)
  ·
    refine ⟨810671613103135163792603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 540447742068756775861735 810671613103135163792603)
    ·
      refine ⟨1216007419654702745688905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 810671613103135163792603 1216007419654702745688905)
      ·
        refine ⟨912005564741027059266679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1216007419654702745688905 912005564741027059266679)
        ·
          refine ⟨1368008347111540588900019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912005564741027059266679 1368008347111540588900019)
          ·
            refine ⟨2052012520667310883350029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368008347111540588900019 2052012520667310883350029)
            ·
              refine ⟨769504695250241581256261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2052012520667310883350029 769504695250241581256261)
              ·
                refine ⟨144282130359420296485549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 769504695250241581256261 144282130359420296485549)
                ·
                  refine ⟨54105798884782611182081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144282130359420296485549 54105798884782611182081)
                  ·
                    rfl

theorem cell20_118542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_118542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118542 prefixEnd_118542 := by exact prefixLift 118542
  have htrace : WordTrace (prefixWord ++ tailWord_118542) baseStart_118542 baseEnd_118542 := by
    simpa [prefixWord, tailWord_118542, baseEnd_118542] using wordTrace_append hprefix tailTrace_118542
  have hstable : (prefixWord ++ tailWord_118542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118542).length < 2 ^ (prefixWord ++ tailWord_118542).sum := by decide
  have hdescent : baseEnd_118542 < baseStart_118542 := by decide
  rcases family_descends (prefixWord ++ tailWord_118542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118548 : List Nat := [2, 4, 4, 1, 1, 2, 1, 5]
def baseStart_118548 : Nat := 118140960795 + 118548 * 2 ^ 59
def prefixEnd_118548 : Nat := 4983230072969 + 3 ^ 40 * 118548 * 2
def baseEnd_118548 : Nat := 18036179149424418994019

theorem tailTrace_118548 : CollatzResearch.WordTrace tailWord_118548 prefixEnd_118548 18036179149424418994019 := by
  unfold tailWord_118548
  simp only [CollatzResearch.WordTrace]
  refine ⟨2161900387264158615806149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2882533849685544821074865 2161900387264158615806149)
  ·
    refine ⟨405356322612029740463653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2161900387264158615806149 405356322612029740463653)
    ·
      refine ⟨76004310489755576336935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 405356322612029740463653 76004310489755576336935)
      ·
        refine ⟨114006465734633364505403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76004310489755576336935 114006465734633364505403)
        ·
          refine ⟨171009698601950046758105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114006465734633364505403 171009698601950046758105)
          ·
            refine ⟨128257273951462535068579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171009698601950046758105 128257273951462535068579)
            ·
              refine ⟨192385910927193802602869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128257273951462535068579 192385910927193802602869)
              ·
                refine ⟨18036179149424418994019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192385910927193802602869 18036179149424418994019)
                ·
                  rfl

theorem cell20_118548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 5].length) (baseStart_118548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118548 prefixEnd_118548 := by exact prefixLift 118548
  have htrace : WordTrace (prefixWord ++ tailWord_118548) baseStart_118548 baseEnd_118548 := by
    simpa [prefixWord, tailWord_118548, baseEnd_118548] using wordTrace_append hprefix tailTrace_118548
  have hstable : (prefixWord ++ tailWord_118548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118548).length < 2 ^ (prefixWord ++ tailWord_118548).sum := by decide
  have hdescent : baseEnd_118548 < baseStart_118548 := by decide
  rcases family_descends (prefixWord ++ tailWord_118548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118601 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 5]
def baseStart_118601 : Nat := 118140960795 + 118601 * 2 ^ 59
def prefixEnd_118601 : Nat := 4983230072969 + 3 ^ 40 * 118601 * 2
def baseEnd_118601 : Nat := 54132728092440628215173

theorem tailTrace_118601 : CollatzResearch.WordTrace tailWord_118601 prefixEnd_118601 54132728092440628215173 := by
  unfold tailWord_118601
  simp only [CollatzResearch.WordTrace]
  refine ⟨4325733843336307283291657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2883822562224204855527771 4325733843336307283291657)
  ·
    refine ⟨3244300382502230462468743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4325733843336307283291657 3244300382502230462468743)
    ·
      refine ⟨4866450573753345693703115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3244300382502230462468743 4866450573753345693703115)
      ·
        refine ⟨7299675860630018540554673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4866450573753345693703115 7299675860630018540554673)
        ·
          refine ⟨5474756895472513905416005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7299675860630018540554673 5474756895472513905416005)
          ·
            refine ⟨1026516917901096357265501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5474756895472513905416005 1026516917901096357265501)
            ·
              refine ⟨384943844212911133974563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1026516917901096357265501 384943844212911133974563)
              ·
                refine ⟨577415766319366700961845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384943844212911133974563 577415766319366700961845)
                ·
                  refine ⟨54132728092440628215173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 577415766319366700961845 54132728092440628215173)
                  ·
                    rfl

theorem cell20_118601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_118601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118601 prefixEnd_118601 := by exact prefixLift 118601
  have htrace : WordTrace (prefixWord ++ tailWord_118601) baseStart_118601 baseEnd_118601 := by
    simpa [prefixWord, tailWord_118601, baseEnd_118601] using wordTrace_append hprefix tailTrace_118601
  have hstable : (prefixWord ++ tailWord_118601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118601).length < 2 ^ (prefixWord ++ tailWord_118601).sum := by decide
  have hdescent : baseEnd_118601 < baseStart_118601 := by decide
  rcases family_descends (prefixWord ++ tailWord_118601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118604 : List Nat := [2, 2, 1, 3, 4, 1, 2, 1, 4]
def baseStart_118604 : Nat := 118140960795 + 118604 * 2 ^ 59
def prefixEnd_118604 : Nat := 4983230072969 + 3 ^ 40 * 118604 * 2
def baseEnd_118604 : Nat := 54134097374185951115161

theorem tailTrace_118604 : CollatzResearch.WordTrace tailWord_118604 prefixEnd_118604 54134097374185951115161 := by
  unfold tailWord_118604
  simp only [CollatzResearch.WordTrace]
  refine ⟨2162921631162719397825433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2883895508216959197100577 2162921631162719397825433)
  ·
    refine ⟨1622191223372039548369075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2162921631162719397825433 1622191223372039548369075)
    ·
      refine ⟨2433286835058059322553613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1622191223372039548369075 2433286835058059322553613)
      ·
        refine ⟨912482563146772245957605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2433286835058059322553613 912482563146772245957605)
        ·
          refine ⟨171090480590019796117051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 912482563146772245957605 171090480590019796117051)
          ·
            refine ⟨256635720885029694175577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171090480590019796117051 256635720885029694175577)
            ·
              refine ⟨192476790663772270631683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256635720885029694175577 192476790663772270631683)
              ·
                refine ⟨288715185995658405947525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192476790663772270631683 288715185995658405947525)
                ·
                  refine ⟨54134097374185951115161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 288715185995658405947525 54134097374185951115161)
                  ·
                    rfl

theorem cell20_118604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_118604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118604 prefixEnd_118604 := by exact prefixLift 118604
  have htrace : WordTrace (prefixWord ++ tailWord_118604) baseStart_118604 baseEnd_118604 := by
    simpa [prefixWord, tailWord_118604, baseEnd_118604] using wordTrace_append hprefix tailTrace_118604
  have hstable : (prefixWord ++ tailWord_118604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118604).length < 2 ^ (prefixWord ++ tailWord_118604).sum := by decide
  have hdescent : baseEnd_118604 < baseStart_118604 := by decide
  rcases family_descends (prefixWord ++ tailWord_118604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118628 : List Nat := [2, 3, 1, 1, 5, 2, 2, 4]
def baseStart_118628 : Nat := 118140960795 + 118628 * 2 ^ 59
def prefixEnd_118628 : Nat := 4983230072969 + 3 ^ 40 * 118628 * 2
def baseEnd_118628 : Nat := 18048350542716178105021

theorem tailTrace_118628 : CollatzResearch.WordTrace tailWord_118628 prefixEnd_118628 18048350542716178105021 := by
  unfold tailWord_118628
  simp only [CollatzResearch.WordTrace]
  refine ⟨2163359307119245447262269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2884479076158993929683025 2163359307119245447262269)
  ·
    refine ⟨811259740169717042723351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2163359307119245447262269 811259740169717042723351)
    ·
      refine ⟨1216889610254575564085027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 811259740169717042723351 1216889610254575564085027)
      ·
        refine ⟨1825334415381863346127541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1216889610254575564085027 1825334415381863346127541)
        ·
          refine ⟨171125101442049688699457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1825334415381863346127541 171125101442049688699457)
          ·
            refine ⟨128343826081537266524593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171125101442049688699457 128343826081537266524593)
            ·
              refine ⟨96257869561152949893445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128343826081537266524593 96257869561152949893445)
              ·
                refine ⟨18048350542716178105021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96257869561152949893445 18048350542716178105021)
                ·
                  rfl

theorem cell20_118628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 4].length) (baseStart_118628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118628 prefixEnd_118628 := by exact prefixLift 118628
  have htrace : WordTrace (prefixWord ++ tailWord_118628) baseStart_118628 baseEnd_118628 := by
    simpa [prefixWord, tailWord_118628, baseEnd_118628] using wordTrace_append hprefix tailTrace_118628
  have hstable : (prefixWord ++ tailWord_118628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118628).length < 2 ^ (prefixWord ++ tailWord_118628).sum := by decide
  have hdescent : baseEnd_118628 < baseStart_118628 := by decide
  rcases family_descends (prefixWord ++ tailWord_118628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118632 : List Nat := [2, 1, 4, 2, 1, 1, 3, 6]
def baseStart_118632 : Nat := 118140960795 + 118632 * 2 ^ 59
def prefixEnd_118632 : Nat := 4983230072969 + 3 ^ 40 * 118632 * 2
def baseEnd_118632 : Nat := 18048959112380766060571

theorem tailTrace_118632 : CollatzResearch.WordTrace tailWord_118632 prefixEnd_118632 18048959112380766060571 := by
  unfold tailWord_118632
  simp only [CollatzResearch.WordTrace]
  refine ⟨2163432253111999788835075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2884576337482666385113433 2163432253111999788835075)
  ·
    refine ⟨3245148379667999683252613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2163432253111999788835075 3245148379667999683252613)
    ·
      refine ⟨608465321187749940609865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3245148379667999683252613 608465321187749940609865)
      ·
        refine ⟨456348990890812455457399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608465321187749940609865 456348990890812455457399)
        ·
          refine ⟨684523486336218683186099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456348990890812455457399 684523486336218683186099)
          ·
            refine ⟨1026785229504328024779149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684523486336218683186099 1026785229504328024779149)
            ·
              refine ⟨385044461064123009292181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1026785229504328024779149 385044461064123009292181)
              ·
                refine ⟨18048959112380766060571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 385044461064123009292181 18048959112380766060571)
                ·
                  rfl

theorem cell20_118632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_118632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118632 prefixEnd_118632 := by exact prefixLift 118632
  have htrace : WordTrace (prefixWord ++ tailWord_118632) baseStart_118632 baseEnd_118632 := by
    simpa [prefixWord, tailWord_118632, baseEnd_118632] using wordTrace_append hprefix tailTrace_118632
  have hstable : (prefixWord ++ tailWord_118632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118632).length < 2 ^ (prefixWord ++ tailWord_118632).sum := by decide
  have hdescent : baseEnd_118632 < baseStart_118632 := by decide
  rcases family_descends (prefixWord ++ tailWord_118632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118638 : List Nat := [4, 1, 2, 3, 1, 3, 1, 3, 2]
def baseStart_118638 : Nat := 118140960795 + 118638 * 2 ^ 59
def prefixEnd_118638 : Nat := 4983230072969 + 3 ^ 40 * 118638 * 2
def baseEnd_118638 : Nat := 54149615900632943981689

theorem tailTrace_118638 : CollatzResearch.WordTrace tailWord_118638 prefixEnd_118638 54149615900632943981689 := by
  unfold tailWord_118638
  simp only [CollatzResearch.WordTrace]
  refine ⟨540885418025282825298571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2884722229468175068259045 540885418025282825298571)
  ·
    refine ⟨811328127037924237947857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 540885418025282825298571 811328127037924237947857)
    ·
      refine ⟨608496095278443178460893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 811328127037924237947857 608496095278443178460893)
      ·
        refine ⟨228186035729416191922835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 608496095278443178460893 228186035729416191922835)
        ·
          refine ⟨342279053594124287884253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228186035729416191922835 342279053594124287884253)
          ·
            refine ⟨128354645097796607956595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342279053594124287884253 128354645097796607956595)
            ·
              refine ⟨192531967646694911934893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128354645097796607956595 192531967646694911934893)
              ·
                refine ⟨72199487867510591975585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192531967646694911934893 72199487867510591975585)
                ·
                  refine ⟨54149615900632943981689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72199487867510591975585 54149615900632943981689)
                  ·
                    rfl

theorem cell20_118638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_118638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118638 prefixEnd_118638 := by exact prefixLift 118638
  have htrace : WordTrace (prefixWord ++ tailWord_118638) baseStart_118638 baseEnd_118638 := by
    simpa [prefixWord, tailWord_118638, baseEnd_118638] using wordTrace_append hprefix tailTrace_118638
  have hstable : (prefixWord ++ tailWord_118638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118638).length < 2 ^ (prefixWord ++ tailWord_118638).sum := by decide
  have hdescent : baseEnd_118638 < baseStart_118638 := by decide
  rcases family_descends (prefixWord ++ tailWord_118638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118659 : List Nat := [1, 1, 1, 3, 4, 3, 3, 2, 2]
def baseStart_118659 : Nat := 118140960795 + 118659 * 2 ^ 59
def prefixEnd_118659 : Nat := 4983230072969 + 3 ^ 40 * 118659 * 2
def baseEnd_118659 : Nat := 54159200872850204281603

theorem tailTrace_118659 : CollatzResearch.WordTrace tailWord_118659 prefixEnd_118659 54159200872850204281603 := by
  unfold tailWord_118659
  simp only [CollatzResearch.WordTrace]
  refine ⟨4327849277126183188903031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2885232851417455459268687 4327849277126183188903031)
  ·
    refine ⟨6491773915689274783354547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4327849277126183188903031 6491773915689274783354547)
    ·
      refine ⟨9737660873533912175031821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6491773915689274783354547 9737660873533912175031821)
      ·
        refine ⟨3651622827575217065636933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9737660873533912175031821 3651622827575217065636933)
        ·
          refine ⟨684679280170353199806925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3651622827575217065636933 684679280170353199806925)
          ·
            refine ⟨256754730063882449927597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 684679280170353199806925 256754730063882449927597)
            ·
              refine ⟨96283023773955918722849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256754730063882449927597 96283023773955918722849)
              ·
                refine ⟨72212267830466939042137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96283023773955918722849 72212267830466939042137)
                ·
                  refine ⟨54159200872850204281603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72212267830466939042137 54159200872850204281603)
                  ·
                    rfl

theorem cell20_118659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 2, 2].length) (baseStart_118659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118659 prefixEnd_118659 := by exact prefixLift 118659
  have htrace : WordTrace (prefixWord ++ tailWord_118659) baseStart_118659 baseEnd_118659 := by
    simpa [prefixWord, tailWord_118659, baseEnd_118659] using wordTrace_append hprefix tailTrace_118659
  have hstable : (prefixWord ++ tailWord_118659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118659).length < 2 ^ (prefixWord ++ tailWord_118659).sum := by decide
  have hdescent : baseEnd_118659 < baseStart_118659 := by decide
  rcases family_descends (prefixWord ++ tailWord_118659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118715 : List Nat := [1, 1, 1, 1, 1, 2, 2, 8, 3]
def baseStart_118715 : Nat := 118140960795 + 118715 * 2 ^ 59
def prefixEnd_118715 : Nat := 4983230072969 + 3 ^ 40 * 118715 * 2
def baseEnd_118715 : Nat := 54184760798762898414707

theorem tailTrace_118715 : CollatzResearch.WordTrace tailWord_118715 prefixEnd_118715 54184760798762898414707 := by
  unfold tailWord_118715
  simp only [CollatzResearch.WordTrace]
  refine ⟨4329891764923304752941599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2886594509948869835294399 4329891764923304752941599)
  ·
    refine ⟨6494837647384957129412399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4329891764923304752941599 6494837647384957129412399)
    ·
      refine ⟨9742256471077435694118599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6494837647384957129412399 9742256471077435694118599)
      ·
        refine ⟨14613384706616153541177899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9742256471077435694118599 14613384706616153541177899)
        ·
          refine ⟨21920077059924230311766849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14613384706616153541177899 21920077059924230311766849)
          ·
            refine ⟨16440057794943172733825137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21920077059924230311766849 16440057794943172733825137)
            ·
              refine ⟨12330043346207379550368853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16440057794943172733825137 12330043346207379550368853)
              ·
                refine ⟨144492695463367729105885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12330043346207379550368853 144492695463367729105885)
                ·
                  refine ⟨54184760798762898414707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144492695463367729105885 54184760798762898414707)
                  ·
                    rfl

theorem cell20_118715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 3].length) (baseStart_118715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118715 prefixEnd_118715 := by exact prefixLift 118715
  have htrace : WordTrace (prefixWord ++ tailWord_118715) baseStart_118715 baseEnd_118715 := by
    simpa [prefixWord, tailWord_118715, baseEnd_118715] using wordTrace_append hprefix tailTrace_118715
  have hstable : (prefixWord ++ tailWord_118715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118715).length < 2 ^ (prefixWord ++ tailWord_118715).sum := by decide
  have hdescent : baseEnd_118715 < baseStart_118715 := by decide
  rcases family_descends (prefixWord ++ tailWord_118715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118732 : List Nat := [2, 2, 1, 4, 1, 2, 2, 3, 3]
def baseStart_118732 : Nat := 118140960795 + 118732 * 2 ^ 59
def prefixEnd_118732 : Nat := 4983230072969 + 3 ^ 40 * 118732 * 2
def baseEnd_118732 : Nat := 54192520061986394847971

theorem tailTrace_118732 : CollatzResearch.WordTrace tailWord_118732 prefixEnd_118732 54192520061986394847971 := by
  unfold tailWord_118732
  simp only [CollatzResearch.WordTrace]
  refine ⟨2165255902930858328155225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2887007870574477770873633 2165255902930858328155225)
  ·
    refine ⟨1623941927198143746116419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2165255902930858328155225 1623941927198143746116419)
    ·
      refine ⟨2435912890797215619174629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1623941927198143746116419 2435912890797215619174629)
      ·
        refine ⟨456733667024477928595243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2435912890797215619174629 456733667024477928595243)
        ·
          refine ⟨685100500536716892892865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456733667024477928595243 685100500536716892892865)
          ·
            refine ⟨513825375402537669669649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 685100500536716892892865 513825375402537669669649)
            ·
              refine ⟨385369031551903252252237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513825375402537669669649 385369031551903252252237)
              ·
                refine ⟨144513386831963719594589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385369031551903252252237 144513386831963719594589)
                ·
                  refine ⟨54192520061986394847971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144513386831963719594589 54192520061986394847971)
                  ·
                    rfl

theorem cell20_118732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_118732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118732 prefixEnd_118732 := by exact prefixLift 118732
  have htrace : WordTrace (prefixWord ++ tailWord_118732) baseStart_118732 baseEnd_118732 := by
    simpa [prefixWord, tailWord_118732, baseEnd_118732] using wordTrace_append hprefix tailTrace_118732
  have hstable : (prefixWord ++ tailWord_118732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118732).length < 2 ^ (prefixWord ++ tailWord_118732).sum := by decide
  have hdescent : baseEnd_118732 < baseStart_118732 := by decide
  rcases family_descends (prefixWord ++ tailWord_118732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118756 : List Nat := [2, 3, 1, 1, 1, 1, 6, 3, 2]
def baseStart_118756 : Nat := 118140960795 + 118756 * 2 ^ 59
def prefixEnd_118756 : Nat := 4983230072969 + 3 ^ 40 * 118756 * 2
def baseEnd_118756 : Nat := 54203474315948978047873

theorem tailTrace_118756 : CollatzResearch.WordTrace tailWord_118756 prefixEnd_118756 54203474315948978047873 := by
  unfold tailWord_118756
  simp only [CollatzResearch.WordTrace]
  refine ⟨2165693578887384377592061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2887591438516512503456081 2165693578887384377592061)
  ·
    refine ⟨812135092082769141597023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2165693578887384377592061 812135092082769141597023)
    ·
      refine ⟨1218202638124153712395535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 812135092082769141597023 1218202638124153712395535)
      ·
        refine ⟨1827303957186230568593303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1218202638124153712395535 1827303957186230568593303)
        ·
          refine ⟨2740955935779345852889955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1827303957186230568593303 2740955935779345852889955)
          ·
            refine ⟨4111433903669018779334933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2740955935779345852889955 4111433903669018779334933)
            ·
              refine ⟨192723464234485255281325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4111433903669018779334933 192723464234485255281325)
              ·
                refine ⟨72271299087931970730497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192723464234485255281325 72271299087931970730497)
                ·
                  refine ⟨54203474315948978047873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72271299087931970730497 54203474315948978047873)
                  ·
                    rfl

theorem cell20_118756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_118756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118756 prefixEnd_118756 := by exact prefixLift 118756
  have htrace : WordTrace (prefixWord ++ tailWord_118756) baseStart_118756 baseEnd_118756 := by
    simpa [prefixWord, tailWord_118756, baseEnd_118756] using wordTrace_append hprefix tailTrace_118756
  have hstable : (prefixWord ++ tailWord_118756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118756).length < 2 ^ (prefixWord ++ tailWord_118756).sum := by decide
  have hdescent : baseEnd_118756 < baseStart_118756 := by decide
  rcases family_descends (prefixWord ++ tailWord_118756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118760 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 8]
def baseStart_118760 : Nat := 118140960795 + 118760 * 2 ^ 59
def prefixEnd_118760 : Nat := 4983230072969 + 3 ^ 40 * 118760 * 2
def baseEnd_118760 : Nat := 54205300024942741914523

theorem tailTrace_118760 : CollatzResearch.WordTrace tailWord_118760 prefixEnd_118760 54205300024942741914523 := by
  unfold tailWord_118760
  simp only [CollatzResearch.WordTrace]
  refine ⟨2165766524880138719164867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2887688699840184958886489 2165766524880138719164867)
  ·
    refine ⟨3248649787320208078747301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2165766524880138719164867 3248649787320208078747301)
    ·
      refine ⟨609121835122539014765119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3248649787320208078747301 609121835122539014765119)
      ·
        refine ⟨913682752683808522147679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609121835122539014765119 913682752683808522147679)
        ·
          refine ⟨1370524129025712783221519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913682752683808522147679 1370524129025712783221519)
          ·
            refine ⟨2055786193538569174832279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370524129025712783221519 2055786193538569174832279)
            ·
              refine ⟨3083679290307853762248419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2055786193538569174832279 3083679290307853762248419)
              ·
                refine ⟨4625518935461780643372629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3083679290307853762248419 4625518935461780643372629)
                ·
                  refine ⟨54205300024942741914523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4625518935461780643372629 54205300024942741914523)
                  ·
                    rfl

theorem cell20_118760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_118760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118760 prefixEnd_118760 := by exact prefixLift 118760
  have htrace : WordTrace (prefixWord ++ tailWord_118760) baseStart_118760 baseEnd_118760 := by
    simpa [prefixWord, tailWord_118760, baseEnd_118760] using wordTrace_append hprefix tailTrace_118760
  have hstable : (prefixWord ++ tailWord_118760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118760).length < 2 ^ (prefixWord ++ tailWord_118760).sum := by decide
  have hdescent : baseEnd_118760 < baseStart_118760 := by decide
  rcases family_descends (prefixWord ++ tailWord_118760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118767 : List Nat := [1, 1, 2, 1, 4, 2, 9]
def baseStart_118767 : Nat := 118140960795 + 118767 * 2 ^ 59
def prefixEnd_118767 : Nat := 4983230072969 + 3 ^ 40 * 118767 * 2
def baseEnd_118767 : Nat := 6023166112853536520129

theorem tailTrace_118767 : CollatzResearch.WordTrace tailWord_118767 prefixEnd_118767 6023166112853536520129 := by
  unfold tailWord_118767
  simp only [CollatzResearch.WordTrace]
  refine ⟨4331788360734917633834555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2887858907156611755889703 4331788360734917633834555)
  ·
    refine ⟨6497682541102376450751833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4331788360734917633834555 6497682541102376450751833)
    ·
      refine ⟨4873261905826782338063875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6497682541102376450751833 4873261905826782338063875)
      ·
        refine ⟨7309892858740173507095813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4873261905826782338063875 7309892858740173507095813)
        ·
          refine ⟨1370604911013782532580465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7309892858740173507095813 1370604911013782532580465)
          ·
            refine ⟨1027953683260336899435349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1370604911013782532580465 1027953683260336899435349)
            ·
              refine ⟨6023166112853536520129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1027953683260336899435349 6023166112853536520129)
              ·
                rfl

theorem cell20_118767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 9].length) (baseStart_118767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118767 prefixEnd_118767 := by exact prefixLift 118767
  have htrace : WordTrace (prefixWord ++ tailWord_118767) baseStart_118767 baseEnd_118767 := by
    simpa [prefixWord, tailWord_118767, baseEnd_118767] using wordTrace_append hprefix tailTrace_118767
  have hstable : (prefixWord ++ tailWord_118767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118767).length < 2 ^ (prefixWord ++ tailWord_118767).sum := by decide
  have hdescent : baseEnd_118767 < baseStart_118767 := by decide
  rcases family_descends (prefixWord ++ tailWord_118767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118777 : List Nat := [1, 2, 1, 3, 1, 5, 2, 1, 4]
def baseStart_118777 : Nat := 118140960795 + 118777 * 2 ^ 59
def prefixEnd_118777 : Nat := 4983230072969 + 3 ^ 40 * 118777 * 2
def baseEnd_118777 : Nat := 54213059288166238347787

theorem tailTrace_118777 : CollatzResearch.WordTrace tailWord_118777 prefixEnd_118777 54213059288166238347787 := by
  unfold tailWord_118777
  simp only [CollatzResearch.WordTrace]
  refine ⟨4332153090698689341698585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2888102060465792894465723 4332153090698689341698585)
  ·
    refine ⟨3249114818024017006273939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4332153090698689341698585 3249114818024017006273939)
    ·
      refine ⟨4873672227036025509410909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3249114818024017006273939 4873672227036025509410909)
      ·
        refine ⟨1827627085138509566029091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4873672227036025509410909 1827627085138509566029091)
        ·
          refine ⟨2741440627707764349043637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1827627085138509566029091 2741440627707764349043637)
          ·
            refine ⟨257010058847602907722841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2741440627707764349043637 257010058847602907722841)
            ·
              refine ⟨192757544135702180792131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257010058847602907722841 192757544135702180792131)
              ·
                refine ⟨289136316203553271188197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192757544135702180792131 289136316203553271188197)
                ·
                  refine ⟨54213059288166238347787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 289136316203553271188197 54213059288166238347787)
                  ·
                    rfl

theorem cell20_118777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_118777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118777 prefixEnd_118777 := by exact prefixLift 118777
  have htrace : WordTrace (prefixWord ++ tailWord_118777) baseStart_118777 baseEnd_118777 := by
    simpa [prefixWord, tailWord_118777, baseEnd_118777] using wordTrace_append hprefix tailTrace_118777
  have hstable : (prefixWord ++ tailWord_118777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118777).length < 2 ^ (prefixWord ++ tailWord_118777).sum := by decide
  have hdescent : baseEnd_118777 < baseStart_118777 := by decide
  rcases family_descends (prefixWord ++ tailWord_118777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118797 : List Nat := [1, 7, 1, 2, 1, 1, 1, 6]
def baseStart_118797 : Nat := 118140960795 + 118797 * 2 ^ 59
def prefixEnd_118797 : Nat := 4983230072969 + 3 ^ 40 * 118797 * 2
def baseEnd_118797 : Nat := 18074062611045019227013

theorem tailTrace_118797 : CollatzResearch.WordTrace tailWord_118797 prefixEnd_118797 18074062611045019227013 := by
  unfold tailWord_118797
  simp only [CollatzResearch.WordTrace]
  refine ⟨4332882550626232757426645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2888588367084155171617763 4332882550626232757426645)
  ·
    refine ⟨101551934780302330252187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 4332882550626232757426645 101551934780302330252187)
    ·
      refine ⟨152327902170453495378281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101551934780302330252187 152327902170453495378281)
      ·
        refine ⟨114245926627840121533711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152327902170453495378281 114245926627840121533711)
        ·
          refine ⟨171368889941760182300567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114245926627840121533711 171368889941760182300567)
          ·
            refine ⟨257053334912640273450851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171368889941760182300567 257053334912640273450851)
            ·
              refine ⟨385580002368960410176277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257053334912640273450851 385580002368960410176277)
              ·
                refine ⟨18074062611045019227013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 385580002368960410176277 18074062611045019227013)
                ·
                  rfl

theorem cell20_118797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 6].length) (baseStart_118797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118797 prefixEnd_118797 := by exact prefixLift 118797
  have htrace : WordTrace (prefixWord ++ tailWord_118797) baseStart_118797 baseEnd_118797 := by
    simpa [prefixWord, tailWord_118797, baseEnd_118797] using wordTrace_append hprefix tailTrace_118797
  have hstable : (prefixWord ++ tailWord_118797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118797).length < 2 ^ (prefixWord ++ tailWord_118797).sum := by decide
  have hdescent : baseEnd_118797 < baseStart_118797 := by decide
  rcases family_descends (prefixWord ++ tailWord_118797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118898 : List Nat := [3, 2, 1, 2, 2, 2, 3, 5]
def baseStart_118898 : Nat := 118140960795 + 118898 * 2 ^ 59
def prefixEnd_118898 : Nat := 4983230072969 + 3 ^ 40 * 118898 * 2
def baseEnd_118898 : Nat := 18089428995075865104653

theorem tailTrace_118898 : CollatzResearch.WordTrace tailWord_118898 prefixEnd_118898 18089428995075865104653 := by
  unfold tailWord_118898
  simp only [CollatzResearch.WordTrace]
  refine ⟨1084141580815081751713337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2891044215506884671235565 1084141580815081751713337)
  ·
    refine ⟨813106185611311313785003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1084141580815081751713337 813106185611311313785003)
    ·
      refine ⟨1219659278416966970677505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 813106185611311313785003 1219659278416966970677505)
      ·
        refine ⟨914744458812725228008129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1219659278416966970677505 914744458812725228008129)
        ·
          refine ⟨686058344109543921006097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 914744458812725228008129 686058344109543921006097)
          ·
            refine ⟨514543758082157940754573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 686058344109543921006097 514543758082157940754573)
            ·
              refine ⟨192953909280809227782965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 514543758082157940754573 192953909280809227782965)
              ·
                refine ⟨18089428995075865104653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192953909280809227782965 18089428995075865104653)
                ·
                  rfl

theorem cell20_118898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_118898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118898 prefixEnd_118898 := by exact prefixLift 118898
  have htrace : WordTrace (prefixWord ++ tailWord_118898) baseStart_118898 baseEnd_118898 := by
    simpa [prefixWord, tailWord_118898, baseEnd_118898] using wordTrace_append hprefix tailTrace_118898
  have hstable : (prefixWord ++ tailWord_118898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118898).length < 2 ^ (prefixWord ++ tailWord_118898).sum := by decide
  have hdescent : baseEnd_118898 < baseStart_118898 := by decide
  rcases family_descends (prefixWord ++ tailWord_118898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118919 : List Nat := [1, 1, 4, 2, 1, 1, 2, 8]
def baseStart_118919 : Nat := 118140960795 + 118919 * 2 ^ 59
def prefixEnd_118919 : Nat := 4983230072969 + 3 ^ 40 * 118919 * 2
def baseEnd_118919 : Nat := 18092623985814951871291

theorem tailTrace_118919 : CollatzResearch.WordTrace tailWord_118919 prefixEnd_118919 18092623985814951871291 := by
  unfold tailWord_118919
  simp only [CollatzResearch.WordTrace]
  refine ⟨4337332256184247593367811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2891554837456165062245207 4337332256184247593367811)
  ·
    refine ⟨6505998384276371390051717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4337332256184247593367811 6505998384276371390051717)
    ·
      refine ⟨1219874697051819635634697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6505998384276371390051717 1219874697051819635634697)
      ·
        refine ⟨914906022788864726726023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1219874697051819635634697 914906022788864726726023)
        ·
          refine ⟨1372359034183297090089035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914906022788864726726023 1372359034183297090089035)
          ·
            refine ⟨2058538551274945635133553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372359034183297090089035 2058538551274945635133553)
            ·
              refine ⟨1543903913456209226350165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2058538551274945635133553 1543903913456209226350165)
              ·
                refine ⟨18092623985814951871291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1543903913456209226350165 18092623985814951871291)
                ·
                  rfl

theorem cell20_118919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 8].length) (baseStart_118919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118919 prefixEnd_118919 := by exact prefixLift 118919
  have htrace : WordTrace (prefixWord ++ tailWord_118919) baseStart_118919 baseEnd_118919 := by
    simpa [prefixWord, tailWord_118919, baseEnd_118919] using wordTrace_append hprefix tailTrace_118919
  have hstable : (prefixWord ++ tailWord_118919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118919).length < 2 ^ (prefixWord ++ tailWord_118919).sum := by decide
  have hdescent : baseEnd_118919 < baseStart_118919 := by decide
  rcases family_descends (prefixWord ++ tailWord_118919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118936 : List Nat := [2, 1, 2, 4, 3, 1, 7]
def baseStart_118936 : Nat := 118140960795 + 118936 * 2 ^ 59
def prefixEnd_118936 : Nat := 4983230072969 + 3 ^ 40 * 118936 * 2
def baseEnd_118936 : Nat := 6031736802296483560793

theorem tailTrace_118936 : CollatzResearch.WordTrace tailWord_118936 prefixEnd_118936 6031736802296483560793 := by
  unfold tailWord_118936
  simp only [CollatzResearch.WordTrace]
  refine ⟨2168976148561329748368331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2891968198081772997824441 2168976148561329748368331)
  ·
    refine ⟨3253464222841994622552497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2168976148561329748368331 3253464222841994622552497)
    ·
      refine ⟨2440098167131495966914373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3253464222841994622552497 2440098167131495966914373)
      ·
        refine ⟨457518406337155493796445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2440098167131495966914373 457518406337155493796445)
        ·
          refine ⟨171569402376433310173667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 457518406337155493796445 171569402376433310173667)
          ·
            refine ⟨257354103564649965260501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171569402376433310173667 257354103564649965260501)
            ·
              refine ⟨6031736802296483560793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 257354103564649965260501 6031736802296483560793)
              ·
                rfl

theorem cell20_118936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 7].length) (baseStart_118936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118936 prefixEnd_118936 := by exact prefixLift 118936
  have htrace : WordTrace (prefixWord ++ tailWord_118936) baseStart_118936 baseEnd_118936 := by
    simpa [prefixWord, tailWord_118936, baseEnd_118936] using wordTrace_append hprefix tailTrace_118936
  have hstable : (prefixWord ++ tailWord_118936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118936).length < 2 ^ (prefixWord ++ tailWord_118936).sum := by decide
  have hdescent : baseEnd_118936 < baseStart_118936 := by decide
  rcases family_descends (prefixWord ++ tailWord_118936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118946 : List Nat := [3, 3, 1, 3, 1, 2, 2, 1, 4]
def baseStart_118946 : Nat := 118140960795 + 118946 * 2 ^ 59
def prefixEnd_118946 : Nat := 4983230072969 + 3 ^ 40 * 118946 * 2
def baseEnd_118946 : Nat := 54290195493152761713763

theorem tailTrace_118946 : CollatzResearch.WordTrace tailWord_118946 prefixEnd_118946 54290195493152761713763 := by
  unfold tailWord_118946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1084579256771607801150173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2892211351390954136400461 1084579256771607801150173)
  ·
    refine ⟨406717221289352925431315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1084579256771607801150173 406717221289352925431315)
    ·
      refine ⟨610075831934029388146973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406717221289352925431315 610075831934029388146973)
      ·
        refine ⟨228778436975261020555115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 610075831934029388146973 228778436975261020555115)
        ·
          refine ⟨343167655462891530832673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228778436975261020555115 343167655462891530832673)
          ·
            refine ⟨257375741597168648124505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343167655462891530832673 257375741597168648124505)
            ·
              refine ⟨193031806197876486093379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257375741597168648124505 193031806197876486093379)
              ·
                refine ⟨289547709296814729140069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193031806197876486093379 289547709296814729140069)
                ·
                  refine ⟨54290195493152761713763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 289547709296814729140069 54290195493152761713763)
                  ·
                    rfl

theorem cell20_118946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_118946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_118946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_118946 prefixEnd_118946 := by exact prefixLift 118946
  have htrace : WordTrace (prefixWord ++ tailWord_118946) baseStart_118946 baseEnd_118946 := by
    simpa [prefixWord, tailWord_118946, baseEnd_118946] using wordTrace_append hprefix tailTrace_118946
  have hstable : (prefixWord ++ tailWord_118946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118946).length < 2 ^ (prefixWord ++ tailWord_118946).sum := by decide
  have hdescent : baseEnd_118946 < baseStart_118946 := by decide
  rcases family_descends (prefixWord ++ tailWord_118946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119011 : List Nat := [1, 1, 1, 8, 2, 1, 2, 1, 3]
def baseStart_119011 : Nat := 118140960795 + 119011 * 2 ^ 59
def prefixEnd_119011 : Nat := 4983230072969 + 3 ^ 40 * 119011 * 2
def baseEnd_119011 : Nat := 54319863264301424546831

theorem tailTrace_119011 : CollatzResearch.WordTrace tailWord_119011 prefixEnd_119011 54319863264301424546831 := by
  unfold tailWord_119011
  simp only [CollatzResearch.WordTrace]
  refine ⟨4340687771850947305716887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2893791847900631537144591 4340687771850947305716887)
  ·
    refine ⟨6511031657776420958575331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4340687771850947305716887 6511031657776420958575331)
    ·
      refine ⟨9766547486664631437862997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6511031657776420958575331 9766547486664631437862997)
      ·
        refine ⟨114451728359351149662457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 9766547486664631437862997 114451728359351149662457)
        ·
          refine ⟨85838796269513362246843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114451728359351149662457 85838796269513362246843)
          ·
            refine ⟨128758194404270043370265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85838796269513362246843 128758194404270043370265)
            ·
              refine ⟨96568645803202532527699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128758194404270043370265 96568645803202532527699)
              ·
                refine ⟨144852968704803798791549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96568645803202532527699 144852968704803798791549)
                ·
                  refine ⟨54319863264301424546831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144852968704803798791549 54319863264301424546831)
                  ·
                    rfl

theorem cell20_119011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 3].length) (baseStart_119011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119011 prefixEnd_119011 := by exact prefixLift 119011
  have htrace : WordTrace (prefixWord ++ tailWord_119011) baseStart_119011 baseEnd_119011 := by
    simpa [prefixWord, tailWord_119011, baseEnd_119011] using wordTrace_append hprefix tailTrace_119011
  have hstable : (prefixWord ++ tailWord_119011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119011).length < 2 ^ (prefixWord ++ tailWord_119011).sum := by decide
  have hdescent : baseEnd_119011 < baseStart_119011 := by decide
  rcases family_descends (prefixWord ++ tailWord_119011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119015 : List Nat := [1, 1, 5, 3, 1, 1, 4, 1, 3]
def baseStart_119015 : Nat := 118140960795 + 119015 * 2 ^ 59
def prefixEnd_119015 : Nat := 4983230072969 + 3 ^ 40 * 119015 * 2
def baseEnd_119015 : Nat := 54321688973295188413481

theorem tailTrace_119015 : CollatzResearch.WordTrace tailWord_119015 prefixEnd_119015 54321688973295188413481 := by
  unfold tailWord_119015
  simp only [CollatzResearch.WordTrace]
  refine ⟨4340833663836455988862499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2893889109224303992574999 4340833663836455988862499)
  ·
    refine ⟨6511250495754683983293749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4340833663836455988862499 6511250495754683983293749)
    ·
      refine ⟨610429733977001623433789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6511250495754683983293749 610429733977001623433789)
      ·
        refine ⟨228911150241375608787671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 610429733977001623433789 228911150241375608787671)
        ·
          refine ⟨343366725362063413181507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228911150241375608787671 343366725362063413181507)
          ·
            refine ⟨515050088043095119772261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343366725362063413181507 515050088043095119772261)
            ·
              refine ⟨96571891508080334957299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 515050088043095119772261 96571891508080334957299)
              ·
                refine ⟨144857837262120502435949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96571891508080334957299 144857837262120502435949)
                ·
                  refine ⟨54321688973295188413481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144857837262120502435949 54321688973295188413481)
                  ·
                    rfl

theorem cell20_119015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 3].length) (baseStart_119015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119015 prefixEnd_119015 := by exact prefixLift 119015
  have htrace : WordTrace (prefixWord ++ tailWord_119015) baseStart_119015 baseEnd_119015 := by
    simpa [prefixWord, tailWord_119015, baseEnd_119015] using wordTrace_append hprefix tailTrace_119015
  have hstable : (prefixWord ++ tailWord_119015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119015).length < 2 ^ (prefixWord ++ tailWord_119015).sum := by decide
  have hdescent : baseEnd_119015 < baseStart_119015 := by decide
  rcases family_descends (prefixWord ++ tailWord_119015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119019 : List Nat := [1, 1, 1, 1, 2, 5, 3, 3, 3]
def baseStart_119019 : Nat := 118140960795 + 119019 * 2 ^ 59
def prefixEnd_119019 : Nat := 4983230072969 + 3 ^ 40 * 119019 * 2
def baseEnd_119019 : Nat := 54323514682288952280131

theorem tailTrace_119019 : CollatzResearch.WordTrace tailWord_119019 prefixEnd_119019 54323514682288952280131 := by
  unfold tailWord_119019
  simp only [CollatzResearch.WordTrace]
  refine ⟨4340979555821964672008111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2893986370547976448005407 4340979555821964672008111)
  ·
    refine ⟨6511469333732947008012167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4340979555821964672008111 6511469333732947008012167)
    ·
      refine ⟨9767204000599420512018251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6511469333732947008012167 9767204000599420512018251)
      ·
        refine ⟨14650806000899130768027377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9767204000599420512018251 14650806000899130768027377)
        ·
          refine ⟨10988104500674348076020533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14650806000899130768027377 10988104500674348076020533)
          ·
            refine ⟨1030134796938220132126925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10988104500674348076020533 1030134796938220132126925)
            ·
              refine ⟨386300548851832549547597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1030134796938220132126925 386300548851832549547597)
              ·
                refine ⟨144862705819437206080349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386300548851832549547597 144862705819437206080349)
                ·
                  refine ⟨54323514682288952280131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144862705819437206080349 54323514682288952280131)
                  ·
                    rfl

theorem cell20_119019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 3].length) (baseStart_119019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119019 prefixEnd_119019 := by exact prefixLift 119019
  have htrace : WordTrace (prefixWord ++ tailWord_119019) baseStart_119019 baseEnd_119019 := by
    simpa [prefixWord, tailWord_119019, baseEnd_119019] using wordTrace_append hprefix tailTrace_119019
  have hstable : (prefixWord ++ tailWord_119019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119019).length < 2 ^ (prefixWord ++ tailWord_119019).sum := by decide
  have hdescent : baseEnd_119019 < baseStart_119019 := by decide
  rcases family_descends (prefixWord ++ tailWord_119019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119040 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 7]
def baseStart_119040 : Nat := 118140960795 + 119040 * 2 ^ 59
def prefixEnd_119040 : Nat := 4983230072969 + 3 ^ 40 * 119040 * 2
def baseEnd_119040 : Nat := 54333099654506212580045

theorem tailTrace_119040 : CollatzResearch.WordTrace tailWord_119040 prefixEnd_119040 54333099654506212580045 := by
  unfold tailWord_119040
  simp only [CollatzResearch.WordTrace]
  refine ⟨2170872744372942629261287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2894496992497256839015049 2170872744372942629261287)
  ·
    refine ⟨3256309116559413943891931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2170872744372942629261287 3256309116559413943891931)
    ·
      refine ⟨4884463674839120915837897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3256309116559413943891931 4884463674839120915837897)
      ·
        refine ⟨3663347756129340686878423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4884463674839120915837897 3663347756129340686878423)
        ·
          refine ⟨5495021634194011030317635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3663347756129340686878423 5495021634194011030317635)
          ·
            refine ⟨8242532451291016545476453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5495021634194011030317635 8242532451291016545476453)
            ·
              refine ⟨1545474834617065602276835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8242532451291016545476453 1545474834617065602276835)
              ·
                refine ⟨2318212251925598403415253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1545474834617065602276835 2318212251925598403415253)
                ·
                  refine ⟨54333099654506212580045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2318212251925598403415253 54333099654506212580045)
                  ·
                    rfl

theorem cell20_119040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_119040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119040 prefixEnd_119040 := by exact prefixLift 119040
  have htrace : WordTrace (prefixWord ++ tailWord_119040) baseStart_119040 baseEnd_119040 := by
    simpa [prefixWord, tailWord_119040, baseEnd_119040] using wordTrace_append hprefix tailTrace_119040
  have hstable : (prefixWord ++ tailWord_119040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119040).length < 2 ^ (prefixWord ++ tailWord_119040).sum := by decide
  have hdescent : baseEnd_119040 < baseStart_119040 := by decide
  rcases family_descends (prefixWord ++ tailWord_119040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119043 : List Nat := [1, 1, 1, 3, 2, 3, 2, 5, 2]
def baseStart_119043 : Nat := 118140960795 + 119043 * 2 ^ 59
def prefixEnd_119043 : Nat := 4983230072969 + 3 ^ 40 * 119043 * 2
def baseEnd_119043 : Nat := 54334468936251535480033

theorem tailTrace_119043 : CollatzResearch.WordTrace tailWord_119043 prefixEnd_119043 54334468936251535480033 := by
  unfold tailWord_119043
  simp only [CollatzResearch.WordTrace]
  refine ⟨4341854907735016770881783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2894569938490011180587855 4341854907735016770881783)
  ·
    refine ⟨6512782361602525156322675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4341854907735016770881783 6512782361602525156322675)
    ·
      refine ⟨9769173542403787734484013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6512782361602525156322675 9769173542403787734484013)
      ·
        refine ⟨3663440078401420400431505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9769173542403787734484013 3663440078401420400431505)
        ·
          refine ⟨2747580058801065300323629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3663440078401420400431505 2747580058801065300323629)
          ·
            refine ⟨1030342522050399487621361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2747580058801065300323629 1030342522050399487621361)
            ·
              refine ⟨772756891537799615716021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1030342522050399487621361 772756891537799615716021)
              ·
                refine ⟨72445958581668713973377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 772756891537799615716021 72445958581668713973377)
                ·
                  refine ⟨54334468936251535480033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72445958581668713973377 54334468936251535480033)
                  ·
                    rfl

theorem cell20_119043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 2].length) (baseStart_119043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119043 prefixEnd_119043 := by exact prefixLift 119043
  have htrace : WordTrace (prefixWord ++ tailWord_119043) baseStart_119043 baseEnd_119043 := by
    simpa [prefixWord, tailWord_119043, baseEnd_119043] using wordTrace_append hprefix tailTrace_119043
  have hstable : (prefixWord ++ tailWord_119043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119043).length < 2 ^ (prefixWord ++ tailWord_119043).sum := by decide
  have hdescent : baseEnd_119043 < baseStart_119043 := by decide
  rcases family_descends (prefixWord ++ tailWord_119043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119057 : List Nat := [1, 2, 2, 1, 1, 5, 1, 4, 3]
def baseStart_119057 : Nat := 118140960795 + 119057 * 2 ^ 59
def prefixEnd_119057 : Nat := 4983230072969 + 3 ^ 40 * 119057 * 2
def baseEnd_119057 : Nat := 54340858917729709013309

theorem tailTrace_119057 : CollatzResearch.WordTrace tailWord_119057 prefixEnd_119057 54340858917729709013309 := by
  unfold tailWord_119057
  simp only [CollatzResearch.WordTrace]
  refine ⟨4342365529684297161891425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2894910353122864774594283 4342365529684297161891425)
  ·
    refine ⟨3256774147263222871418569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4342365529684297161891425 3256774147263222871418569)
    ·
      refine ⟨2442580610447417153563927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3256774147263222871418569 2442580610447417153563927)
      ·
        refine ⟨3663870915671125730345891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442580610447417153563927 3663870915671125730345891)
        ·
          refine ⟨5495806373506688595518837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3663870915671125730345891 5495806373506688595518837)
          ·
            refine ⟨515231847516252055829891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5495806373506688595518837 515231847516252055829891)
            ·
              refine ⟨772847771274378083744837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515231847516252055829891 772847771274378083744837)
              ·
                refine ⟨144908957113945890702157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 772847771274378083744837 144908957113945890702157)
                ·
                  refine ⟨54340858917729709013309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144908957113945890702157 54340858917729709013309)
                  ·
                    rfl

theorem cell20_119057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_119057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119057 prefixEnd_119057 := by exact prefixLift 119057
  have htrace : WordTrace (prefixWord ++ tailWord_119057) baseStart_119057 baseEnd_119057 := by
    simpa [prefixWord, tailWord_119057, baseEnd_119057] using wordTrace_append hprefix tailTrace_119057
  have hstable : (prefixWord ++ tailWord_119057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119057).length < 2 ^ (prefixWord ++ tailWord_119057).sum := by decide
  have hdescent : baseEnd_119057 < baseStart_119057 := by decide
  rcases family_descends (prefixWord ++ tailWord_119057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119064 : List Nat := [2, 1, 2, 3, 1, 2, 2, 3, 4]
def baseStart_119064 : Nat := 118140960795 + 119064 * 2 ^ 59
def prefixEnd_119064 : Nat := 4983230072969 + 3 ^ 40 * 119064 * 2
def baseEnd_119064 : Nat := 54344053908468795779947

theorem tailTrace_119064 : CollatzResearch.WordTrace tailWord_119064 prefixEnd_119064 54344053908468795779947 := by
  unfold tailWord_119064
  simp only [CollatzResearch.WordTrace]
  refine ⟨2171310420329468678698123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2895080560439291571597497 2171310420329468678698123)
  ·
    refine ⟨3256965630494203018047185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2171310420329468678698123 3256965630494203018047185)
    ·
      refine ⟨2442724222870652263535389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3256965630494203018047185 2442724222870652263535389)
      ·
        refine ⟨916021583576494598825771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2442724222870652263535389 916021583576494598825771)
        ·
          refine ⟨1374032375364741898238657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916021583576494598825771 1374032375364741898238657)
          ·
            refine ⟨1030524281523556423678993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1374032375364741898238657 1030524281523556423678993)
            ·
              refine ⟨772893211142667317759245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1030524281523556423678993 772893211142667317759245)
              ·
                refine ⟨289834954178500244159717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 772893211142667317759245 289834954178500244159717)
                ·
                  refine ⟨54344053908468795779947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 289834954178500244159717 54344053908468795779947)
                  ·
                    rfl

theorem cell20_119064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_119064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119064 prefixEnd_119064 := by exact prefixLift 119064
  have htrace : WordTrace (prefixWord ++ tailWord_119064) baseStart_119064 baseEnd_119064 := by
    simpa [prefixWord, tailWord_119064, baseEnd_119064] using wordTrace_append hprefix tailTrace_119064
  have hstable : (prefixWord ++ tailWord_119064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119064).length < 2 ^ (prefixWord ++ tailWord_119064).sum := by decide
  have hdescent : baseEnd_119064 < baseStart_119064 := by decide
  rcases family_descends (prefixWord ++ tailWord_119064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119074 : List Nat := [3, 3, 1, 1, 3, 1, 2, 3, 3]
def baseStart_119074 : Nat := 118140960795 + 119074 * 2 ^ 59
def prefixEnd_119074 : Nat := 4983230072969 + 3 ^ 40 * 119074 * 2
def baseEnd_119074 : Nat := 54348618180953205446573

theorem tailTrace_119074 : CollatzResearch.WordTrace tailWord_119074 prefixEnd_119074 54348618180953205446573 := by
  unfold tailWord_119074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1085746392655677266315069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2895323713748472710173517 1085746392655677266315069)
  ·
    refine ⟨407154897245878974868151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1085746392655677266315069 407154897245878974868151)
    ·
      refine ⟨610732345868818462302227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407154897245878974868151 610732345868818462302227)
      ·
        refine ⟨916098518803227693453341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610732345868818462302227 916098518803227693453341)
        ·
          refine ⟨343536944551210385045003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 916098518803227693453341 343536944551210385045003)
          ·
            refine ⟨515305416826815577567505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343536944551210385045003 515305416826815577567505)
            ·
              refine ⟨386479062620111683175629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515305416826815577567505 386479062620111683175629)
              ·
                refine ⟨144929648482541881190861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386479062620111683175629 144929648482541881190861)
                ·
                  refine ⟨54348618180953205446573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144929648482541881190861 54348618180953205446573)
                  ·
                    rfl

theorem cell20_119074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_119074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119074 prefixEnd_119074 := by exact prefixLift 119074
  have htrace : WordTrace (prefixWord ++ tailWord_119074) baseStart_119074 baseEnd_119074 := by
    simpa [prefixWord, tailWord_119074, baseEnd_119074] using wordTrace_append hprefix tailTrace_119074
  have hstable : (prefixWord ++ tailWord_119074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119074).length < 2 ^ (prefixWord ++ tailWord_119074).sum := by decide
  have hdescent : baseEnd_119074 < baseStart_119074 := by decide
  rcases family_descends (prefixWord ++ tailWord_119074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119098 : List Nat := [3, 1, 1, 1, 4, 3, 2, 3, 2]
def baseStart_119098 : Nat := 118140960795 + 119098 * 2 ^ 59
def prefixEnd_119098 : Nat := 4983230072969 + 3 ^ 40 * 119098 * 2
def baseEnd_119098 : Nat := 54359572434915788646475

theorem tailTrace_119098 : CollatzResearch.WordTrace tailWord_119098 prefixEnd_119098 54359572434915788646475 := by
  unfold tailWord_119098
  simp only [CollatzResearch.WordTrace]
  refine ⟨1085965230633940291033487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2895907281690507442755965 1085965230633940291033487)
  ·
    refine ⟨1628947845950910436550231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1085965230633940291033487 1628947845950910436550231)
    ·
      refine ⟨2443421768926365654825347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1628947845950910436550231 2443421768926365654825347)
      ·
        refine ⟨3665132653389548482238021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2443421768926365654825347 3665132653389548482238021)
        ·
          refine ⟨687212372510540340419629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3665132653389548482238021 687212372510540340419629)
          ·
            refine ⟨257704639691452627657361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 687212372510540340419629 257704639691452627657361)
            ·
              refine ⟨193278479768589470743021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257704639691452627657361 193278479768589470743021)
              ·
                refine ⟨72479429913221051528633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193278479768589470743021 72479429913221051528633)
                ·
                  refine ⟨54359572434915788646475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72479429913221051528633 54359572434915788646475)
                  ·
                    rfl

theorem cell20_119098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_119098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119098 prefixEnd_119098 := by exact prefixLift 119098
  have htrace : WordTrace (prefixWord ++ tailWord_119098) baseStart_119098 baseEnd_119098 := by
    simpa [prefixWord, tailWord_119098, baseEnd_119098] using wordTrace_append hprefix tailTrace_119098
  have hstable : (prefixWord ++ tailWord_119098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119098).length < 2 ^ (prefixWord ++ tailWord_119098).sum := by decide
  have hdescent : baseEnd_119098 < baseStart_119098 := by decide
  rcases family_descends (prefixWord ++ tailWord_119098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119108 : List Nat := [2, 3, 4, 1, 2, 2, 1, 2, 3]
def baseStart_119108 : Nat := 118140960795 + 119108 * 2 ^ 59
def prefixEnd_119108 : Nat := 4983230072969 + 3 ^ 40 * 119108 * 2
def baseEnd_119108 : Nat := 54364136707400198313101

theorem tailTrace_119108 : CollatzResearch.WordTrace tailWord_119108 prefixEnd_119108 54364136707400198313101 := by
  unfold tailWord_119108
  simp only [CollatzResearch.WordTrace]
  refine ⟨2172112826249766435998989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2896150434999688581331985 2172112826249766435998989)
  ·
    refine ⟨814542309843662413499621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2172112826249766435998989 814542309843662413499621)
    ·
      refine ⟨152726683095686702531179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 814542309843662413499621 152726683095686702531179)
      ·
        refine ⟨229090024643530053796769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152726683095686702531179 229090024643530053796769)
        ·
          refine ⟨171817518482647540347577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229090024643530053796769 171817518482647540347577)
          ·
            refine ⟨128863138861985655260683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171817518482647540347577 128863138861985655260683)
            ·
              refine ⟨193294708292978482891025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128863138861985655260683 193294708292978482891025)
              ·
                refine ⟨144971031219733862168269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193294708292978482891025 144971031219733862168269)
                ·
                  refine ⟨54364136707400198313101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144971031219733862168269 54364136707400198313101)
                  ·
                    rfl

theorem cell20_119108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_119108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119108 prefixEnd_119108 := by exact prefixLift 119108
  have htrace : WordTrace (prefixWord ++ tailWord_119108) baseStart_119108 baseEnd_119108 := by
    simpa [prefixWord, tailWord_119108, baseEnd_119108] using wordTrace_append hprefix tailTrace_119108
  have hstable : (prefixWord ++ tailWord_119108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119108).length < 2 ^ (prefixWord ++ tailWord_119108).sum := by decide
  have hdescent : baseEnd_119108 < baseStart_119108 := by decide
  rcases family_descends (prefixWord ++ tailWord_119108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119140 : List Nat := [2, 3, 1, 1, 3, 1, 1, 4, 4]
def baseStart_119140 : Nat := 118140960795 + 119140 * 2 ^ 59
def prefixEnd_119140 : Nat := 4983230072969 + 3 ^ 40 * 119140 * 2
def baseEnd_119140 : Nat := 54378742379350309246303

theorem tailTrace_119140 : CollatzResearch.WordTrace tailWord_119140 prefixEnd_119140 54378742379350309246303 := by
  unfold tailWord_119140
  simp only [CollatzResearch.WordTrace]
  refine ⟨2172696394191801168581437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2896928525589068224775249 2172696394191801168581437)
  ·
    refine ⟨814761147821925438218039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2172696394191801168581437 814761147821925438218039)
    ·
      refine ⟨1222141721732888157327059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 814761147821925438218039 1222141721732888157327059)
      ·
        refine ⟨1833212582599332235990589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1222141721732888157327059 1833212582599332235990589)
        ·
          refine ⟨687454718474749588496471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1833212582599332235990589 687454718474749588496471)
          ·
            refine ⟨1031182077712124382744707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687454718474749588496471 1031182077712124382744707)
            ·
              refine ⟨1546773116568186574117061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1031182077712124382744707 1546773116568186574117061)
              ·
                refine ⟨290019959356534982646949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1546773116568186574117061 290019959356534982646949)
                ·
                  refine ⟨54378742379350309246303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 290019959356534982646949 54378742379350309246303)
                  ·
                    rfl

theorem cell20_119140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_119140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119140 prefixEnd_119140 := by exact prefixLift 119140
  have htrace : WordTrace (prefixWord ++ tailWord_119140) baseStart_119140 baseEnd_119140 := by
    simpa [prefixWord, tailWord_119140, baseEnd_119140] using wordTrace_append hprefix tailTrace_119140
  have hstable : (prefixWord ++ tailWord_119140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119140).length < 2 ^ (prefixWord ++ tailWord_119140).sum := by decide
  have hdescent : baseEnd_119140 < baseStart_119140 := by decide
  rcases family_descends (prefixWord ++ tailWord_119140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119143 : List Nat := [1, 1, 5, 1, 3, 3, 2, 4]
def baseStart_119143 : Nat := 118140960795 + 119143 * 2 ^ 59
def prefixEnd_119143 : Nat := 4983230072969 + 3 ^ 40 * 119143 * 2
def baseEnd_119143 : Nat := 18126703887031877382097

theorem tailTrace_119143 : CollatzResearch.WordTrace tailWord_119143 prefixEnd_119143 18126703887031877382097 := by
  unfold tailWord_119143
  simp only [CollatzResearch.WordTrace]
  refine ⟨4345502207372733849522083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2897001471581822566348055 4345502207372733849522083)
  ·
    refine ⟨6518253311059100774283125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4345502207372733849522083 6518253311059100774283125)
    ·
      refine ⟨611086247911790697589043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6518253311059100774283125 611086247911790697589043)
      ·
        refine ⟨916629371867686046383565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611086247911790697589043 916629371867686046383565)
        ·
          refine ⟨343736014450382267393837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 916629371867686046383565 343736014450382267393837)
          ·
            refine ⟨128901005418893350272689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343736014450382267393837 128901005418893350272689)
            ·
              refine ⟨96675754064170012704517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128901005418893350272689 96675754064170012704517)
              ·
                refine ⟨18126703887031877382097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96675754064170012704517 18126703887031877382097)
                ·
                  rfl

theorem cell20_119143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 4].length) (baseStart_119143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119143 prefixEnd_119143 := by exact prefixLift 119143
  have htrace : WordTrace (prefixWord ++ tailWord_119143) baseStart_119143 baseEnd_119143 := by
    simpa [prefixWord, tailWord_119143, baseEnd_119143] using wordTrace_append hprefix tailTrace_119143
  have hstable : (prefixWord ++ tailWord_119143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119143).length < 2 ^ (prefixWord ++ tailWord_119143).sum := by decide
  have hdescent : baseEnd_119143 < baseStart_119143 := by decide
  rcases family_descends (prefixWord ++ tailWord_119143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119170 : List Nat := [3, 4, 2, 1, 3, 1, 1, 1, 4]
def baseStart_119170 : Nat := 118140960795 + 119170 * 2 ^ 59
def prefixEnd_119170 : Nat := 4983230072969 + 3 ^ 40 * 119170 * 2
def baseEnd_119170 : Nat := 54392435196803538246181

theorem tailTrace_119170 : CollatzResearch.WordTrace tailWord_119170 prefixEnd_119170 54392435196803538246181 := by
  unfold tailWord_119170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1086621744568729365188741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2897657985516611640503309 1086621744568729365188741)
  ·
    refine ⟨203741577106636755972889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1086621744568729365188741 203741577106636755972889)
    ·
      refine ⟨152806182829977566979667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203741577106636755972889 152806182829977566979667)
      ·
        refine ⟨229209274244966350469501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152806182829977566979667 229209274244966350469501)
        ·
          refine ⟨85953477841862381426063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229209274244966350469501 85953477841862381426063)
          ·
            refine ⟨128930216762793572139095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85953477841862381426063 128930216762793572139095)
            ·
              refine ⟨193395325144190358208643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128930216762793572139095 193395325144190358208643)
              ·
                refine ⟨290092987716285537312965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193395325144190358208643 290092987716285537312965)
                ·
                  refine ⟨54392435196803538246181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 290092987716285537312965 54392435196803538246181)
                  ·
                    rfl

theorem cell20_119170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_119170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119170 prefixEnd_119170 := by exact prefixLift 119170
  have htrace : WordTrace (prefixWord ++ tailWord_119170) baseStart_119170 baseEnd_119170 := by
    simpa [prefixWord, tailWord_119170, baseEnd_119170] using wordTrace_append hprefix tailTrace_119170
  have hstable : (prefixWord ++ tailWord_119170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119170).length < 2 ^ (prefixWord ++ tailWord_119170).sum := by decide
  have hdescent : baseEnd_119170 < baseStart_119170 := by decide
  rcases family_descends (prefixWord ++ tailWord_119170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119229 : List Nat := [1, 4, 1, 2, 2, 4, 2, 2, 2]
def baseStart_119229 : Nat := 118140960795 + 119229 * 2 ^ 59
def prefixEnd_119229 : Nat := 4983230072969 + 3 ^ 40 * 119229 * 2
def baseEnd_119229 : Nat := 54419364404461555279273

theorem tailTrace_119229 : CollatzResearch.WordTrace tailWord_119229 prefixEnd_119229 54419364404461555279273 := by
  unfold tailWord_119229
  simp only [CollatzResearch.WordTrace]
  refine ⟨4348638885061170537152741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2899092590040780358101827 4348638885061170537152741)
  ·
    refine ⟨815369790948969475716139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4348638885061170537152741 815369790948969475716139)
    ·
      refine ⟨1223054686423454213574209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 815369790948969475716139 1223054686423454213574209)
      ·
        refine ⟨917291014817590660180657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1223054686423454213574209 917291014817590660180657)
        ·
          refine ⟨687968261113192995135493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 917291014817590660180657 687968261113192995135493)
          ·
            refine ⟨128994048958723686587905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 687968261113192995135493 128994048958723686587905)
            ·
              refine ⟨96745536719042764940929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128994048958723686587905 96745536719042764940929)
              ·
                refine ⟨72559152539282073705697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96745536719042764940929 72559152539282073705697)
                ·
                  refine ⟨54419364404461555279273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72559152539282073705697 54419364404461555279273)
                  ·
                    rfl

theorem cell20_119229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_119229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119229 prefixEnd_119229 := by exact prefixLift 119229
  have htrace : WordTrace (prefixWord ++ tailWord_119229) baseStart_119229 baseEnd_119229 := by
    simpa [prefixWord, tailWord_119229, baseEnd_119229] using wordTrace_append hprefix tailTrace_119229
  have hstable : (prefixWord ++ tailWord_119229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119229).length < 2 ^ (prefixWord ++ tailWord_119229).sum := by decide
  have hdescent : baseEnd_119229 < baseStart_119229 := by decide
  rcases family_descends (prefixWord ++ tailWord_119229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119236 : List Nat := [2, 3, 3, 2, 3, 1, 1, 5]
def baseStart_119236 : Nat := 118140960795 + 119236 * 2 ^ 59
def prefixEnd_119236 : Nat := 4983230072969 + 3 ^ 40 * 119236 * 2
def baseEnd_119236 : Nat := 18140853131733547348637

theorem tailTrace_119236 : CollatzResearch.WordTrace tailWord_119236 prefixEnd_119236 18140853131733547348637 := by
  unfold tailWord_119236
  simp only [CollatzResearch.WordTrace]
  refine ⟨2174447098017905366328781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2899262797357207155105041 2174447098017905366328781)
  ·
    refine ⟨815417661756714512373293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2174447098017905366328781 815417661756714512373293)
    ·
      refine ⟨305781623158767942139985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 815417661756714512373293 305781623158767942139985)
      ·
        refine ⟨229336217369075956604989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305781623158767942139985 229336217369075956604989)
        ·
          refine ⟨86001081513403483726871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229336217369075956604989 86001081513403483726871)
          ·
            refine ⟨129001622270105225590307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86001081513403483726871 129001622270105225590307)
            ·
              refine ⟨193502433405157838385461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129001622270105225590307 193502433405157838385461)
              ·
                refine ⟨18140853131733547348637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193502433405157838385461 18140853131733547348637)
                ·
                  rfl

theorem cell20_119236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 5].length) (baseStart_119236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119236 prefixEnd_119236 := by exact prefixLift 119236
  have htrace : WordTrace (prefixWord ++ tailWord_119236) baseStart_119236 baseEnd_119236 := by
    simpa [prefixWord, tailWord_119236, baseEnd_119236] using wordTrace_append hprefix tailTrace_119236
  have hstable : (prefixWord ++ tailWord_119236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119236).length < 2 ^ (prefixWord ++ tailWord_119236).sum := by decide
  have hdescent : baseEnd_119236 < baseStart_119236 := by decide
  rcases family_descends (prefixWord ++ tailWord_119236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119237 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 10]
def baseStart_119237 : Nat := 118140960795 + 119237 * 2 ^ 59
def prefixEnd_119237 : Nat := 4983230072969 + 3 ^ 40 * 119237 * 2
def baseEnd_119237 : Nat := 54423015822449083012573

theorem tailTrace_119237 : CollatzResearch.WordTrace tailWord_119237 prefixEnd_119237 54423015822449083012573 := by
  unfold tailWord_119237
  simp only [CollatzResearch.WordTrace]
  refine ⟨4348930669032187903443965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2899287112688125268962643 4348930669032187903443965)
  ·
    refine ⟨1630849000887070463791487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4348930669032187903443965 1630849000887070463791487)
    ·
      refine ⟨2446273501330605695687231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1630849000887070463791487 2446273501330605695687231)
      ·
        refine ⟨3669410251995908543530847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2446273501330605695687231 3669410251995908543530847)
        ·
          refine ⟨5504115377993862815296271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3669410251995908543530847 5504115377993862815296271)
          ·
            refine ⟨8256173066990794222944407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5504115377993862815296271 8256173066990794222944407)
            ·
              refine ⟨12384259600486191334416611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8256173066990794222944407 12384259600486191334416611)
              ·
                refine ⟨18576389400729287001624917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12384259600486191334416611 18576389400729287001624917)
                ·
                  refine ⟨54423015822449083012573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 18576389400729287001624917 54423015822449083012573)
                  ·
                    rfl

theorem cell20_119237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_119237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119237 prefixEnd_119237 := by exact prefixLift 119237
  have htrace : WordTrace (prefixWord ++ tailWord_119237) baseStart_119237 baseEnd_119237 := by
    simpa [prefixWord, tailWord_119237, baseEnd_119237] using wordTrace_append hprefix tailTrace_119237
  have hstable : (prefixWord ++ tailWord_119237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119237).length < 2 ^ (prefixWord ++ tailWord_119237).sum := by decide
  have hdescent : baseEnd_119237 < baseStart_119237 := by decide
  rcases family_descends (prefixWord ++ tailWord_119237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119240 : List Nat := [2, 1, 3, 1, 3, 4, 1, 5]
def baseStart_119240 : Nat := 118140960795 + 119240 * 2 ^ 59
def prefixEnd_119240 : Nat := 4983230072969 + 3 ^ 40 * 119240 * 2
def baseEnd_119240 : Nat := 18141461701398135304187

theorem tailTrace_119240 : CollatzResearch.WordTrace tailWord_119240 prefixEnd_119240 18141461701398135304187 := by
  unfold tailWord_119240
  simp only [CollatzResearch.WordTrace]
  refine ⟨2174520044010659707901587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2899360058680879610535449 2174520044010659707901587)
  ·
    refine ⟨3261780066015989561852381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2174520044010659707901587 3261780066015989561852381)
    ·
      refine ⟨1223167524755996085694643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3261780066015989561852381 1223167524755996085694643)
      ·
        refine ⟨1834751287133994128541965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1223167524755996085694643 1834751287133994128541965)
        ·
          refine ⟨688031732675247798203237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1834751287133994128541965 688031732675247798203237)
          ·
            refine ⟨129005949876608962163107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 688031732675247798203237 129005949876608962163107)
            ·
              refine ⟨193508924814913443244661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129005949876608962163107 193508924814913443244661)
              ·
                refine ⟨18141461701398135304187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193508924814913443244661 18141461701398135304187)
                ·
                  rfl

theorem cell20_119240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 5].length) (baseStart_119240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119240 prefixEnd_119240 := by exact prefixLift 119240
  have htrace : WordTrace (prefixWord ++ tailWord_119240) baseStart_119240 baseEnd_119240 := by
    simpa [prefixWord, tailWord_119240, baseEnd_119240] using wordTrace_append hprefix tailTrace_119240
  have hstable : (prefixWord ++ tailWord_119240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119240).length < 2 ^ (prefixWord ++ tailWord_119240).sum := by decide
  have hdescent : baseEnd_119240 < baseStart_119240 := by decide
  rcases family_descends (prefixWord ++ tailWord_119240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119250 : List Nat := [3, 2, 2, 4, 1, 1, 1, 2, 4]
def baseStart_119250 : Nat := 118140960795 + 119250 * 2 ^ 59
def prefixEnd_119250 : Nat := 4983230072969 + 3 ^ 40 * 119250 * 2
def baseEnd_119250 : Nat := 54428949376678815579187

theorem tailTrace_119250 : CollatzResearch.WordTrace tailWord_119250 prefixEnd_119250 54428949376678815579187 := by
  unfold tailWord_119250
  simp only [CollatzResearch.WordTrace]
  refine ⟨1087351204496272780916801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2899603211990060749111469 1087351204496272780916801)
  ·
    refine ⟨815513403372204585687601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1087351204496272780916801 815513403372204585687601)
    ·
      refine ⟨611635052529153439265701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 815513403372204585687601 611635052529153439265701)
      ·
        refine ⟨114681572349216269862319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 611635052529153439265701 114681572349216269862319)
        ·
          refine ⟨172022358523824404793479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114681572349216269862319 172022358523824404793479)
          ·
            refine ⟨258033537785736607190219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172022358523824404793479 258033537785736607190219)
            ·
              refine ⟨387050306678604910785329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258033537785736607190219 387050306678604910785329)
              ·
                refine ⟨290287730008953683088997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387050306678604910785329 290287730008953683088997)
                ·
                  refine ⟨54428949376678815579187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 290287730008953683088997 54428949376678815579187)
                  ·
                    rfl

theorem cell20_119250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_119250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119250 prefixEnd_119250 := by exact prefixLift 119250
  have htrace : WordTrace (prefixWord ++ tailWord_119250) baseStart_119250 baseEnd_119250 := by
    simpa [prefixWord, tailWord_119250, baseEnd_119250] using wordTrace_append hprefix tailTrace_119250
  have hstable : (prefixWord ++ tailWord_119250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119250).length < 2 ^ (prefixWord ++ tailWord_119250).sum := by decide
  have hdescent : baseEnd_119250 < baseStart_119250 := by decide
  rcases family_descends (prefixWord ++ tailWord_119250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119275 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 6]
def baseStart_119275 : Nat := 118140960795 + 119275 * 2 ^ 59
def prefixEnd_119275 : Nat := 4983230072969 + 3 ^ 40 * 119275 * 2
def baseEnd_119275 : Nat := 54440360057889839745751

theorem tailTrace_119275 : CollatzResearch.WordTrace tailWord_119275 prefixEnd_119275 54440360057889839745751 := by
  unfold tailWord_119275
  simp only [CollatzResearch.WordTrace]
  refine ⟨4350316642894520393327279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2900211095263013595551519 4350316642894520393327279)
  ·
    refine ⟨6525474964341780589990919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4350316642894520393327279 6525474964341780589990919)
    ·
      refine ⟨9788212446512670884986379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6525474964341780589990919 9788212446512670884986379)
      ·
        refine ⟨14682318669769006327479569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9788212446512670884986379 14682318669769006327479569)
        ·
          refine ⟨11011739002326754745609677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14682318669769006327479569 11011739002326754745609677)
          ·
            refine ⟨4129402125872533029603629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11011739002326754745609677 4129402125872533029603629)
            ·
              refine ⟨1548525797202199886101361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4129402125872533029603629 1548525797202199886101361)
              ·
                refine ⟨1161394347901649914576021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548525797202199886101361 1161394347901649914576021)
                ·
                  refine ⟨54440360057889839745751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1161394347901649914576021 54440360057889839745751)
                  ·
                    rfl

theorem cell20_119275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_119275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119275 prefixEnd_119275 := by exact prefixLift 119275
  have htrace : WordTrace (prefixWord ++ tailWord_119275) baseStart_119275 baseEnd_119275 := by
    simpa [prefixWord, tailWord_119275, baseEnd_119275] using wordTrace_append hprefix tailTrace_119275
  have hstable : (prefixWord ++ tailWord_119275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119275).length < 2 ^ (prefixWord ++ tailWord_119275).sum := by decide
  have hdescent : baseEnd_119275 < baseStart_119275 := by decide
  rcases family_descends (prefixWord ++ tailWord_119275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119298 : List Nat := [3, 4, 1, 2, 2, 1, 3, 1, 3]
def baseStart_119298 : Nat := 118140960795 + 119298 * 2 ^ 59
def prefixEnd_119298 : Nat := 4983230072969 + 3 ^ 40 * 119298 * 2
def baseEnd_119298 : Nat := 54450857884603981978991

theorem tailTrace_119298 : CollatzResearch.WordTrace tailWord_119298 prefixEnd_119298 54450857884603981978991 := by
  unfold tailWord_119298
  simp only [CollatzResearch.WordTrace]
  refine ⟨1087788880452798830353637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2900770347874130214276365 1087788880452798830353637)
  ·
    refine ⟨203960415084899780691307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1087788880452798830353637 203960415084899780691307)
    ·
      refine ⟨305940622627349671036961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203960415084899780691307 305940622627349671036961)
      ·
        refine ⟨229455466970512253277721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305940622627349671036961 229455466970512253277721)
        ·
          refine ⟨172091600227884189958291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229455466970512253277721 172091600227884189958291)
          ·
            refine ⟨258137400341826284937437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172091600227884189958291 258137400341826284937437)
            ·
              refine ⟨96801525128184856851539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258137400341826284937437 96801525128184856851539)
              ·
                refine ⟨145202287692277285277309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96801525128184856851539 145202287692277285277309)
                ·
                  refine ⟨54450857884603981978991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145202287692277285277309 54450857884603981978991)
                  ·
                    rfl

theorem cell20_119298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_119298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119298 prefixEnd_119298 := by exact prefixLift 119298
  have htrace : WordTrace (prefixWord ++ tailWord_119298) baseStart_119298 baseEnd_119298 := by
    simpa [prefixWord, tailWord_119298, baseEnd_119298] using wordTrace_append hprefix tailTrace_119298
  have hstable : (prefixWord ++ tailWord_119298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119298).length < 2 ^ (prefixWord ++ tailWord_119298).sum := by decide
  have hdescent : baseEnd_119298 < baseStart_119298 := by decide
  rcases family_descends (prefixWord ++ tailWord_119298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119313 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 6]
def baseStart_119313 : Nat := 118140960795 + 119313 * 2 ^ 59
def prefixEnd_119313 : Nat := 4983230072969 + 3 ^ 40 * 119313 * 2
def baseEnd_119313 : Nat := 54457704293330596478929

theorem tailTrace_119313 : CollatzResearch.WordTrace tailWord_119313 prefixEnd_119313 54457704293330596478929 := by
  unfold tailWord_119313
  simp only [CollatzResearch.WordTrace]
  refine ⟨4351702616756852883210593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2901135077837901922140395 4351702616756852883210593)
  ·
    refine ⟨3263776962567639662407945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4351702616756852883210593 3263776962567639662407945)
    ·
      refine ⟨2447832721925729746805959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3263776962567639662407945 2447832721925729746805959)
      ·
        refine ⟨3671749082888594620208939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2447832721925729746805959 3671749082888594620208939)
        ·
          refine ⟨5507623624332891930313409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3671749082888594620208939 5507623624332891930313409)
          ·
            refine ⟨4130717718249668947735057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5507623624332891930313409 4130717718249668947735057)
            ·
              refine ⟨3098038288687251710801293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4130717718249668947735057 3098038288687251710801293)
              ·
                refine ⟨1161764358257719391550485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3098038288687251710801293 1161764358257719391550485)
                ·
                  refine ⟨54457704293330596478929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1161764358257719391550485 54457704293330596478929)
                  ·
                    rfl

theorem cell20_119313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_119313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119313 prefixEnd_119313 := by exact prefixLift 119313
  have htrace : WordTrace (prefixWord ++ tailWord_119313) baseStart_119313 baseEnd_119313 := by
    simpa [prefixWord, tailWord_119313, baseEnd_119313] using wordTrace_append hprefix tailTrace_119313
  have hstable : (prefixWord ++ tailWord_119313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119313).length < 2 ^ (prefixWord ++ tailWord_119313).sum := by decide
  have hdescent : baseEnd_119313 < baseStart_119313 := by decide
  rcases family_descends (prefixWord ++ tailWord_119313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119344 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 5]
def baseStart_119344 : Nat := 118140960795 + 119344 * 2 ^ 59
def prefixEnd_119344 : Nat := 4983230072969 + 3 ^ 40 * 119344 * 2
def baseEnd_119344 : Nat := 54471853538032266445469

theorem tailTrace_119344 : CollatzResearch.WordTrace tailWord_119344 prefixEnd_119344 54471853538032266445469 := by
  unfold tailWord_119344
  simp only [CollatzResearch.WordTrace]
  refine ⟨2176416639822272588794543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2901888853096363451726057 2176416639822272588794543)
  ·
    refine ⟨3264624959733408883191815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2176416639822272588794543 3264624959733408883191815)
    ·
      refine ⟨4896937439600113324787723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3264624959733408883191815 4896937439600113324787723)
      ·
        refine ⟨7345406159400169987181585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4896937439600113324787723 7345406159400169987181585)
        ·
          refine ⟨5509054619550127490386189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7345406159400169987181585 5509054619550127490386189)
          ·
            refine ⟨2065895482331297808894821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5509054619550127490386189 2065895482331297808894821)
            ·
              refine ⟨387355402937118339167779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2065895482331297808894821 387355402937118339167779)
              ·
                refine ⟨581033104405677508751669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387355402937118339167779 581033104405677508751669)
                ·
                  refine ⟨54471853538032266445469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 581033104405677508751669 54471853538032266445469)
                  ·
                    rfl

theorem cell20_119344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_119344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119344 prefixEnd_119344 := by exact prefixLift 119344
  have htrace : WordTrace (prefixWord ++ tailWord_119344) baseStart_119344 baseEnd_119344 := by
    simpa [prefixWord, tailWord_119344, baseEnd_119344] using wordTrace_append hprefix tailTrace_119344
  have hstable : (prefixWord ++ tailWord_119344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119344).length < 2 ^ (prefixWord ++ tailWord_119344).sum := by decide
  have hdescent : baseEnd_119344 < baseStart_119344 := by decide
  rcases family_descends (prefixWord ++ tailWord_119344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119357 : List Nat := [1, 4, 1, 3, 2, 3, 2, 1, 3]
def baseStart_119357 : Nat := 118140960795 + 119357 * 2 ^ 59
def prefixEnd_119357 : Nat := 4983230072969 + 3 ^ 40 * 119357 * 2
def baseEnd_119357 : Nat := 54477787092261999012083

theorem tailTrace_119357 : CollatzResearch.WordTrace tailWord_119357 prefixEnd_119357 54477787092261999012083 := by
  unfold tailWord_119357
  simp only [CollatzResearch.WordTrace]
  refine ⟨4353307428597448397812325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2902204952398298931874883 4353307428597448397812325)
  ·
    refine ⟨816245142862021574589811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4353307428597448397812325 816245142862021574589811)
    ·
      refine ⟨1224367714293032361884717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 816245142862021574589811 1224367714293032361884717)
      ·
        refine ⟨459137892859887135706769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1224367714293032361884717 459137892859887135706769)
        ·
          refine ⟨344353419644915351780077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 459137892859887135706769 344353419644915351780077)
          ·
            refine ⟨129132532366843256917529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344353419644915351780077 129132532366843256917529)
            ·
              refine ⟨96849399275132442688147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129132532366843256917529 96849399275132442688147)
              ·
                refine ⟨145274098912698664032221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96849399275132442688147 145274098912698664032221)
                ·
                  refine ⟨54477787092261999012083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145274098912698664032221 54477787092261999012083)
                  ·
                    rfl

theorem cell20_119357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_119357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119357 prefixEnd_119357 := by exact prefixLift 119357
  have htrace : WordTrace (prefixWord ++ tailWord_119357) baseStart_119357 baseEnd_119357 := by
    simpa [prefixWord, tailWord_119357, baseEnd_119357] using wordTrace_append hprefix tailTrace_119357
  have hstable : (prefixWord ++ tailWord_119357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119357).length < 2 ^ (prefixWord ++ tailWord_119357).sum := by decide
  have hdescent : baseEnd_119357 < baseStart_119357 := by decide
  rcases family_descends (prefixWord ++ tailWord_119357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119427 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 6]
def baseStart_119427 : Nat := 118140960795 + 119427 * 2 ^ 59
def prefixEnd_119427 : Nat := 4983230072969 + 3 ^ 40 * 119427 * 2
def baseEnd_119427 : Nat := 54509736999652866678463

theorem tailTrace_119427 : CollatzResearch.WordTrace tailWord_119427 prefixEnd_119427 54509736999652866678463 := by
  unfold tailWord_119427
  simp only [CollatzResearch.WordTrace]
  refine ⟨4355860538343850352860535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2903907025562566901907023 4355860538343850352860535)
  ·
    refine ⟨6533790807515775529290803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4355860538343850352860535 6533790807515775529290803)
    ·
      refine ⟨9800686211273663293936205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6533790807515775529290803 9800686211273663293936205)
      ·
        refine ⟨3675257329227623735226077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9800686211273663293936205 3675257329227623735226077)
        ·
          refine ⟨1378221498460358900709779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3675257329227623735226077 1378221498460358900709779)
          ·
            refine ⟨2067332247690538351064669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378221498460358900709779 2067332247690538351064669)
            ·
              refine ⟨775249592883951881649251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2067332247690538351064669 775249592883951881649251)
              ·
                refine ⟨1162874389325927822473877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775249592883951881649251 1162874389325927822473877)
                ·
                  refine ⟨54509736999652866678463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1162874389325927822473877 54509736999652866678463)
                  ·
                    rfl

theorem cell20_119427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_119427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119427 prefixEnd_119427 := by exact prefixLift 119427
  have htrace : WordTrace (prefixWord ++ tailWord_119427) baseStart_119427 baseEnd_119427 := by
    simpa [prefixWord, tailWord_119427, baseEnd_119427] using wordTrace_append hprefix tailTrace_119427
  have hstable : (prefixWord ++ tailWord_119427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119427).length < 2 ^ (prefixWord ++ tailWord_119427).sum := by decide
  have hdescent : baseEnd_119427 < baseStart_119427 := by decide
  rcases family_descends (prefixWord ++ tailWord_119427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119450 : List Nat := [3, 1, 1, 6, 2, 1, 1, 2, 3]
def baseStart_119450 : Nat := 118140960795 + 119450 * 2 ^ 59
def prefixEnd_119450 : Nat := 4983230072969 + 3 ^ 40 * 119450 * 2
def baseEnd_119450 : Nat := 54520234826367008911703

theorem tailTrace_119450 : CollatzResearch.WordTrace tailWord_119450 prefixEnd_119450 54520234826367008911703 := by
  unfold tailWord_119450
  simp only [CollatzResearch.WordTrace]
  refine ⟨1089174854315131320236951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2904466278173683520631869 1089174854315131320236951)
  ·
    refine ⟨1633762281472696980355427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1089174854315131320236951 1633762281472696980355427)
    ·
      refine ⟨2450643422209045470533141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1633762281472696980355427 2450643422209045470533141)
      ·
        refine ⟨114873910416049006431241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2450643422209045470533141 114873910416049006431241)
        ·
          refine ⟨86155432812036754823431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114873910416049006431241 86155432812036754823431)
          ·
            refine ⟨129233149218055132235147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86155432812036754823431 129233149218055132235147)
            ·
              refine ⟨193849723827082698352721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129233149218055132235147 193849723827082698352721)
              ·
                refine ⟨145387292870312023764541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193849723827082698352721 145387292870312023764541)
                ·
                  refine ⟨54520234826367008911703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145387292870312023764541 54520234826367008911703)
                  ·
                    rfl

theorem cell20_119450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_119450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119450 prefixEnd_119450 := by exact prefixLift 119450
  have htrace : WordTrace (prefixWord ++ tailWord_119450) baseStart_119450 baseEnd_119450 := by
    simpa [prefixWord, tailWord_119450, baseEnd_119450] using wordTrace_append hprefix tailTrace_119450
  have hstable : (prefixWord ++ tailWord_119450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119450).length < 2 ^ (prefixWord ++ tailWord_119450).sum := by decide
  have hdescent : baseEnd_119450 < baseStart_119450 := by decide
  rcases family_descends (prefixWord ++ tailWord_119450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119465 : List Nat := [1, 2, 1, 1, 1, 1, 2, 7, 4]
def baseStart_119465 : Nat := 118140960795 + 119465 * 2 ^ 59
def prefixEnd_119465 : Nat := 4983230072969 + 3 ^ 40 * 119465 * 2
def baseEnd_119465 : Nat := 54527081235093623411641

theorem tailTrace_119465 : CollatzResearch.WordTrace tailWord_119465 prefixEnd_119465 54527081235093623411641 := by
  unfold tailWord_119465
  simp only [CollatzResearch.WordTrace]
  refine ⟨4357246512206182842743849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2904831008137455228495899 4357246512206182842743849)
  ·
    refine ⟨3267934884154637132057887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4357246512206182842743849 3267934884154637132057887)
    ·
      refine ⟨4901902326231955698086831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3267934884154637132057887 4901902326231955698086831)
      ·
        refine ⟨7352853489347933547130247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4901902326231955698086831 7352853489347933547130247)
        ·
          refine ⟨11029280234021900320695371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7352853489347933547130247 11029280234021900320695371)
          ·
            refine ⟨16543920351032850481043057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11029280234021900320695371 16543920351032850481043057)
            ·
              refine ⟨12407940263274637860782293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16543920351032850481043057 12407940263274637860782293)
              ·
                refine ⟨290811099920499324862085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12407940263274637860782293 290811099920499324862085)
                ·
                  refine ⟨54527081235093623411641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 290811099920499324862085 54527081235093623411641)
                  ·
                    rfl

theorem cell20_119465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_119465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119465 prefixEnd_119465 := by exact prefixLift 119465
  have htrace : WordTrace (prefixWord ++ tailWord_119465) baseStart_119465 baseEnd_119465 := by
    simpa [prefixWord, tailWord_119465, baseEnd_119465] using wordTrace_append hprefix tailTrace_119465
  have hstable : (prefixWord ++ tailWord_119465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119465).length < 2 ^ (prefixWord ++ tailWord_119465).sum := by decide
  have hdescent : baseEnd_119465 < baseStart_119465 := by decide
  rcases family_descends (prefixWord ++ tailWord_119465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119472 : List Nat := [2, 1, 1, 1, 2, 1, 3, 9]
def baseStart_119472 : Nat := 118140960795 + 119472 * 2 ^ 59
def prefixEnd_119472 : Nat := 4983230072969 + 3 ^ 40 * 119472 * 2
def baseEnd_119472 : Nat := 18176758741944236726093

theorem tailTrace_119472 : CollatzResearch.WordTrace tailWord_119472 prefixEnd_119472 18176758741944236726093 := by
  unfold tailWord_119472
  simp only [CollatzResearch.WordTrace]
  refine ⟨2178750911590411519124335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2905001215453882025499113 2178750911590411519124335)
  ·
    refine ⟨3268126367385617278686503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2178750911590411519124335 3268126367385617278686503)
    ·
      refine ⟨4902189551078425918029755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3268126367385617278686503 4902189551078425918029755)
      ·
        refine ⟨7353284326617638877044633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4902189551078425918029755 7353284326617638877044633)
        ·
          refine ⟨5514963244963229157783475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7353284326617638877044633 5514963244963229157783475)
          ·
            refine ⟨8272444867444843736675213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5514963244963229157783475 8272444867444843736675213)
            ·
              refine ⟨3102166825291816401253205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8272444867444843736675213 3102166825291816401253205)
              ·
                refine ⟨18176758741944236726093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3102166825291816401253205 18176758741944236726093)
                ·
                  rfl

theorem cell20_119472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_119472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119472 prefixEnd_119472 := by exact prefixLift 119472
  have htrace : WordTrace (prefixWord ++ tailWord_119472) baseStart_119472 baseEnd_119472 := by
    simpa [prefixWord, tailWord_119472, baseEnd_119472] using wordTrace_append hprefix tailTrace_119472
  have hstable : (prefixWord ++ tailWord_119472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119472).length < 2 ^ (prefixWord ++ tailWord_119472).sum := by decide
  have hdescent : baseEnd_119472 < baseStart_119472 := by decide
  rcases family_descends (prefixWord ++ tailWord_119472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119496 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 5]
def baseStart_119496 : Nat := 118140960795 + 119496 * 2 ^ 59
def prefixEnd_119496 : Nat := 4983230072969 + 3 ^ 40 * 119496 * 2
def baseEnd_119496 : Nat := 54541230479795293378181

theorem tailTrace_119496 : CollatzResearch.WordTrace tailWord_119496 prefixEnd_119496 54541230479795293378181 := by
  unfold tailWord_119496
  simp only [CollatzResearch.WordTrace]
  refine ⟨2179188587546937568561171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2905584783395916758081561 2179188587546937568561171)
  ·
    refine ⟨3268782881320406352841757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2179188587546937568561171 3268782881320406352841757)
    ·
      refine ⟨1225793580495152382315659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3268782881320406352841757 1225793580495152382315659)
      ·
        refine ⟨1838690370742728573473489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1225793580495152382315659 1838690370742728573473489)
        ·
          refine ⟨1379017778057046430105117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1838690370742728573473489 1379017778057046430105117)
          ·
            refine ⟨517131666771392411289419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1379017778057046430105117 517131666771392411289419)
            ·
              refine ⟨775697500157088616934129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517131666771392411289419 775697500157088616934129)
              ·
                refine ⟨581773125117816462700597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775697500157088616934129 581773125117816462700597)
                ·
                  refine ⟨54541230479795293378181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 581773125117816462700597 54541230479795293378181)
                  ·
                    rfl

theorem cell20_119496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_119496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119496 prefixEnd_119496 := by exact prefixLift 119496
  have htrace : WordTrace (prefixWord ++ tailWord_119496) baseStart_119496 baseEnd_119496 := by
    simpa [prefixWord, tailWord_119496, baseEnd_119496] using wordTrace_append hprefix tailTrace_119496
  have hstable : (prefixWord ++ tailWord_119496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119496).length < 2 ^ (prefixWord ++ tailWord_119496).sum := by decide
  have hdescent : baseEnd_119496 < baseStart_119496 := by decide
  rcases family_descends (prefixWord ++ tailWord_119496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119506 : List Nat := [3, 2, 2, 2, 3, 2, 6]
def baseStart_119506 : Nat := 118140960795 + 119506 * 2 ^ 59
def prefixEnd_119506 : Nat := 4983230072969 + 3 ^ 40 * 119506 * 2
def baseEnd_119506 : Nat := 6060643861364411449423

theorem tailTrace_119506 : CollatzResearch.WordTrace tailWord_119506 prefixEnd_119506 6060643861364411449423 := by
  unfold tailWord_119506
  simp only [CollatzResearch.WordTrace]
  refine ⟨1089685476264411711246593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2905827936705097896657581 1089685476264411711246593)
  ·
    refine ⟨817264107198308783434945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1089685476264411711246593 817264107198308783434945)
    ·
      refine ⟨612948080398731587576209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 817264107198308783434945 612948080398731587576209)
      ·
        refine ⟨459711060299048690682157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 612948080398731587576209 459711060299048690682157)
        ·
          refine ⟨172391647612143259005809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459711060299048690682157 172391647612143259005809)
          ·
            refine ⟨129293735709107444254357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172391647612143259005809 129293735709107444254357)
            ·
              refine ⟨6060643861364411449423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129293735709107444254357 6060643861364411449423)
              ·
                rfl

theorem cell20_119506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 6].length) (baseStart_119506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119506 prefixEnd_119506 := by exact prefixLift 119506
  have htrace : WordTrace (prefixWord ++ tailWord_119506) baseStart_119506 baseEnd_119506 := by
    simpa [prefixWord, tailWord_119506, baseEnd_119506] using wordTrace_append hprefix tailTrace_119506
  have hstable : (prefixWord ++ tailWord_119506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119506).length < 2 ^ (prefixWord ++ tailWord_119506).sum := by decide
  have hdescent : baseEnd_119506 < baseStart_119506 := by decide
  rcases family_descends (prefixWord ++ tailWord_119506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119516 : List Nat := [2, 2, 5, 1, 1, 3, 1, 1, 4]
def baseStart_119516 : Nat := 118140960795 + 119516 * 2 ^ 59
def prefixEnd_119516 : Nat := 4983230072969 + 3 ^ 40 * 119516 * 2
def baseEnd_119516 : Nat := 54550359024764112711433

theorem tailTrace_119516 : CollatzResearch.WordTrace tailWord_119516 prefixEnd_119516 54550359024764112711433 := by
  unfold tailWord_119516
  simp only [CollatzResearch.WordTrace]
  refine ⟨2179553317510709276425201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2906071090014279035233601 2179553317510709276425201)
  ·
    refine ⟨1634664988133031957318901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2179553317510709276425201 1634664988133031957318901)
    ·
      refine ⟨153249842637471745998647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1634664988133031957318901 153249842637471745998647)
      ·
        refine ⟨229874763956207618997971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153249842637471745998647 229874763956207618997971)
        ·
          refine ⟨344812145934311428496957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229874763956207618997971 344812145934311428496957)
          ·
            refine ⟨129304554725366785686359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 344812145934311428496957 129304554725366785686359)
            ·
              refine ⟨193956832088050178529539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129304554725366785686359 193956832088050178529539)
              ·
                refine ⟨290935248132075267794309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193956832088050178529539 290935248132075267794309)
                ·
                  refine ⟨54550359024764112711433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 290935248132075267794309 54550359024764112711433)
                  ·
                    rfl

theorem cell20_119516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_119516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119516 prefixEnd_119516 := by exact prefixLift 119516
  have htrace : WordTrace (prefixWord ++ tailWord_119516) baseStart_119516 baseEnd_119516 := by
    simpa [prefixWord, tailWord_119516, baseEnd_119516] using wordTrace_append hprefix tailTrace_119516
  have hstable : (prefixWord ++ tailWord_119516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119516).length < 2 ^ (prefixWord ++ tailWord_119516).sum := by decide
  have hdescent : baseEnd_119516 < baseStart_119516 := by decide
  rcases family_descends (prefixWord ++ tailWord_119516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119624 : List Nat := [2, 1, 3, 1, 1, 3, 9]
def baseStart_119624 : Nat := 118140960795 + 119624 * 2 ^ 59
def prefixEnd_119624 : Nat := 4983230072969 + 3 ^ 40 * 119624 * 2
def baseEnd_119624 : Nat := 6066628129732859678999

theorem tailTrace_119624 : CollatzResearch.WordTrace tailWord_119624 prefixEnd_119624 6066628129732859678999 := by
  unfold tailWord_119624
  simp only [CollatzResearch.WordTrace]
  refine ⟨2181522859315076498890963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2908697145753435331854617 2181522859315076498890963)
  ·
    refine ⟨3272284288972614748336445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2181522859315076498890963 3272284288972614748336445)
    ·
      refine ⟨1227106608364730530626167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3272284288972614748336445 1227106608364730530626167)
      ·
        refine ⟨1840659912547095795939251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1227106608364730530626167 1840659912547095795939251)
        ·
          refine ⟨2760989868820643693908877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1840659912547095795939251 2760989868820643693908877)
          ·
            refine ⟨1035371200807741385215829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2760989868820643693908877 1035371200807741385215829)
            ·
              refine ⟨6066628129732859678999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1035371200807741385215829 6066628129732859678999)
              ·
                rfl

theorem cell20_119624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 9].length) (baseStart_119624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119624 prefixEnd_119624 := by exact prefixLift 119624
  have htrace : WordTrace (prefixWord ++ tailWord_119624) baseStart_119624 baseEnd_119624 := by
    simpa [prefixWord, tailWord_119624, baseEnd_119624] using wordTrace_append hprefix tailTrace_119624
  have hstable : (prefixWord ++ tailWord_119624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119624).length < 2 ^ (prefixWord ++ tailWord_119624).sum := by decide
  have hdescent : baseEnd_119624 < baseStart_119624 := by decide
  rcases family_descends (prefixWord ++ tailWord_119624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119634 : List Nat := [3, 2, 2, 1, 1, 2, 4, 1, 4]
def baseStart_119634 : Nat := 118140960795 + 119634 * 2 ^ 59
def prefixEnd_119634 : Nat := 4983230072969 + 3 ^ 40 * 119634 * 2
def baseEnd_119634 : Nat := 54604217440080146777617

theorem tailTrace_119634 : CollatzResearch.WordTrace tailWord_119634 prefixEnd_119634 54604217440080146777617 := by
  unfold tailWord_119634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1090852612148481176411489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2908940299062616470430637 1090852612148481176411489)
  ·
    refine ⟨818139459111360882308617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1090852612148481176411489 818139459111360882308617)
    ·
      refine ⟨613604594333520661731463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 818139459111360882308617 613604594333520661731463)
      ·
        refine ⟨920406891500280992597195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613604594333520661731463 920406891500280992597195)
        ·
          refine ⟨1380610337250421488895793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920406891500280992597195 1380610337250421488895793)
          ·
            refine ⟨1035457752937816116671845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1380610337250421488895793 1035457752937816116671845)
            ·
              refine ⟨194148328675840521875971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1035457752937816116671845 194148328675840521875971)
              ·
                refine ⟨291222493013760782813957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194148328675840521875971 291222493013760782813957)
                ·
                  refine ⟨54604217440080146777617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 291222493013760782813957 54604217440080146777617)
                  ·
                    rfl

theorem cell20_119634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_119634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119634 prefixEnd_119634 := by exact prefixLift 119634
  have htrace : WordTrace (prefixWord ++ tailWord_119634) baseStart_119634 baseEnd_119634 := by
    simpa [prefixWord, tailWord_119634, baseEnd_119634] using wordTrace_append hprefix tailTrace_119634
  have hstable : (prefixWord ++ tailWord_119634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119634).length < 2 ^ (prefixWord ++ tailWord_119634).sum := by decide
  have hdescent : baseEnd_119634 < baseStart_119634 := by decide
  rcases family_descends (prefixWord ++ tailWord_119634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119672 : List Nat := [2, 1, 2, 1, 1, 1, 1, 9, 2]
def baseStart_119672 : Nat := 118140960795 + 119672 * 2 ^ 59
def prefixEnd_119672 : Nat := 4983230072969 + 3 ^ 40 * 119672 * 2
def baseEnd_119672 : Nat := 54621561675520903510795

theorem tailTrace_119672 : CollatzResearch.WordTrace tailWord_119672 prefixEnd_119672 54621561675520903510795 := by
  unfold tailWord_119672
  simp only [CollatzResearch.WordTrace]
  refine ⟨2182398211228128597764635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2909864281637504797019513 2182398211228128597764635)
  ·
    refine ⟨3273597316842192896646953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2182398211228128597764635 3273597316842192896646953)
    ·
      refine ⟨2455197987631644672485215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3273597316842192896646953 2455197987631644672485215)
      ·
        refine ⟨3682796981447467008727823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2455197987631644672485215 3682796981447467008727823)
        ·
          refine ⟨5524195472171200513091735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3682796981447467008727823 5524195472171200513091735)
          ·
            refine ⟨8286293208256800769637603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5524195472171200513091735 8286293208256800769637603)
            ·
              refine ⟨12429439812385201154456405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8286293208256800769637603 12429439812385201154456405)
              ·
                refine ⟨72828748900694538014393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12429439812385201154456405 72828748900694538014393)
                ·
                  refine ⟨54621561675520903510795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72828748900694538014393 54621561675520903510795)
                  ·
                    rfl

theorem cell20_119672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 2].length) (baseStart_119672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119672 prefixEnd_119672 := by exact prefixLift 119672
  have htrace : WordTrace (prefixWord ++ tailWord_119672) baseStart_119672 baseEnd_119672 := by
    simpa [prefixWord, tailWord_119672, baseEnd_119672] using wordTrace_append hprefix tailTrace_119672
  have hstable : (prefixWord ++ tailWord_119672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119672).length < 2 ^ (prefixWord ++ tailWord_119672).sum := by decide
  have hdescent : baseEnd_119672 < baseStart_119672 := by decide
  rcases family_descends (prefixWord ++ tailWord_119672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119744 : List Nat := [2, 1, 1, 2, 3, 5, 2, 2, 2]
def baseStart_119744 : Nat := 118140960795 + 119744 * 2 ^ 59
def prefixEnd_119744 : Nat := 4983230072969 + 3 ^ 40 * 119744 * 2
def baseEnd_119744 : Nat := 54654424437408653110501

theorem tailTrace_119744 : CollatzResearch.WordTrace tailWord_119744 prefixEnd_119744 54654424437408653110501 := by
  unfold tailWord_119744
  simp only [CollatzResearch.WordTrace]
  refine ⟨2183711239097706746075143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2911614985463608994766857 2183711239097706746075143)
  ·
    refine ⟨3275566858646560119112715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2183711239097706746075143 3275566858646560119112715)
    ·
      refine ⟨4913350287969840178669073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3275566858646560119112715 4913350287969840178669073)
      ·
        refine ⟨3685012715977380134001805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4913350287969840178669073 3685012715977380134001805)
        ·
          refine ⟨1381879768491517550250677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3685012715977380134001805 1381879768491517550250677)
          ·
            refine ⟨129551228296079770336001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1381879768491517550250677 129551228296079770336001)
            ·
              refine ⟨97163421222059827752001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129551228296079770336001 97163421222059827752001)
              ·
                refine ⟨72872565916544870814001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97163421222059827752001 72872565916544870814001)
                ·
                  refine ⟨54654424437408653110501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72872565916544870814001 54654424437408653110501)
                  ·
                    rfl

theorem cell20_119744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 2].length) (baseStart_119744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119744 prefixEnd_119744 := by exact prefixLift 119744
  have htrace : WordTrace (prefixWord ++ tailWord_119744) baseStart_119744 baseEnd_119744 := by
    simpa [prefixWord, tailWord_119744, baseEnd_119744] using wordTrace_append hprefix tailTrace_119744
  have hstable : (prefixWord ++ tailWord_119744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119744).length < 2 ^ (prefixWord ++ tailWord_119744).sum := by decide
  have hdescent : baseEnd_119744 < baseStart_119744 := by decide
  rcases family_descends (prefixWord ++ tailWord_119744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119755 : List Nat := [1, 1, 1, 1, 3, 7, 1, 5]
def baseStart_119755 : Nat := 118140960795 + 119755 * 2 ^ 59
def prefixEnd_119755 : Nat := 4983230072969 + 3 ^ 40 * 119755 * 2
def baseEnd_119755 : Nat := 18219815045713834581263

theorem tailTrace_119755 : CollatzResearch.WordTrace tailWord_119755 prefixEnd_119755 18219815045713834581263 := by
  unfold tailWord_119755
  simp only [CollatzResearch.WordTrace]
  refine ⟨4367823681155562370800719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2911882454103708247200479 4367823681155562370800719)
  ·
    refine ⟨6551735521733343556201079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4367823681155562370800719 6551735521733343556201079)
    ·
      refine ⟨9827603282600015334301619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6551735521733343556201079 9827603282600015334301619)
      ·
        refine ⟨14741404923900023001452429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9827603282600015334301619 14741404923900023001452429)
        ·
          refine ⟨5528026846462508625544661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14741404923900023001452429 5528026846462508625544661)
          ·
            refine ⟨129563129213965045911203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 5528026846462508625544661 129563129213965045911203)
            ·
              refine ⟨194344693820947568866805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129563129213965045911203 194344693820947568866805)
              ·
                refine ⟨18219815045713834581263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194344693820947568866805 18219815045713834581263)
                ·
                  rfl

theorem cell20_119755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 5].length) (baseStart_119755 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119755 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119755 prefixEnd_119755 := by exact prefixLift 119755
  have htrace : WordTrace (prefixWord ++ tailWord_119755) baseStart_119755 baseEnd_119755 := by
    simpa [prefixWord, tailWord_119755, baseEnd_119755] using wordTrace_append hprefix tailTrace_119755
  have hstable : (prefixWord ++ tailWord_119755).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119755).length < 2 ^ (prefixWord ++ tailWord_119755).sum := by decide
  have hdescent : baseEnd_119755 < baseStart_119755 := by decide
  rcases family_descends (prefixWord ++ tailWord_119755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119769 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 6]
def baseStart_119769 : Nat := 118140960795 + 119769 * 2 ^ 59
def prefixEnd_119769 : Nat := 4983230072969 + 3 ^ 40 * 119769 * 2
def baseEnd_119769 : Nat := 54665835118619677277065

theorem tailTrace_119769 : CollatzResearch.WordTrace tailWord_119769 prefixEnd_119769 54665835118619677277065 := by
  unfold tailWord_119769
  simp only [CollatzResearch.WordTrace]
  refine ⟨4368334303104842761810361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2912222868736561841206907 4368334303104842761810361)
  ·
    refine ⟨3276250727328632071357771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4368334303104842761810361 3276250727328632071357771)
    ·
      refine ⟨4914376090992948107036657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3276250727328632071357771 4914376090992948107036657)
      ·
        refine ⟨3685782068244711080277493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4914376090992948107036657 3685782068244711080277493)
        ·
          refine ⟨345542068897941663776015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3685782068244711080277493 345542068897941663776015)
          ·
            refine ⟨518313103346912495664023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345542068897941663776015 518313103346912495664023)
            ·
              refine ⟨777469655020368743496035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518313103346912495664023 777469655020368743496035)
              ·
                refine ⟨1166204482530553115244053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777469655020368743496035 1166204482530553115244053)
                ·
                  refine ⟨54665835118619677277065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1166204482530553115244053 54665835118619677277065)
                  ·
                    rfl

theorem cell20_119769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_119769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119769 prefixEnd_119769 := by exact prefixLift 119769
  have htrace : WordTrace (prefixWord ++ tailWord_119769) baseStart_119769 baseEnd_119769 := by
    simpa [prefixWord, tailWord_119769, baseEnd_119769] using wordTrace_append hprefix tailTrace_119769
  have hstable : (prefixWord ++ tailWord_119769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119769).length < 2 ^ (prefixWord ++ tailWord_119769).sum := by decide
  have hdescent : baseEnd_119769 < baseStart_119769 := by decide
  rcases family_descends (prefixWord ++ tailWord_119769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119831 : List Nat := [1, 1, 3, 5, 1, 2, 1, 6]
def baseStart_119831 : Nat := 118140960795 + 119831 * 2 ^ 59
def prefixEnd_119831 : Nat := 4983230072969 + 3 ^ 40 * 119831 * 2
def baseEnd_119831 : Nat := 18231377869341005736715

theorem tailTrace_119831 : CollatzResearch.WordTrace tailWord_119831 prefixEnd_119831 18231377869341005736715 := by
  unfold tailWord_119831
  simp only [CollatzResearch.WordTrace]
  refine ⟨4370595628880227350567347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2913730419253484900378231 4370595628880227350567347)
  ·
    refine ⟨6555893443320341025851021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4370595628880227350567347 6555893443320341025851021)
    ·
      refine ⟨2458460041245127884694133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6555893443320341025851021 2458460041245127884694133)
      ·
        refine ⟨230480628866730739190075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2458460041245127884694133 230480628866730739190075)
        ·
          refine ⟨345720943300096108785113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230480628866730739190075 345720943300096108785113)
          ·
            refine ⟨259290707475072081588835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345720943300096108785113 259290707475072081588835)
            ·
              refine ⟨388936061212608122383253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259290707475072081588835 388936061212608122383253)
              ·
                refine ⟨18231377869341005736715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 388936061212608122383253 18231377869341005736715)
                ·
                  rfl

theorem cell20_119831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 6].length) (baseStart_119831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119831 prefixEnd_119831 := by exact prefixLift 119831
  have htrace : WordTrace (prefixWord ++ tailWord_119831) baseStart_119831 baseEnd_119831 := by
    simpa [prefixWord, tailWord_119831, baseEnd_119831] using wordTrace_append hprefix tailTrace_119831
  have hstable : (prefixWord ++ tailWord_119831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119831).length < 2 ^ (prefixWord ++ tailWord_119831).sum := by decide
  have hdescent : baseEnd_119831 < baseStart_119831 := by decide
  rcases family_descends (prefixWord ++ tailWord_119831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119837 : List Nat := [1, 4, 2, 2, 4, 1, 1, 3, 2]
def baseStart_119837 : Nat := 118140960795 + 119837 * 2 ^ 59
def prefixEnd_119837 : Nat := 4983230072969 + 3 ^ 40 * 119837 * 2
def baseEnd_119837 : Nat := 54696872171513663010121

theorem tailTrace_119837 : CollatzResearch.WordTrace tailWord_119837 prefixEnd_119837 54696872171513663010121 := by
  unfold tailWord_119837
  simp only [CollatzResearch.WordTrace]
  refine ⟨4370814466858490375285765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2913876311238993583523843 4370814466858490375285765)
  ·
    refine ⟨819527712535966945366081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4370814466858490375285765 819527712535966945366081)
    ·
      refine ⟨614645784401975209024561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 819527712535966945366081 614645784401975209024561)
      ·
        refine ⟨460984338301481406768421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614645784401975209024561 460984338301481406768421)
        ·
          refine ⟨86434563431527763769079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 460984338301481406768421 86434563431527763769079)
          ·
            refine ⟨129651845147291645653619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86434563431527763769079 129651845147291645653619)
            ·
              refine ⟨194477767720937468480429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129651845147291645653619 194477767720937468480429)
              ·
                refine ⟨72929162895351550680161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194477767720937468480429 72929162895351550680161)
                ·
                  refine ⟨54696872171513663010121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72929162895351550680161 54696872171513663010121)
                  ·
                    rfl

theorem cell20_119837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_119837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119837 prefixEnd_119837 := by exact prefixLift 119837
  have htrace : WordTrace (prefixWord ++ tailWord_119837) baseStart_119837 baseEnd_119837 := by
    simpa [prefixWord, tailWord_119837, baseEnd_119837] using wordTrace_append hprefix tailTrace_119837
  have hstable : (prefixWord ++ tailWord_119837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119837).length < 2 ^ (prefixWord ++ tailWord_119837).sum := by decide
  have hdescent : baseEnd_119837 < baseStart_119837 := by decide
  rcases family_descends (prefixWord ++ tailWord_119837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119841 : List Nat := [1, 2, 3, 2, 3, 1, 3, 3, 2]
def baseStart_119841 : Nat := 118140960795 + 119841 * 2 ^ 59
def prefixEnd_119841 : Nat := 4983230072969 + 3 ^ 40 * 119841 * 2
def baseEnd_119841 : Nat := 54698697880507426876771

theorem tailTrace_119841 : CollatzResearch.WordTrace tailWord_119841 prefixEnd_119841 54698697880507426876771 := by
  unfold tailWord_119841
  simp only [CollatzResearch.WordTrace]
  refine ⟨4370960358843999058431377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2913973572562666038954251 4370960358843999058431377)
  ·
    refine ⟨3278220269132999293823533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4370960358843999058431377 3278220269132999293823533)
    ·
      refine ⟨1229332600924874735183825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3278220269132999293823533 1229332600924874735183825)
      ·
        refine ⟨921999450693656051387869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1229332600924874735183825 921999450693656051387869)
        ·
          refine ⟨345749794010121019270451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 921999450693656051387869 345749794010121019270451)
          ·
            refine ⟨518624691015181528905677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345749794010121019270451 518624691015181528905677)
            ·
              refine ⟨194484259130693073339629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 518624691015181528905677 194484259130693073339629)
              ·
                refine ⟨72931597174009902502361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194484259130693073339629 72931597174009902502361)
                ·
                  refine ⟨54698697880507426876771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72931597174009902502361 54698697880507426876771)
                  ·
                    rfl

theorem cell20_119841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 2].length) (baseStart_119841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119841 prefixEnd_119841 := by exact prefixLift 119841
  have htrace : WordTrace (prefixWord ++ tailWord_119841) baseStart_119841 baseEnd_119841 := by
    simpa [prefixWord, tailWord_119841, baseEnd_119841] using wordTrace_append hprefix tailTrace_119841
  have hstable : (prefixWord ++ tailWord_119841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119841).length < 2 ^ (prefixWord ++ tailWord_119841).sum := by decide
  have hdescent : baseEnd_119841 < baseStart_119841 := by decide
  rcases family_descends (prefixWord ++ tailWord_119841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119869 : List Nat := [1, 4, 1, 3, 1, 3, 2, 5]
def baseStart_119869 : Nat := 118140960795 + 119869 * 2 ^ 59
def prefixEnd_119869 : Nat := 4983230072969 + 3 ^ 40 * 119869 * 2
def baseEnd_119869 : Nat := 18237159281154591314441

theorem tailTrace_119869 : CollatzResearch.WordTrace tailWord_119869 prefixEnd_119869 18237159281154591314441 := by
  unfold tailWord_119869
  simp only [CollatzResearch.WordTrace]
  refine ⟨4371981602742559840450661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2914654401828373226967107 4371981602742559840450661)
  ·
    refine ⟨819746550514229970084499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4371981602742559840450661 819746550514229970084499)
    ·
      refine ⟨1229619825771344955126749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 819746550514229970084499 1229619825771344955126749)
      ·
        refine ⟨461107434664254358172531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1229619825771344955126749 461107434664254358172531)
        ·
          refine ⟨691661151996381537258797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461107434664254358172531 691661151996381537258797)
          ·
            refine ⟨259372931998643076472049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 691661151996381537258797 259372931998643076472049)
            ·
              refine ⟨194529698998982307354037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259372931998643076472049 194529698998982307354037)
              ·
                refine ⟨18237159281154591314441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194529698998982307354037 18237159281154591314441)
                ·
                  rfl

theorem cell20_119869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 5].length) (baseStart_119869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119869 prefixEnd_119869 := by exact prefixLift 119869
  have htrace : WordTrace (prefixWord ++ tailWord_119869) baseStart_119869 baseEnd_119869 := by
    simpa [prefixWord, tailWord_119869, baseEnd_119869] using wordTrace_append hprefix tailTrace_119869
  have hstable : (prefixWord ++ tailWord_119869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119869).length < 2 ^ (prefixWord ++ tailWord_119869).sum := by decide
  have hdescent : baseEnd_119869 < baseStart_119869 := by decide
  rcases family_descends (prefixWord ++ tailWord_119869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119897 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 5]
def baseStart_119897 : Nat := 118140960795 + 119897 * 2 ^ 59
def prefixEnd_119897 : Nat := 4983230072969 + 3 ^ 40 * 119897 * 2
def baseEnd_119897 : Nat := 54724257806420121009875

theorem tailTrace_119897 : CollatzResearch.WordTrace tailWord_119897 prefixEnd_119897 54724257806420121009875 := by
  unfold tailWord_119897
  simp only [CollatzResearch.WordTrace]
  refine ⟨4373002846641120622469945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2915335231094080414979963 4373002846641120622469945)
  ·
    refine ⟨3279752134980840466852459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4373002846641120622469945 3279752134980840466852459)
    ·
      refine ⟨4919628202471260700278689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3279752134980840466852459 4919628202471260700278689)
      ·
        refine ⟨3689721151853445525209017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4919628202471260700278689 3689721151853445525209017)
        ·
          refine ⟨2767290863890084143906763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3689721151853445525209017 2767290863890084143906763)
          ·
            refine ⟨4150936295835126215860145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2767290863890084143906763 4150936295835126215860145)
            ·
              refine ⟨3113202221876344661895109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4150936295835126215860145 3113202221876344661895109)
              ·
                refine ⟨583725416601814624105333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3113202221876344661895109 583725416601814624105333)
                ·
                  refine ⟨54724257806420121009875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 583725416601814624105333 54724257806420121009875)
                  ·
                    rfl

theorem cell20_119897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_119897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119897 prefixEnd_119897 := by exact prefixLift 119897
  have htrace : WordTrace (prefixWord ++ tailWord_119897) baseStart_119897 baseEnd_119897 := by
    simpa [prefixWord, tailWord_119897, baseEnd_119897] using wordTrace_append hprefix tailTrace_119897
  have hstable : (prefixWord ++ tailWord_119897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119897).length < 2 ^ (prefixWord ++ tailWord_119897).sum := by decide
  have hdescent : baseEnd_119897 < baseStart_119897 := by decide
  rcases family_descends (prefixWord ++ tailWord_119897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119917 : List Nat := [1, 5, 1, 1, 2, 3, 1, 4, 2]
def baseStart_119917 : Nat := 118140960795 + 119917 * 2 ^ 59
def prefixEnd_119917 : Nat := 4983230072969 + 3 ^ 40 * 119917 * 2
def baseEnd_119917 : Nat := 54733386351388940343127

theorem tailTrace_119917 : CollatzResearch.WordTrace tailWord_119917 prefixEnd_119917 54733386351388940343127 := by
  unfold tailWord_119917
  simp only [CollatzResearch.WordTrace]
  refine ⟨4373732306568664038198005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2915821537712442692132003 4373732306568664038198005)
  ·
    refine ⟨410037403740812253581063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4373732306568664038198005 410037403740812253581063)
    ·
      refine ⟨615056105611218380371595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410037403740812253581063 615056105611218380371595)
      ·
        refine ⟨922584158416827570557393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615056105611218380371595 922584158416827570557393)
        ·
          refine ⟨691938118812620677918045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 922584158416827570557393 691938118812620677918045)
          ·
            refine ⟨259476794554732754219267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 691938118812620677918045 259476794554732754219267)
            ·
              refine ⟨389215191832099131328901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259476794554732754219267 389215191832099131328901)
              ·
                refine ⟨72977848468518587124169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 389215191832099131328901 72977848468518587124169)
                ·
                  refine ⟨54733386351388940343127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72977848468518587124169 54733386351388940343127)
                  ·
                    rfl

theorem cell20_119917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_119917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119917 prefixEnd_119917 := by exact prefixLift 119917
  have htrace : WordTrace (prefixWord ++ tailWord_119917) baseStart_119917 baseEnd_119917 := by
    simpa [prefixWord, tailWord_119917, baseEnd_119917] using wordTrace_append hprefix tailTrace_119917
  have hstable : (prefixWord ++ tailWord_119917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119917).length < 2 ^ (prefixWord ++ tailWord_119917).sum := by decide
  have hdescent : baseEnd_119917 < baseStart_119917 := by decide
  rcases family_descends (prefixWord ++ tailWord_119917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119928 : List Nat := [2, 1, 2, 1, 1, 1, 7, 5]
def baseStart_119928 : Nat := 118140960795 + 119928 * 2 ^ 59
def prefixEnd_119928 : Nat := 4983230072969 + 3 ^ 40 * 119928 * 2
def baseEnd_119928 : Nat := 18246135683707263658805

theorem tailTrace_119928 : CollatzResearch.WordTrace tailWord_119928 prefixEnd_119928 18246135683707263658805 := by
  unfold tailWord_119928
  simp only [CollatzResearch.WordTrace]
  refine ⟨2187066754764406458424219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2916089006352541944565625 2187066754764406458424219)
  ·
    refine ⟨3280600132146609687636329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2187066754764406458424219 3280600132146609687636329)
    ·
      refine ⟨2460450099109957265727247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3280600132146609687636329 2460450099109957265727247)
      ·
        refine ⟨3690675148664935898590871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2460450099109957265727247 3690675148664935898590871)
        ·
          refine ⟨5536012722997403847886307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3690675148664935898590871 5536012722997403847886307)
          ·
            refine ⟨8304019084496105771829461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5536012722997403847886307 8304019084496105771829461)
            ·
              refine ⟨194625447292877479027253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 8304019084496105771829461 194625447292877479027253)
              ·
                refine ⟨18246135683707263658805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194625447292877479027253 18246135683707263658805)
                ·
                  rfl

theorem cell20_119928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_119928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119928 prefixEnd_119928 := by exact prefixLift 119928
  have htrace : WordTrace (prefixWord ++ tailWord_119928) baseStart_119928 baseEnd_119928 := by
    simpa [prefixWord, tailWord_119928, baseEnd_119928] using wordTrace_append hprefix tailTrace_119928
  have hstable : (prefixWord ++ tailWord_119928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119928).length < 2 ^ (prefixWord ++ tailWord_119928).sum := by decide
  have hdescent : baseEnd_119928 < baseStart_119928 := by decide
  rcases family_descends (prefixWord ++ tailWord_119928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119945 : List Nat := [1, 2, 1, 1, 4, 4, 3, 4]
def baseStart_119945 : Nat := 118140960795 + 119945 * 2 ^ 59
def prefixEnd_119945 : Nat := 4983230072969 + 3 ^ 40 * 119945 * 2
def baseEnd_119945 : Nat := 18248722104781762469893

theorem tailTrace_119945 : CollatzResearch.WordTrace tailWord_119945 prefixEnd_119945 18248722104781762469893 := by
  unfold tailWord_119945
  simp only [CollatzResearch.WordTrace]
  refine ⟨4374753550467224820217289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2916502366978149880144859 4374753550467224820217289)
  ·
    refine ⟨3281065162850418615162967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4374753550467224820217289 3281065162850418615162967)
    ·
      refine ⟨4921597744275627922744451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3281065162850418615162967 4921597744275627922744451)
      ·
        refine ⟨7382396616413441884116677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4921597744275627922744451 7382396616413441884116677)
        ·
          refine ⟨1384199365577520353271877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7382396616413441884116677 1384199365577520353271877)
          ·
            refine ⟨259537381045785066238477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1384199365577520353271877 259537381045785066238477)
            ·
              refine ⟨97326517892169399839429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259537381045785066238477 97326517892169399839429)
              ·
                refine ⟨18248722104781762469893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97326517892169399839429 18248722104781762469893)
                ·
                  rfl

theorem cell20_119945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 4].length) (baseStart_119945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119945 prefixEnd_119945 := by exact prefixLift 119945
  have htrace : WordTrace (prefixWord ++ tailWord_119945) baseStart_119945 baseEnd_119945 := by
    simpa [prefixWord, tailWord_119945, baseEnd_119945] using wordTrace_append hprefix tailTrace_119945
  have hstable : (prefixWord ++ tailWord_119945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119945).length < 2 ^ (prefixWord ++ tailWord_119945).sum := by decide
  have hdescent : baseEnd_119945 < baseStart_119945 := by decide
  rcases family_descends (prefixWord ++ tailWord_119945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119997 : List Nat := [1, 4, 1, 2, 1, 1, 4, 2, 4]
def baseStart_119997 : Nat := 118140960795 + 119997 * 2 ^ 59
def prefixEnd_119997 : Nat := 4983230072969 + 3 ^ 40 * 119997 * 2
def baseEnd_119997 : Nat := 54769900531264217676133

theorem tailTrace_119997 : CollatzResearch.WordTrace tailWord_119997 prefixEnd_119997 54769900531264217676133 := by
  unfold tailWord_119997
  simp only [CollatzResearch.WordTrace]
  refine ⟨4376650146278837701110245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2917766764185891800740163 4376650146278837701110245)
  ·
    refine ⟨820621902427282068958171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4376650146278837701110245 820621902427282068958171)
    ·
      refine ⟨1230932853640923103437257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 820621902427282068958171 1230932853640923103437257)
      ·
        refine ⟨923199640230692327577943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1230932853640923103437257 923199640230692327577943)
        ·
          refine ⟨1384799460346038491366915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923199640230692327577943 1384799460346038491366915)
          ·
            refine ⟨2077199190519057737050373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1384799460346038491366915 2077199190519057737050373)
            ·
              refine ⟨389474848222323325696945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2077199190519057737050373 389474848222323325696945)
              ·
                refine ⟨292106136166742494272709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389474848222323325696945 292106136166742494272709)
                ·
                  refine ⟨54769900531264217676133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 292106136166742494272709 54769900531264217676133)
                  ·
                    rfl

theorem cell20_119997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_119997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_119997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_119997 prefixEnd_119997 := by exact prefixLift 119997
  have htrace : WordTrace (prefixWord ++ tailWord_119997) baseStart_119997 baseEnd_119997 := by
    simpa [prefixWord, tailWord_119997, baseEnd_119997] using wordTrace_append hprefix tailTrace_119997
  have hstable : (prefixWord ++ tailWord_119997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119997).length < 2 ^ (prefixWord ++ tailWord_119997).sum := by decide
  have hdescent : baseEnd_119997 < baseStart_119997 := by decide
  rcases family_descends (prefixWord ++ tailWord_119997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120000 : List Nat := [2, 1, 1, 2, 6, 2, 2, 4]
def baseStart_120000 : Nat := 118140960795 + 120000 * 2 ^ 59
def prefixEnd_120000 : Nat := 4983230072969 + 3 ^ 40 * 120000 * 2
def baseEnd_120000 : Nat := 18257089937669846858707

theorem tailTrace_120000 : CollatzResearch.WordTrace tailWord_120000 prefixEnd_120000 18257089937669846858707 := by
  unfold tailWord_120000
  simp only [CollatzResearch.WordTrace]
  refine ⟨2188379782633984606734727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2917839710178646142312969 2188379782633984606734727)
  ·
    refine ⟨3282569673950976910102091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2188379782633984606734727 3282569673950976910102091)
    ·
      refine ⟨4923854510926465365153137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3282569673950976910102091 4923854510926465365153137)
      ·
        refine ⟨3692890883194849023864853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4923854510926465365153137 3692890883194849023864853)
        ·
          refine ⟨173104260149758547993665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3692890883194849023864853 173104260149758547993665)
          ·
            refine ⟨129828195112318910995249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173104260149758547993665 129828195112318910995249)
            ·
              refine ⟨97371146334239183246437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129828195112318910995249 97371146334239183246437)
              ·
                refine ⟨18257089937669846858707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97371146334239183246437 18257089937669846858707)
                ·
                  rfl

theorem cell20_120000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 4].length) (baseStart_120000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120000 prefixEnd_120000 := by exact prefixLift 120000
  have htrace : WordTrace (prefixWord ++ tailWord_120000) baseStart_120000 baseEnd_120000 := by
    simpa [prefixWord, tailWord_120000, baseEnd_120000] using wordTrace_append hprefix tailTrace_120000
  have hstable : (prefixWord ++ tailWord_120000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120000).length < 2 ^ (prefixWord ++ tailWord_120000).sum := by decide
  have hdescent : baseEnd_120000 < baseStart_120000 := by decide
  rcases family_descends (prefixWord ++ tailWord_120000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120021 : List Nat := [1, 3, 2, 4, 1, 3, 6]
def baseStart_120021 : Nat := 118140960795 + 120021 * 2 ^ 59
def prefixEnd_120021 : Nat := 4983230072969 + 3 ^ 40 * 120021 * 2
def baseEnd_120021 : Nat := 6086761642802977875115

theorem tailTrace_120021 : CollatzResearch.WordTrace tailWord_120021 prefixEnd_120021 6086761642802977875115 := by
  unfold tailWord_120021
  simp only [CollatzResearch.WordTrace]
  refine ⟨4377525498191889799983917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2918350332127926533322611 4377525498191889799983917)
  ·
    refine ⟨1641572061821958674993969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4377525498191889799983917 1641572061821958674993969)
    ·
      refine ⟨1231179046366469006245477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1641572061821958674993969 1231179046366469006245477)
      ·
        refine ⟨230846071193712938671027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1231179046366469006245477 230846071193712938671027)
        ·
          refine ⟨346269106790569408006541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230846071193712938671027 346269106790569408006541)
          ·
            refine ⟨129850915046463528002453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346269106790569408006541 129850915046463528002453)
            ·
              refine ⟨6086761642802977875115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129850915046463528002453 6086761642802977875115)
              ·
                rfl

theorem cell20_120021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 6].length) (baseStart_120021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120021 prefixEnd_120021 := by exact prefixLift 120021
  have htrace : WordTrace (prefixWord ++ tailWord_120021) baseStart_120021 baseEnd_120021 := by
    simpa [prefixWord, tailWord_120021, baseEnd_120021] using wordTrace_append hprefix tailTrace_120021
  have hstable : (prefixWord ++ tailWord_120021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120021).length < 2 ^ (prefixWord ++ tailWord_120021).sum := by decide
  have hdescent : baseEnd_120021 < baseStart_120021 := by decide
  rcases family_descends (prefixWord ++ tailWord_120021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120042 : List Nat := [3, 1, 3, 1, 1, 3, 1, 7]
def baseStart_120042 : Nat := 118140960795 + 120042 * 2 ^ 59
def prefixEnd_120042 : Nat := 4983230072969 + 3 ^ 40 * 120042 * 2
def baseEnd_120042 : Nat := 18263479919148020391983

theorem tailTrace_120042 : CollatzResearch.WordTrace tailWord_120042 prefixEnd_120042 18263479919148020391983 := by
  unfold tailWord_120042
  simp only [CollatzResearch.WordTrace]
  refine ⟨1094572857778952596624595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2918860954077206924332253 1094572857778952596624595)
  ·
    refine ⟨1641859286668428894936893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1094572857778952596624595 1641859286668428894936893)
    ·
      refine ⟨615697232500660835601335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1641859286668428894936893 615697232500660835601335)
      ·
        refine ⟨923545848750991253402003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615697232500660835601335 923545848750991253402003)
        ·
          refine ⟨1385318773126486880103005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923545848750991253402003 1385318773126486880103005)
          ·
            refine ⟨519494539922432580038627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1385318773126486880103005 519494539922432580038627)
            ·
              refine ⟨779241809883648870057941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519494539922432580038627 779241809883648870057941)
              ·
                refine ⟨18263479919148020391983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 779241809883648870057941 18263479919148020391983)
                ·
                  rfl

theorem cell20_120042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_120042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120042 prefixEnd_120042 := by exact prefixLift 120042
  have htrace : WordTrace (prefixWord ++ tailWord_120042) baseStart_120042 baseEnd_120042 := by
    simpa [prefixWord, tailWord_120042, baseEnd_120042] using wordTrace_append hprefix tailTrace_120042
  have hstable : (prefixWord ++ tailWord_120042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120042).length < 2 ^ (prefixWord ++ tailWord_120042).sum := by decide
  have hdescent : baseEnd_120042 < baseStart_120042 := by decide
  rcases family_descends (prefixWord ++ tailWord_120042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120045 : List Nat := [1, 5, 1, 2, 2, 2, 1, 3, 3]
def baseStart_120045 : Nat := 118140960795 + 120045 * 2 ^ 59
def prefixEnd_120045 : Nat := 4983230072969 + 3 ^ 40 * 120045 * 2
def baseEnd_120045 : Nat := 54791809039189384075937

theorem tailTrace_120045 : CollatzResearch.WordTrace tailWord_120045 prefixEnd_120045 54791809039189384075937 := by
  unfold tailWord_120045
  simp only [CollatzResearch.WordTrace]
  refine ⟨4378400850104941898857589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2918933900069961265905059 4378400850104941898857589)
  ·
    refine ⟨410475079697338303017899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4378400850104941898857589 410475079697338303017899)
    ·
      refine ⟨615712619546007454526849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410475079697338303017899 615712619546007454526849)
      ·
        refine ⟨461784464659505590895137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 615712619546007454526849 461784464659505590895137)
        ·
          refine ⟨346338348494629193171353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461784464659505590895137 346338348494629193171353)
          ·
            refine ⟨259753761370971894878515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346338348494629193171353 259753761370971894878515)
            ·
              refine ⟨389630642056457842317773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259753761370971894878515 389630642056457842317773)
              ·
                refine ⟨146111490771171690869165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 389630642056457842317773 146111490771171690869165)
                ·
                  refine ⟨54791809039189384075937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146111490771171690869165 54791809039189384075937)
                  ·
                    rfl

theorem cell20_120045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_120045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120045 prefixEnd_120045 := by exact prefixLift 120045
  have htrace : WordTrace (prefixWord ++ tailWord_120045) baseStart_120045 baseEnd_120045 := by
    simpa [prefixWord, tailWord_120045, baseEnd_120045] using wordTrace_append hprefix tailTrace_120045
  have hstable : (prefixWord ++ tailWord_120045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120045).length < 2 ^ (prefixWord ++ tailWord_120045).sum := by decide
  have hdescent : baseEnd_120045 < baseStart_120045 := by decide
  rcases family_descends (prefixWord ++ tailWord_120045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120082 : List Nat := [3, 2, 4, 2, 1, 2, 2, 2, 2]
def baseStart_120082 : Nat := 118140960795 + 120082 * 2 ^ 59
def prefixEnd_120082 : Nat := 4983230072969 + 3 ^ 40 * 120082 * 2
def baseEnd_120082 : Nat := 54808696847381699842453

theorem tailTrace_120082 : CollatzResearch.WordTrace tailWord_120082 prefixEnd_120082 54808696847381699842453 := by
  unfold tailWord_120082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1094937587742724304488625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2919833567313931478636333 1094937587742724304488625)
  ·
    refine ⟨821203190807043228366469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1094937587742724304488625 821203190807043228366469)
    ·
      refine ⟨153975598276320605318713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 821203190807043228366469 153975598276320605318713)
      ·
        refine ⟨115481698707240453989035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153975598276320605318713 115481698707240453989035)
        ·
          refine ⟨173222548060860680983553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115481698707240453989035 173222548060860680983553)
          ·
            refine ⟨129916911045645510737665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173222548060860680983553 129916911045645510737665)
            ·
              refine ⟨97437683284234133053249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129916911045645510737665 97437683284234133053249)
              ·
                refine ⟨73078262463175599789937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97437683284234133053249 73078262463175599789937)
                ·
                  refine ⟨54808696847381699842453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73078262463175599789937 54808696847381699842453)
                  ·
                    rfl

theorem cell20_120082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_120082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120082 prefixEnd_120082 := by exact prefixLift 120082
  have htrace : WordTrace (prefixWord ++ tailWord_120082) baseStart_120082 baseEnd_120082 := by
    simpa [prefixWord, tailWord_120082, baseEnd_120082] using wordTrace_append hprefix tailTrace_120082
  have hstable : (prefixWord ++ tailWord_120082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120082).length < 2 ^ (prefixWord ++ tailWord_120082).sum := by decide
  have hdescent : baseEnd_120082 < baseStart_120082 := by decide
  rcases family_descends (prefixWord ++ tailWord_120082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120128 : List Nat := [2, 1, 1, 2, 2, 1, 6, 3, 2]
def baseStart_120128 : Nat := 118140960795 + 120128 * 2 ^ 59
def prefixEnd_120128 : Nat := 4983230072969 + 3 ^ 40 * 120128 * 2
def baseEnd_120128 : Nat := 54829692500809984308931

theorem tailTrace_120128 : CollatzResearch.WordTrace tailWord_120128 prefixEnd_120128 54829692500809984308931 := by
  unfold tailWord_120128
  simp only [CollatzResearch.WordTrace]
  refine ⟨2190714054402123537064519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2920952072536164716086025 2190714054402123537064519)
  ·
    refine ⟨3286071081603185305596779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2190714054402123537064519 3286071081603185305596779)
    ·
      refine ⟨4929106622404777958395169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3286071081603185305596779 4929106622404777958395169)
      ·
        refine ⟨3696829966803583468796377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4929106622404777958395169 3696829966803583468796377)
        ·
          refine ⟨2772622475102687601597283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3696829966803583468796377 2772622475102687601597283)
          ·
            refine ⟨4158933712654031402395925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2772622475102687601597283 4158933712654031402395925)
            ·
              refine ⟨194950017780657721987309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4158933712654031402395925 194950017780657721987309)
              ·
                refine ⟨73106256667746645745241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194950017780657721987309 73106256667746645745241)
                ·
                  refine ⟨54829692500809984308931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73106256667746645745241 54829692500809984308931)
                  ·
                    rfl

theorem cell20_120128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 2].length) (baseStart_120128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120128 prefixEnd_120128 := by exact prefixLift 120128
  have htrace : WordTrace (prefixWord ++ tailWord_120128) baseStart_120128 baseEnd_120128 := by
    simpa [prefixWord, tailWord_120128, baseEnd_120128] using wordTrace_append hprefix tailTrace_120128
  have hstable : (prefixWord ++ tailWord_120128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120128).length < 2 ^ (prefixWord ++ tailWord_120128).sum := by decide
  have hdescent : baseEnd_120128 < baseStart_120128 := by decide
  rcases family_descends (prefixWord ++ tailWord_120128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120134 : List Nat := [6, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_120134 : Nat := 118140960795 + 120134 * 2 ^ 59
def prefixEnd_120134 : Nat := 4983230072969 + 3 ^ 40 * 120134 * 2
def baseEnd_120134 : Nat := 54832431064300630108907

theorem tailTrace_120134 : CollatzResearch.WordTrace tailWord_120134 prefixEnd_120134 54832431064300630108907 := by
  unfold tailWord_120134
  simp only [CollatzResearch.WordTrace]
  refine ⟨136926467086953440588983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2921097964521673399231637 136926467086953440588983)
  ·
    refine ⟨205389700630430160883475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136926467086953440588983 205389700630430160883475)
    ·
      refine ⟨308084550945645241325213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205389700630430160883475 308084550945645241325213)
      ·
        refine ⟨115531706604616965496955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308084550945645241325213 115531706604616965496955)
        ·
          refine ⟨173297559906925448245433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115531706604616965496955 173297559906925448245433)
          ·
            refine ⟨129973169930194086184075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173297559906925448245433 129973169930194086184075)
            ·
              refine ⟨194959754895291129276113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129973169930194086184075 194959754895291129276113)
              ·
                refine ⟨146219816171468346957085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194959754895291129276113 146219816171468346957085)
                ·
                  refine ⟨54832431064300630108907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146219816171468346957085 54832431064300630108907)
                  ·
                    rfl

theorem cell20_120134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_120134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120134 prefixEnd_120134 := by exact prefixLift 120134
  have htrace : WordTrace (prefixWord ++ tailWord_120134) baseStart_120134 baseEnd_120134 := by
    simpa [prefixWord, tailWord_120134, baseEnd_120134] using wordTrace_append hprefix tailTrace_120134
  have hstable : (prefixWord ++ tailWord_120134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120134).length < 2 ^ (prefixWord ++ tailWord_120134).sum := by decide
  have hdescent : baseEnd_120134 < baseStart_120134 := by decide
  rcases family_descends (prefixWord ++ tailWord_120134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120149 : List Nat := [1, 3, 2, 2, 3, 1, 1, 3, 4]
def baseStart_120149 : Nat := 118140960795 + 120149 * 2 ^ 59
def prefixEnd_120149 : Nat := 4983230072969 + 3 ^ 40 * 120149 * 2
def baseEnd_120149 : Nat := 54839277473027244608845

theorem tailTrace_120149 : CollatzResearch.WordTrace tailWord_120149 prefixEnd_120149 54839277473027244608845 := by
  unfold tailWord_120149
  simp only [CollatzResearch.WordTrace]
  refine ⟨4382194041728167660643501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2921462694485445107095667 4382194041728167660643501)
  ·
    refine ⟨1643322765648062872741313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4382194041728167660643501 1643322765648062872741313)
    ·
      refine ⟨1232492074236047154555985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1643322765648062872741313 1232492074236047154555985)
      ·
        refine ⟨924369055677035365916989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1232492074236047154555985 924369055677035365916989)
        ·
          refine ⟨346638395878888262218871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 924369055677035365916989 346638395878888262218871)
          ·
            refine ⟨519957593818332393328307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346638395878888262218871 519957593818332393328307)
            ·
              refine ⟨779936390727498589992461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519957593818332393328307 779936390727498589992461)
              ·
                refine ⟨292476146522811971247173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 779936390727498589992461 292476146522811971247173)
                ·
                  refine ⟨54839277473027244608845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 292476146522811971247173 54839277473027244608845)
                  ·
                    rfl

theorem cell20_120149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_120149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120149 prefixEnd_120149 := by exact prefixLift 120149
  have htrace : WordTrace (prefixWord ++ tailWord_120149) baseStart_120149 baseEnd_120149 := by
    simpa [prefixWord, tailWord_120149, baseEnd_120149] using wordTrace_append hprefix tailTrace_120149
  have hstable : (prefixWord ++ tailWord_120149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120149).length < 2 ^ (prefixWord ++ tailWord_120149).sum := by decide
  have hdescent : baseEnd_120149 < baseStart_120149 := by decide
  rcases family_descends (prefixWord ++ tailWord_120149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120173 : List Nat := [1, 5, 1, 1, 1, 3, 4, 4]
def baseStart_120173 : Nat := 118140960795 + 120173 * 2 ^ 59
def prefixEnd_120173 : Nat := 4983230072969 + 3 ^ 40 * 120173 * 2
def baseEnd_120173 : Nat := 18283410575663275936249

theorem tailTrace_120173 : CollatzResearch.WordTrace tailWord_120173 prefixEnd_120173 18283410575663275936249 := by
  unfold tailWord_120173
  simp only [CollatzResearch.WordTrace]
  refine ⟨4383069393641219759517173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2922046262427479839678115 4383069393641219759517173)
  ·
    refine ⟨410912755653864352454735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4383069393641219759517173 410912755653864352454735)
    ·
      refine ⟨616369133480796528682103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410912755653864352454735 616369133480796528682103)
      ·
        refine ⟨924553700221194793023155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616369133480796528682103 924553700221194793023155)
        ·
          refine ⟨1386830550331792189534733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924553700221194793023155 1386830550331792189534733)
          ·
            refine ⟨520061456374422071075525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1386830550331792189534733 520061456374422071075525)
            ·
              refine ⟨97511523070204138326661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 520061456374422071075525 97511523070204138326661)
              ·
                refine ⟨18283410575663275936249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97511523070204138326661 18283410575663275936249)
                ·
                  rfl

theorem cell20_120173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 4].length) (baseStart_120173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120173 prefixEnd_120173 := by exact prefixLift 120173
  have htrace : WordTrace (prefixWord ++ tailWord_120173) baseStart_120173 baseEnd_120173 := by
    simpa [prefixWord, tailWord_120173, baseEnd_120173] using wordTrace_append hprefix tailTrace_120173
  have hstable : (prefixWord ++ tailWord_120173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120173).length < 2 ^ (prefixWord ++ tailWord_120173).sum := by decide
  have hdescent : baseEnd_120173 < baseStart_120173 := by decide
  rcases family_descends (prefixWord ++ tailWord_120173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120210 : List Nat := [3, 2, 3, 3, 2, 1, 2, 1, 3]
def baseStart_120210 : Nat := 118140960795 + 120210 * 2 ^ 59
def prefixEnd_120210 : Nat := 4983230072969 + 3 ^ 40 * 120210 * 2
def baseEnd_120210 : Nat := 54867119535182143575263

theorem tailTrace_120210 : CollatzResearch.WordTrace tailWord_120210 prefixEnd_120210 54867119535182143575263 := by
  unfold tailWord_120210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1096104723626793769653521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2922945929671450052409389 1096104723626793769653521)
  ·
    refine ⟨822078542720095327240141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1096104723626793769653521 822078542720095327240141)
    ·
      refine ⟨308279453520035747715053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 822078542720095327240141 308279453520035747715053)
      ·
        refine ⟨115604795070013405393145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308279453520035747715053 115604795070013405393145)
        ·
          refine ⟨86703596302510054044859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115604795070013405393145 86703596302510054044859)
          ·
            refine ⟨130055394453765081067289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86703596302510054044859 130055394453765081067289)
            ·
              refine ⟨97541545840323810800467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130055394453765081067289 97541545840323810800467)
              ·
                refine ⟨146312318760485716200701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97541545840323810800467 146312318760485716200701)
                ·
                  refine ⟨54867119535182143575263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146312318760485716200701 54867119535182143575263)
                  ·
                    rfl

theorem cell20_120210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_120210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120210 prefixEnd_120210 := by exact prefixLift 120210
  have htrace : WordTrace (prefixWord ++ tailWord_120210) baseStart_120210 baseEnd_120210 := by
    simpa [prefixWord, tailWord_120210, baseEnd_120210] using wordTrace_append hprefix tailTrace_120210
  have hstable : (prefixWord ++ tailWord_120210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120210).length < 2 ^ (prefixWord ++ tailWord_120210).sum := by decide
  have hdescent : baseEnd_120210 < baseStart_120210 := by decide
  rcases family_descends (prefixWord ++ tailWord_120210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120218 : List Nat := [3, 1, 1, 4, 1, 1, 3, 3, 3]
def baseStart_120218 : Nat := 118140960795 + 120218 * 2 ^ 59
def prefixEnd_120218 : Nat := 4983230072969 + 3 ^ 40 * 120218 * 2
def baseEnd_120218 : Nat := 54870770953169671308563

theorem tailTrace_120218 : CollatzResearch.WordTrace tailWord_120218 prefixEnd_120218 54870770953169671308563 := by
  unfold tailWord_120218
  simp only [CollatzResearch.WordTrace]
  refine ⟨1096177669619548111226327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2923140452318794963270205 1096177669619548111226327)
  ·
    refine ⟨1644266504429322166839491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1096177669619548111226327 1644266504429322166839491)
    ·
      refine ⟨2466399756643983250259237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1644266504429322166839491 2466399756643983250259237)
      ·
        refine ⟨462449954370746859423607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2466399756643983250259237 462449954370746859423607)
        ·
          refine ⟨693674931556120289135411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462449954370746859423607 693674931556120289135411)
          ·
            refine ⟨1040512397334180433703117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693674931556120289135411 1040512397334180433703117)
            ·
              refine ⟨390192149000317662638669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1040512397334180433703117 390192149000317662638669)
              ·
                refine ⟨146322055875119123489501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 390192149000317662638669 146322055875119123489501)
                ·
                  refine ⟨54870770953169671308563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146322055875119123489501 54870770953169671308563)
                  ·
                    rfl

theorem cell20_120218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_120218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120218 prefixEnd_120218 := by exact prefixLift 120218
  have htrace : WordTrace (prefixWord ++ tailWord_120218) baseStart_120218 baseEnd_120218 := by
    simpa [prefixWord, tailWord_120218, baseEnd_120218] using wordTrace_append hprefix tailTrace_120218
  have hstable : (prefixWord ++ tailWord_120218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120218).length < 2 ^ (prefixWord ++ tailWord_120218).sum := by decide
  have hdescent : baseEnd_120218 < baseStart_120218 := by decide
  rcases family_descends (prefixWord ++ tailWord_120218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120270 : List Nat := [4, 1, 1, 1, 2, 1, 5, 5]
def baseStart_120270 : Nat := 118140960795 + 120270 * 2 ^ 59
def prefixEnd_120270 : Nat := 4983230072969 + 3 ^ 40 * 120270 * 2
def baseEnd_120270 : Nat := 18298168390029533858339

theorem tailTrace_120270 : CollatzResearch.WordTrace tailWord_120270 prefixEnd_120270 18298168390029533858339 := by
  unfold tailWord_120270
  simp only [CollatzResearch.WordTrace]
  refine ⟨548325909286225665724783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2924404849526536883865509 548325909286225665724783)
  ·
    refine ⟨822488863929338498587175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 548325909286225665724783 822488863929338498587175)
    ·
      refine ⟨1233733295894007747880763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 822488863929338498587175 1233733295894007747880763)
      ·
        refine ⟨1850599943841011621821145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1233733295894007747880763 1850599943841011621821145)
        ·
          refine ⟨1387949957880758716365859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1850599943841011621821145 1387949957880758716365859)
          ·
            refine ⟨2081924936821138074548789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1387949957880758716365859 2081924936821138074548789)
            ·
              refine ⟨195180462826981694488949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2081924936821138074548789 195180462826981694488949)
              ·
                refine ⟨18298168390029533858339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 195180462826981694488949 18298168390029533858339)
                ·
                  rfl

theorem cell20_120270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_120270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120270 prefixEnd_120270 := by exact prefixLift 120270
  have htrace : WordTrace (prefixWord ++ tailWord_120270) baseStart_120270 baseEnd_120270 := by
    simpa [prefixWord, tailWord_120270, baseEnd_120270] using wordTrace_append hprefix tailTrace_120270
  have hstable : (prefixWord ++ tailWord_120270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120270).length < 2 ^ (prefixWord ++ tailWord_120270).sum := by decide
  have hdescent : baseEnd_120270 < baseStart_120270 := by decide
  rcases family_descends (prefixWord ++ tailWord_120270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120329 : List Nat := [1, 2, 1, 1, 3, 1, 4, 7]
def baseStart_120329 : Nat := 118140960795 + 120329 * 2 ^ 59
def prefixEnd_120329 : Nat := 4983230072969 + 3 ^ 40 * 120329 * 2
def baseEnd_120329 : Nat := 18307144792582206202703

theorem tailTrace_120329 : CollatzResearch.WordTrace tailWord_120329 prefixEnd_120329 18307144792582206202703 := by
  unfold tailWord_120329
  simp only [CollatzResearch.WordTrace]
  refine ⟨4388759181076058402196041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2925839454050705601464027 4388759181076058402196041)
  ·
    refine ⟨3291569385807043801647031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4388759181076058402196041 3291569385807043801647031)
    ·
      refine ⟨4937354078710565702470547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3291569385807043801647031 4937354078710565702470547)
      ·
        refine ⟨7406031118065848553705821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4937354078710565702470547 7406031118065848553705821)
        ·
          refine ⟨2777261669274693207639683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7406031118065848553705821 2777261669274693207639683)
          ·
            refine ⟨4165892503912039811459525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2777261669274693207639683 4165892503912039811459525)
            ·
              refine ⟨781104844483507464648661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4165892503912039811459525 781104844483507464648661)
              ·
                refine ⟨18307144792582206202703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 781104844483507464648661 18307144792582206202703)
                ·
                  rfl

theorem cell20_120329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 7].length) (baseStart_120329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120329 prefixEnd_120329 := by exact prefixLift 120329
  have htrace : WordTrace (prefixWord ++ tailWord_120329) baseStart_120329 baseEnd_120329 := by
    simpa [prefixWord, tailWord_120329, baseEnd_120329] using wordTrace_append hprefix tailTrace_120329
  have hstable : (prefixWord ++ tailWord_120329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120329).length < 2 ^ (prefixWord ++ tailWord_120329).sum := by decide
  have hdescent : baseEnd_120329 < baseStart_120329 := by decide
  rcases family_descends (prefixWord ++ tailWord_120329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120353 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 5]
def baseStart_120353 : Nat := 118140960795 + 120353 * 2 ^ 59
def prefixEnd_120353 : Nat := 4983230072969 + 3 ^ 40 * 120353 * 2
def baseEnd_120353 : Nat := 54932388631709201808011

theorem tailTrace_120353 : CollatzResearch.WordTrace tailWord_120353 prefixEnd_120353 54932388631709201808011 := by
  unfold tailWord_120353
  simp only [CollatzResearch.WordTrace]
  refine ⟨4389634532989110501069713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2926423021992740334046475 4389634532989110501069713)
  ·
    refine ⟨3292225899741832875802285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4389634532989110501069713 3292225899741832875802285)
    ·
      refine ⟨1234584712403187328425857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3292225899741832875802285 1234584712403187328425857)
      ·
        refine ⟨925938534302390496319393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1234584712403187328425857 925938534302390496319393)
        ·
          refine ⟨694453900726792872239545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 925938534302390496319393 694453900726792872239545)
          ·
            refine ⟨520840425545094654179659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 694453900726792872239545 520840425545094654179659)
            ·
              refine ⟨781260638317641981269489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520840425545094654179659 781260638317641981269489)
              ·
                refine ⟨585945478738231485952117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 781260638317641981269489 585945478738231485952117)
                ·
                  refine ⟨54932388631709201808011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 585945478738231485952117 54932388631709201808011)
                  ·
                    rfl

theorem cell20_120353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_120353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120353 prefixEnd_120353 := by exact prefixLift 120353
  have htrace : WordTrace (prefixWord ++ tailWord_120353) baseStart_120353 baseEnd_120353 := by
    simpa [prefixWord, tailWord_120353, baseEnd_120353] using wordTrace_append hprefix tailTrace_120353
  have hstable : (prefixWord ++ tailWord_120353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120353).length < 2 ^ (prefixWord ++ tailWord_120353).sum := by decide
  have hdescent : baseEnd_120353 < baseStart_120353 := by decide
  rcases family_descends (prefixWord ++ tailWord_120353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120373 : List Nat := [1, 3, 3, 1, 1, 4, 3, 2, 2]
def baseStart_120373 : Nat := 118140960795 + 120373 * 2 ^ 59
def prefixEnd_120373 : Nat := 4983230072969 + 3 ^ 40 * 120373 * 2
def baseEnd_120373 : Nat := 54941517176678021141263

theorem tailTrace_120373 : CollatzResearch.WordTrace tailWord_120373 prefixEnd_120373 54941517176678021141263 := by
  unfold tailWord_120373
  simp only [CollatzResearch.WordTrace]
  refine ⟨4390363992916653916797773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2926909328611102611198515 4390363992916653916797773)
  ·
    refine ⟨1646386497343745218799165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4390363992916653916797773 1646386497343745218799165)
    ·
      refine ⟨617394936503904457049687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1646386497343745218799165 617394936503904457049687)
      ·
        refine ⟨926092404755856685574531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617394936503904457049687 926092404755856685574531)
        ·
          refine ⟨1389138607133785028361797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926092404755856685574531 1389138607133785028361797)
          ·
            refine ⟨260463488837584692817837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1389138607133785028361797 260463488837584692817837)
            ·
              refine ⟨97673808314094259806689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260463488837584692817837 97673808314094259806689)
              ·
                refine ⟨73255356235570694855017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97673808314094259806689 73255356235570694855017)
                ·
                  refine ⟨54941517176678021141263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73255356235570694855017 54941517176678021141263)
                  ·
                    rfl

theorem cell20_120373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_120373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120373 prefixEnd_120373 := by exact prefixLift 120373
  have htrace : WordTrace (prefixWord ++ tailWord_120373) baseStart_120373 baseEnd_120373 := by
    simpa [prefixWord, tailWord_120373, baseEnd_120373] using wordTrace_append hprefix tailTrace_120373
  have hstable : (prefixWord ++ tailWord_120373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120373).length < 2 ^ (prefixWord ++ tailWord_120373).sum := by decide
  have hdescent : baseEnd_120373 < baseStart_120373 := by decide
  rcases family_descends (prefixWord ++ tailWord_120373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120377 : List Nat := [1, 2, 1, 5, 1, 2, 3, 1, 4]
def baseStart_120377 : Nat := 118140960795 + 120377 * 2 ^ 59
def prefixEnd_120377 : Nat := 4983230072969 + 3 ^ 40 * 120377 * 2
def baseEnd_120377 : Nat := 54943342885671785007913

theorem tailTrace_120377 : CollatzResearch.WordTrace tailWord_120377 prefixEnd_120377 54943342885671785007913 := by
  unfold tailWord_120377
  simp only [CollatzResearch.WordTrace]
  refine ⟨4390509884902162599943385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2927006589934775066628923 4390509884902162599943385)
  ·
    refine ⟨3292882413676621949957539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4390509884902162599943385 3292882413676621949957539)
    ·
      refine ⟨4939323620514932924936309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3292882413676621949957539 4939323620514932924936309)
      ·
        refine ⟨463061589423274961712779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4939323620514932924936309 463061589423274961712779)
        ·
          refine ⟨694592384134912442569169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463061589423274961712779 694592384134912442569169)
          ·
            refine ⟨520944288101184331926877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 694592384134912442569169 520944288101184331926877)
            ·
              refine ⟨195354108037944124472579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 520944288101184331926877 195354108037944124472579)
              ·
                refine ⟨293031162056916186708869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195354108037944124472579 293031162056916186708869)
                ·
                  refine ⟨54943342885671785007913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 293031162056916186708869 54943342885671785007913)
                  ·
                    rfl

theorem cell20_120377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_120377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120377 prefixEnd_120377 := by exact prefixLift 120377
  have htrace : WordTrace (prefixWord ++ tailWord_120377) baseStart_120377 baseEnd_120377 := by
    simpa [prefixWord, tailWord_120377, baseEnd_120377] using wordTrace_append hprefix tailTrace_120377
  have hstable : (prefixWord ++ tailWord_120377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120377).length < 2 ^ (prefixWord ++ tailWord_120377).sum := by decide
  have hdescent : baseEnd_120377 < baseStart_120377 := by decide
  rcases family_descends (prefixWord ++ tailWord_120377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120398 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_120398 : Nat := 118140960795 + 120398 * 2 ^ 59
def prefixEnd_120398 : Nat := 4983230072969 + 3 ^ 40 * 120398 * 2
def baseEnd_120398 : Nat := 54952927857889045307827

theorem tailTrace_120398 : CollatzResearch.WordTrace tailWord_120398 prefixEnd_120398 54952927857889045307827 := by
  unfold tailWord_120398
  simp only [CollatzResearch.WordTrace]
  refine ⟨548909477228260398307231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2927517211884055457638565 548909477228260398307231)
  ·
    refine ⟨823364215842390597460847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 548909477228260398307231 823364215842390597460847)
    ·
      refine ⟨1235046323763585896191271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 823364215842390597460847 1235046323763585896191271)
      ·
        refine ⟨1852569485645378844286907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1235046323763585896191271 1852569485645378844286907)
        ·
          refine ⟨2778854228468068266430361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1852569485645378844286907 2778854228468068266430361)
          ·
            refine ⟨2084140671351051199822771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2778854228468068266430361 2084140671351051199822771)
            ·
              refine ⟨3126211007026576799734157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2084140671351051199822771 3126211007026576799734157)
              ·
                refine ⟨1172329127634966299900309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3126211007026576799734157 1172329127634966299900309)
                ·
                  refine ⟨54952927857889045307827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1172329127634966299900309 54952927857889045307827)
                  ·
                    rfl

theorem cell20_120398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_120398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120398 prefixEnd_120398 := by exact prefixLift 120398
  have htrace : WordTrace (prefixWord ++ tailWord_120398) baseStart_120398 baseEnd_120398 := by
    simpa [prefixWord, tailWord_120398, baseEnd_120398] using wordTrace_append hprefix tailTrace_120398
  have hstable : (prefixWord ++ tailWord_120398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120398).length < 2 ^ (prefixWord ++ tailWord_120398).sum := by decide
  have hdescent : baseEnd_120398 < baseStart_120398 := by decide
  rcases family_descends (prefixWord ++ tailWord_120398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120432 : List Nat := [2, 1, 1, 1, 6, 2, 1, 4, 2]
def baseStart_120432 : Nat := 118140960795 + 120432 * 2 ^ 59
def prefixEnd_120432 : Nat := 4983230072969 + 3 ^ 40 * 120432 * 2
def baseEnd_120432 : Nat := 54968446384336038174355

theorem tailTrace_120432 : CollatzResearch.WordTrace tailWord_120432 prefixEnd_120432 54968446384336038174355 := by
  unfold tailWord_120432
  simp only [CollatzResearch.WordTrace]
  refine ⟨2196257949851453496597775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2928343933135271328797033 2196257949851453496597775)
  ·
    refine ⟨3294386924777180244896663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2196257949851453496597775 3294386924777180244896663)
    ·
      refine ⟨4941580387165770367344995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3294386924777180244896663 4941580387165770367344995)
      ·
        refine ⟨7412370580748655551017493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4941580387165770367344995 7412370580748655551017493)
        ·
          refine ⟨347454870972593228953945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7412370580748655551017493 347454870972593228953945)
          ·
            refine ⟨260591153229444921715459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347454870972593228953945 260591153229444921715459)
            ·
              refine ⟨390886729844167382573189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260591153229444921715459 390886729844167382573189)
              ·
                refine ⟨73291261845781384232473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 390886729844167382573189 73291261845781384232473)
                ·
                  refine ⟨54968446384336038174355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73291261845781384232473 54968446384336038174355)
                  ·
                    rfl

theorem cell20_120432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 2].length) (baseStart_120432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120432 prefixEnd_120432 := by exact prefixLift 120432
  have htrace : WordTrace (prefixWord ++ tailWord_120432) baseStart_120432 baseEnd_120432 := by
    simpa [prefixWord, tailWord_120432, baseEnd_120432] using wordTrace_append hprefix tailTrace_120432
  have hstable : (prefixWord ++ tailWord_120432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120432).length < 2 ^ (prefixWord ++ tailWord_120432).sum := by decide
  have hdescent : baseEnd_120432 < baseStart_120432 := by decide
  rcases family_descends (prefixWord ++ tailWord_120432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120456 : List Nat := [2, 1, 3, 5, 1, 1, 3, 4]
def baseStart_120456 : Nat := 118140960795 + 120456 * 2 ^ 59
def prefixEnd_120456 : Nat := 4983230072969 + 3 ^ 40 * 120456 * 2
def baseEnd_120456 : Nat := 18326466879432873791419

theorem tailTrace_120456 : CollatzResearch.WordTrace tailWord_120456 prefixEnd_120456 18326466879432873791419 := by
  unfold tailWord_120456
  simp only [CollatzResearch.WordTrace]
  refine ⟨2196695625807979546034611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2928927501077306061379481 2196695625807979546034611)
  ·
    refine ⟨3295043438711969319051917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2196695625807979546034611 3295043438711969319051917)
    ·
      refine ⟨1235641289516988494644469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3295043438711969319051917 1235641289516988494644469)
      ·
        refine ⟨115841370892217671372919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1235641289516988494644469 115841370892217671372919)
        ·
          refine ⟨173762056338326507059379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115841370892217671372919 173762056338326507059379)
          ·
            refine ⟨260643084507489760589069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173762056338326507059379 260643084507489760589069)
            ·
              refine ⟨97741156690308660220901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260643084507489760589069 97741156690308660220901)
              ·
                refine ⟨18326466879432873791419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97741156690308660220901 18326466879432873791419)
                ·
                  rfl

theorem cell20_120456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 4].length) (baseStart_120456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120456 prefixEnd_120456 := by exact prefixLift 120456
  have htrace : WordTrace (prefixWord ++ tailWord_120456) baseStart_120456 baseEnd_120456 := by
    simpa [prefixWord, tailWord_120456, baseEnd_120456] using wordTrace_append hprefix tailTrace_120456
  have hstable : (prefixWord ++ tailWord_120456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120456).length < 2 ^ (prefixWord ++ tailWord_120456).sum := by decide
  have hdescent : baseEnd_120456 < baseStart_120456 := by decide
  rcases family_descends (prefixWord ++ tailWord_120456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120460 : List Nat := [2, 2, 1, 2, 1, 1, 7, 4]
def baseStart_120460 : Nat := 118140960795 + 120460 * 2 ^ 59
def prefixEnd_120460 : Nat := 4983230072969 + 3 ^ 40 * 120460 * 2
def baseEnd_120460 : Nat := 18327075449097461746969

theorem tailTrace_120460 : CollatzResearch.WordTrace tailWord_120460 prefixEnd_120460 18327075449097461746969 := by
  unfold tailWord_120460
  simp only [CollatzResearch.WordTrace]
  refine ⟨2196768571800733887607417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2929024762400978516809889 2196768571800733887607417)
  ·
    refine ⟨1647576428850550415705563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2196768571800733887607417 1647576428850550415705563)
    ·
      refine ⟨2471364643275825623558345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1647576428850550415705563 2471364643275825623558345)
      ·
        refine ⟨1853523482456869217668759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2471364643275825623558345 1853523482456869217668759)
        ·
          refine ⟨2780285223685303826503139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1853523482456869217668759 2780285223685303826503139)
          ·
            refine ⟨4170427835527955739754709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2780285223685303826503139 4170427835527955739754709)
            ·
              refine ⟨97744402395186462650501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 4170427835527955739754709 97744402395186462650501)
              ·
                refine ⟨18327075449097461746969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97744402395186462650501 18327075449097461746969)
                ·
                  rfl

theorem cell20_120460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 4].length) (baseStart_120460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120460 prefixEnd_120460 := by exact prefixLift 120460
  have htrace : WordTrace (prefixWord ++ tailWord_120460) baseStart_120460 baseEnd_120460 := by
    simpa [prefixWord, tailWord_120460, baseEnd_120460] using wordTrace_append hprefix tailTrace_120460
  have hstable : (prefixWord ++ tailWord_120460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120460).length < 2 ^ (prefixWord ++ tailWord_120460).sum := by decide
  have hdescent : baseEnd_120460 < baseStart_120460 := by decide
  rcases family_descends (prefixWord ++ tailWord_120460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120484 : List Nat := [2, 3, 1, 2, 2, 2, 3, 2, 3]
def baseStart_120484 : Nat := 118140960795 + 120484 * 2 ^ 59
def prefixEnd_120484 : Nat := 4983230072969 + 3 ^ 40 * 120484 * 2
def baseEnd_120484 : Nat := 54992180601254968440809

theorem tailTrace_120484 : CollatzResearch.WordTrace tailWord_120484 prefixEnd_120484 54992180601254968440809 := by
  unfold tailWord_120484
  simp only [CollatzResearch.WordTrace]
  refine ⟨2197206247757259937044253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2929608330343013249392337 2197206247757259937044253)
  ·
    refine ⟨823952342908972476391595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2197206247757259937044253 823952342908972476391595)
    ·
      refine ⟨1235928514363458714587393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 823952342908972476391595 1235928514363458714587393)
      ·
        refine ⟨926946385772594035940545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1235928514363458714587393 926946385772594035940545)
        ·
          refine ⟨695209789329445526955409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 926946385772594035940545 695209789329445526955409)
          ·
            refine ⟨521407341997084145216557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 695209789329445526955409 521407341997084145216557)
            ·
              refine ⟨195527753248906554456209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 521407341997084145216557 195527753248906554456209)
              ·
                refine ⟨146645814936679915842157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195527753248906554456209 146645814936679915842157)
                ·
                  refine ⟨54992180601254968440809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146645814936679915842157 54992180601254968440809)
                  ·
                    rfl

theorem cell20_120484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_120484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120484 prefixEnd_120484 := by exact prefixLift 120484
  have htrace : WordTrace (prefixWord ++ tailWord_120484) baseStart_120484 baseEnd_120484 := by
    simpa [prefixWord, tailWord_120484, baseEnd_120484] using wordTrace_append hprefix tailTrace_120484
  have hstable : (prefixWord ++ tailWord_120484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120484).length < 2 ^ (prefixWord ++ tailWord_120484).sum := by decide
  have hdescent : baseEnd_120484 < baseStart_120484 := by decide
  rcases family_descends (prefixWord ++ tailWord_120484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120505 : List Nat := [1, 2, 1, 4, 1, 1, 2, 5, 3]
def baseStart_120505 : Nat := 118140960795 + 120505 * 2 ^ 59
def prefixEnd_120505 : Nat := 4983230072969 + 3 ^ 40 * 120505 * 2
def baseEnd_120505 : Nat := 55001765573472228740723

theorem tailTrace_120505 : CollatzResearch.WordTrace tailWord_120505 prefixEnd_120505 55001765573472228740723 := by
  unfold tailWord_120505
  simp only [CollatzResearch.WordTrace]
  refine ⟨4395178428438440460602969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2930118952292293640401979 4395178428438440460602969)
  ·
    refine ⟨3296383821328830345452227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4395178428438440460602969 3296383821328830345452227)
    ·
      refine ⟨4944575731993245518178341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3296383821328830345452227 4944575731993245518178341)
      ·
        refine ⟨927107949748733534658439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4944575731993245518178341 927107949748733534658439)
        ·
          refine ⟨1390661924623100301987659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927107949748733534658439 1390661924623100301987659)
          ·
            refine ⟨2085992886934650452981489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390661924623100301987659 2085992886934650452981489)
            ·
              refine ⟨1564494665200987839736117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2085992886934650452981489 1564494665200987839736117)
              ·
                refine ⟨146671374862592609975261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1564494665200987839736117 146671374862592609975261)
                ·
                  refine ⟨55001765573472228740723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146671374862592609975261 55001765573472228740723)
                  ·
                    rfl

theorem cell20_120505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 3].length) (baseStart_120505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120505 prefixEnd_120505 := by exact prefixLift 120505
  have htrace : WordTrace (prefixWord ++ tailWord_120505) baseStart_120505 baseEnd_120505 := by
    simpa [prefixWord, tailWord_120505, baseEnd_120505] using wordTrace_append hprefix tailTrace_120505
  have hstable : (prefixWord ++ tailWord_120505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120505).length < 2 ^ (prefixWord ++ tailWord_120505).sum := by decide
  have hdescent : baseEnd_120505 < baseStart_120505 := by decide
  rcases family_descends (prefixWord ++ tailWord_120505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120512 : List Nat := [2, 1, 1, 2, 4, 1, 1, 4, 4]
def baseStart_120512 : Nat := 118140960795 + 120512 * 2 ^ 59
def prefixEnd_120512 : Nat := 4983230072969 + 3 ^ 40 * 120512 * 2
def baseEnd_120512 : Nat := 55004960564211315507361

theorem tailTrace_120512 : CollatzResearch.WordTrace tailWord_120512 prefixEnd_120512 55004960564211315507361 := by
  unfold tailWord_120512
  simp only [CollatzResearch.WordTrace]
  refine ⟨2197716869706540328053895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2930289159608720437405193 2197716869706540328053895)
  ·
    refine ⟨3296575304559810492080843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2197716869706540328053895 3296575304559810492080843)
    ·
      refine ⟨4944862956839715738121265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3296575304559810492080843 4944862956839715738121265)
      ·
        refine ⟨3708647217629786803590949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4944862956839715738121265 3708647217629786803590949)
        ·
          refine ⟨695371353305585025673303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3708647217629786803590949 695371353305585025673303)
          ·
            refine ⟨1043057029958377538509955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695371353305585025673303 1043057029958377538509955)
            ·
              refine ⟨1564585544937566307764933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1043057029958377538509955 1564585544937566307764933)
              ·
                refine ⟨293359789675793682705925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1564585544937566307764933 293359789675793682705925)
                ·
                  refine ⟨55004960564211315507361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 293359789675793682705925 55004960564211315507361)
                  ·
                    rfl

theorem cell20_120512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_120512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120512 prefixEnd_120512 := by exact prefixLift 120512
  have htrace : WordTrace (prefixWord ++ tailWord_120512) baseStart_120512 baseEnd_120512 := by
    simpa [prefixWord, tailWord_120512, baseEnd_120512] using wordTrace_append hprefix tailTrace_120512
  have hstable : (prefixWord ++ tailWord_120512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120512).length < 2 ^ (prefixWord ++ tailWord_120512).sum := by decide
  have hdescent : baseEnd_120512 < baseStart_120512 := by decide
  rcases family_descends (prefixWord ++ tailWord_120512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120519 : List Nat := [1, 1, 4, 1, 1, 1, 5, 6]
def baseStart_120519 : Nat := 118140960795 + 120519 * 2 ^ 59
def prefixEnd_120519 : Nat := 4983230072969 + 3 ^ 40 * 120519 * 2
def baseEnd_120519 : Nat := 18336051851650134091333

theorem tailTrace_120519 : CollatzResearch.WordTrace tailWord_120519 prefixEnd_120519 18336051851650134091333 := by
  unfold tailWord_120519
  simp only [CollatzResearch.WordTrace]
  refine ⟨4395689050387720851612611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2930459366925147234408407 4395689050387720851612611)
  ·
    refine ⟨6593533575581581277418917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4395689050387720851612611 6593533575581581277418917)
    ·
      refine ⟨1236287545421546489516047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6593533575581581277418917 1236287545421546489516047)
      ·
        refine ⟨1854431318132319734274071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1236287545421546489516047 1854431318132319734274071)
        ·
          refine ⟨2781646977198479601411107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1854431318132319734274071 2781646977198479601411107)
          ·
            refine ⟨4172470465797719402116661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2781646977198479601411107 4172470465797719402116661)
            ·
              refine ⟨391169106168536193948437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4172470465797719402116661 391169106168536193948437)
              ·
                refine ⟨18336051851650134091333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 391169106168536193948437 18336051851650134091333)
                ·
                  rfl

theorem cell20_120519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 6].length) (baseStart_120519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120519 prefixEnd_120519 := by exact prefixLift 120519
  have htrace : WordTrace (prefixWord ++ tailWord_120519) baseStart_120519 baseEnd_120519 := by
    simpa [prefixWord, tailWord_120519, baseEnd_120519] using wordTrace_append hprefix tailTrace_120519
  have hstable : (prefixWord ++ tailWord_120519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120519).length < 2 ^ (prefixWord ++ tailWord_120519).sum := by decide
  have hdescent : baseEnd_120519 < baseStart_120519 := by decide
  rcases family_descends (prefixWord ++ tailWord_120519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120543 : List Nat := [1, 1, 2, 3, 2, 2, 2, 4, 3]
def baseStart_120543 : Nat := 118140960795 + 120543 * 2 ^ 59
def prefixEnd_120543 : Nat := 4983230072969 + 3 ^ 40 * 120543 * 2
def baseEnd_120543 : Nat := 55019109808912985473901

theorem tailTrace_120543 : CollatzResearch.WordTrace tailWord_120543 prefixEnd_120543 55019109808912985473901 := by
  unfold tailWord_120543
  simp only [CollatzResearch.WordTrace]
  refine ⟨4396564402300772950486283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2931042934867181966990855 4396564402300772950486283)
  ·
    refine ⟨6594846603451159425729425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4396564402300772950486283 6594846603451159425729425)
    ·
      refine ⟨4946134952588369569297069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6594846603451159425729425 4946134952588369569297069)
      ·
        refine ⟨1854800607220638588486401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4946134952588369569297069 1854800607220638588486401)
        ·
          refine ⟨1391100455415478941364801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1854800607220638588486401 1391100455415478941364801)
          ·
            refine ⟨1043325341561609206023601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1391100455415478941364801 1043325341561609206023601)
            ·
              refine ⟨782494006171206904517701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1043325341561609206023601 782494006171206904517701)
              ·
                refine ⟨146717626157101294597069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 782494006171206904517701 146717626157101294597069)
                ·
                  refine ⟨55019109808912985473901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146717626157101294597069 55019109808912985473901)
                  ·
                    rfl

theorem cell20_120543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 3].length) (baseStart_120543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120543 prefixEnd_120543 := by exact prefixLift 120543
  have htrace : WordTrace (prefixWord ++ tailWord_120543) baseStart_120543 baseEnd_120543 := by
    simpa [prefixWord, tailWord_120543, baseEnd_120543] using wordTrace_append hprefix tailTrace_120543
  have hstable : (prefixWord ++ tailWord_120543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120543).length < 2 ^ (prefixWord ++ tailWord_120543).sum := by decide
  have hdescent : baseEnd_120543 < baseStart_120543 := by decide
  rcases family_descends (prefixWord ++ tailWord_120543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120612 : List Nat := [2, 3, 1, 3, 2, 1, 3, 5]
def baseStart_120612 : Nat := 118140960795 + 120612 * 2 ^ 59
def prefixEnd_120612 : Nat := 4983230072969 + 3 ^ 40 * 120612 * 2
def baseEnd_120612 : Nat := 18350201096351804057873

theorem tailTrace_120612 : CollatzResearch.WordTrace tailWord_120612 prefixEnd_120612 18350201096351804057873 := by
  unfold tailWord_120612
  simp only [CollatzResearch.WordTrace]
  refine ⟨2199540519525398867374045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2932720692700531823165393 2199540519525398867374045)
  ·
    refine ⟨824827694822024575265267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2199540519525398867374045 824827694822024575265267)
    ·
      refine ⟨1237241542233036862897901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 824827694822024575265267 1237241542233036862897901)
      ·
        refine ⟨463965578337388823586713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1237241542233036862897901 463965578337388823586713)
        ·
          refine ⟨347974183753041617690035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463965578337388823586713 347974183753041617690035)
          ·
            refine ⟨521961275629562426535053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347974183753041617690035 521961275629562426535053)
            ·
              refine ⟨195735478361085909950645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 521961275629562426535053 195735478361085909950645)
              ·
                refine ⟨18350201096351804057873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 195735478361085909950645 18350201096351804057873)
                ·
                  rfl

theorem cell20_120612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_120612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120612 prefixEnd_120612 := by exact prefixLift 120612
  have htrace : WordTrace (prefixWord ++ tailWord_120612) baseStart_120612 baseEnd_120612 := by
    simpa [prefixWord, tailWord_120612, baseEnd_120612] using wordTrace_append hprefix tailTrace_120612
  have hstable : (prefixWord ++ tailWord_120612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120612).length < 2 ^ (prefixWord ++ tailWord_120612).sum := by decide
  have hdescent : baseEnd_120612 < baseStart_120612 := by decide
  rcases family_descends (prefixWord ++ tailWord_120612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120622 : List Nat := [4, 1, 3, 2, 2, 1, 1, 2, 4]
def baseStart_120622 : Nat := 118140960795 + 120622 * 2 ^ 59
def prefixEnd_120622 : Nat := 4983230072969 + 3 ^ 40 * 120622 * 2
def baseEnd_120622 : Nat := 55055167561539821840245

theorem tailTrace_120622 : CollatzResearch.WordTrace tailWord_120622 prefixEnd_120622 55055167561539821840245 := by
  unfold tailWord_120622
  simp only [CollatzResearch.WordTrace]
  refine ⟨549930721126821180326515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2932963846009712961741413 549930721126821180326515)
  ·
    refine ⟨824896081690231770489773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 549930721126821180326515 824896081690231770489773)
    ·
      refine ⟨309336030633836913933665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 824896081690231770489773 309336030633836913933665)
      ·
        refine ⟨232002022975377685450249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309336030633836913933665 232002022975377685450249)
        ·
          refine ⟨174001517231533264087687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232002022975377685450249 174001517231533264087687)
          ·
            refine ⟨261002275847299896131531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174001517231533264087687 261002275847299896131531)
            ·
              refine ⟨391503413770949844197297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261002275847299896131531 391503413770949844197297)
              ·
                refine ⟨293627560328212383147973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391503413770949844197297 293627560328212383147973)
                ·
                  refine ⟨55055167561539821840245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 293627560328212383147973 55055167561539821840245)
                  ·
                    rfl

theorem cell20_120622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_120622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120622 prefixEnd_120622 := by exact prefixLift 120622
  have htrace : WordTrace (prefixWord ++ tailWord_120622) baseStart_120622 baseEnd_120622 := by
    simpa [prefixWord, tailWord_120622, baseEnd_120622] using wordTrace_append hprefix tailTrace_120622
  have hstable : (prefixWord ++ tailWord_120622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120622).length < 2 ^ (prefixWord ++ tailWord_120622).sum := by decide
  have hdescent : baseEnd_120622 < baseStart_120622 := by decide
  rcases family_descends (prefixWord ++ tailWord_120622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120626 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 6]
def baseStart_120626 : Nat := 118140960795 + 120626 * 2 ^ 59
def prefixEnd_120626 : Nat := 4983230072969 + 3 ^ 40 * 120626 * 2
def baseEnd_120626 : Nat := 55056993270533585706895

theorem tailTrace_120626 : CollatzResearch.WordTrace tailWord_120626 prefixEnd_120626 55056993270533585706895 := by
  unfold tailWord_120626
  simp only [CollatzResearch.WordTrace]
  refine ⟨1099897915250019531439433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2933061107333385417171821 1099897915250019531439433)
  ·
    refine ⟨824923436437514648579575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1099897915250019531439433 824923436437514648579575)
    ·
      refine ⟨1237385154656271972869363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 824923436437514648579575 1237385154656271972869363)
      ·
        refine ⟨1856077731984407959304045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1237385154656271972869363 1856077731984407959304045)
        ·
          refine ⟨696029149494152984739017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1856077731984407959304045 696029149494152984739017)
          ·
            refine ⟨522021862120614738554263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 696029149494152984739017 522021862120614738554263)
            ·
              refine ⟨783032793180922107831395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522021862120614738554263 783032793180922107831395)
              ·
                refine ⟨1174549189771383161747093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 783032793180922107831395 1174549189771383161747093)
                ·
                  refine ⟨55056993270533585706895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1174549189771383161747093 55056993270533585706895)
                  ·
                    rfl

theorem cell20_120626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_120626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120626 prefixEnd_120626 := by exact prefixLift 120626
  have htrace : WordTrace (prefixWord ++ tailWord_120626) baseStart_120626 baseEnd_120626 := by
    simpa [prefixWord, tailWord_120626, baseEnd_120626] using wordTrace_append hprefix tailTrace_120626
  have hstable : (prefixWord ++ tailWord_120626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120626).length < 2 ^ (prefixWord ++ tailWord_120626).sum := by decide
  have hdescent : baseEnd_120626 < baseStart_120626 := by decide
  rcases family_descends (prefixWord ++ tailWord_120626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120629 : List Nat := [1, 3, 3, 1, 4, 1, 3, 4]
def baseStart_120629 : Nat := 118140960795 + 120629 * 2 ^ 59
def prefixEnd_120629 : Nat := 4983230072969 + 3 ^ 40 * 120629 * 2
def baseEnd_120629 : Nat := 18352787517426302868961

theorem tailTrace_120629 : CollatzResearch.WordTrace tailWord_120629 prefixEnd_120629 18352787517426302868961 := by
  unfold tailWord_120629
  simp only [CollatzResearch.WordTrace]
  refine ⟨4399701079989209638116941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2933134053326139758744627 4399701079989209638116941)
  ·
    refine ⟨1649887904995953614293853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4399701079989209638116941 1649887904995953614293853)
    ·
      refine ⟨618707964373482605360195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1649887904995953614293853 618707964373482605360195)
      ·
        refine ⟨928061946560223908040293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618707964373482605360195 928061946560223908040293)
        ·
          refine ⟨174011614980041982757555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 928061946560223908040293 174011614980041982757555)
          ·
            refine ⟨261017422470062974136333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174011614980041982757555 261017422470062974136333)
            ·
              refine ⟨97881533426273615301125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261017422470062974136333 97881533426273615301125)
              ·
                refine ⟨18352787517426302868961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97881533426273615301125 18352787517426302868961)
                ·
                  rfl

theorem cell20_120629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 4].length) (baseStart_120629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120629 prefixEnd_120629 := by exact prefixLift 120629
  have htrace : WordTrace (prefixWord ++ tailWord_120629) baseStart_120629 baseEnd_120629 := by
    simpa [prefixWord, tailWord_120629, baseEnd_120629] using wordTrace_append hprefix tailTrace_120629
  have hstable : (prefixWord ++ tailWord_120629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120629).length < 2 ^ (prefixWord ++ tailWord_120629).sum := by decide
  have hdescent : baseEnd_120629 < baseStart_120629 := by decide
  rcases family_descends (prefixWord ++ tailWord_120629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120643 : List Nat := [1, 1, 1, 3, 1, 5, 1, 5, 2]
def baseStart_120643 : Nat := 118140960795 + 120643 * 2 ^ 59
def prefixEnd_120643 : Nat := 4983230072969 + 3 ^ 40 * 120643 * 2
def baseEnd_120643 : Nat := 55064752533757082140159

theorem tailTrace_120643 : CollatzResearch.WordTrace tailWord_120643 prefixEnd_120643 55064752533757082140159 := by
  unfold tailWord_120643
  simp only [CollatzResearch.WordTrace]
  refine ⟨4400211701938490029126583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2933474467958993352751055 4400211701938490029126583)
  ·
    refine ⟨6600317552907735043689875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4400211701938490029126583 6600317552907735043689875)
    ·
      refine ⟨9900476329361602565534813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6600317552907735043689875 9900476329361602565534813)
      ·
        refine ⟨3712678623510600962075555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9900476329361602565534813 3712678623510600962075555)
        ·
          refine ⟨5569017935265901443113333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3712678623510600962075555 5569017935265901443113333)
          ·
            refine ⟨522095431431178260291875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5569017935265901443113333 522095431431178260291875)
            ·
              refine ⟨783143147146767390437813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522095431431178260291875 783143147146767390437813)
              ·
                refine ⟨73419670045009442853545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 783143147146767390437813 73419670045009442853545)
                ·
                  refine ⟨55064752533757082140159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73419670045009442853545 55064752533757082140159)
                  ·
                    rfl

theorem cell20_120643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 2].length) (baseStart_120643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120643 prefixEnd_120643 := by exact prefixLift 120643
  have htrace : WordTrace (prefixWord ++ tailWord_120643) baseStart_120643 baseEnd_120643 := by
    simpa [prefixWord, tailWord_120643, baseEnd_120643] using wordTrace_append hprefix tailTrace_120643
  have hstable : (prefixWord ++ tailWord_120643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120643).length < 2 ^ (prefixWord ++ tailWord_120643).sum := by decide
  have hdescent : baseEnd_120643 < baseStart_120643 := by decide
  rcases family_descends (prefixWord ++ tailWord_120643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120653 : List Nat := [1, 6, 1, 2, 1, 1, 3, 2, 3]
def baseStart_120653 : Nat := 118140960795 + 120653 * 2 ^ 59
def prefixEnd_120653 : Nat := 4983230072969 + 3 ^ 40 * 120653 * 2
def baseEnd_120653 : Nat := 55069316806241491806785

theorem tailTrace_120653 : CollatzResearch.WordTrace tailWord_120653 prefixEnd_120653 55069316806241491806785 := by
  unfold tailWord_120653
  simp only [CollatzResearch.WordTrace]
  refine ⟨4400576431902261736990613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2933717621268174491327075 4400576431902261736990613)
  ·
    refine ⟨206277020245418518921435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4400576431902261736990613 206277020245418518921435)
    ·
      refine ⟨309415530368127778382153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206277020245418518921435 309415530368127778382153)
      ·
        refine ⟨232061647776095833786615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309415530368127778382153 232061647776095833786615)
        ·
          refine ⟨348092471664143750679923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232061647776095833786615 348092471664143750679923)
          ·
            refine ⟨522138707496215626019885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348092471664143750679923 522138707496215626019885)
            ·
              refine ⟨195802015311080859757457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 522138707496215626019885 195802015311080859757457)
              ·
                refine ⟨146851511483310644818093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195802015311080859757457 146851511483310644818093)
                ·
                  refine ⟨55069316806241491806785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146851511483310644818093 55069316806241491806785)
                  ·
                    rfl

theorem cell20_120653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_120653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120653 prefixEnd_120653 := by exact prefixLift 120653
  have htrace : WordTrace (prefixWord ++ tailWord_120653) baseStart_120653 baseEnd_120653 := by
    simpa [prefixWord, tailWord_120653, baseEnd_120653] using wordTrace_append hprefix tailTrace_120653
  have hstable : (prefixWord ++ tailWord_120653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120653).length < 2 ^ (prefixWord ++ tailWord_120653).sum := by decide
  have hdescent : baseEnd_120653 < baseStart_120653 := by decide
  rcases family_descends (prefixWord ++ tailWord_120653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120657 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 5]
def baseStart_120657 : Nat := 118140960795 + 120657 * 2 ^ 59
def prefixEnd_120657 : Nat := 4983230072969 + 3 ^ 40 * 120657 * 2
def baseEnd_120657 : Nat := 55071142515235255673435

theorem tailTrace_120657 : CollatzResearch.WordTrace tailWord_120657 prefixEnd_120657 55071142515235255673435 := by
  unfold tailWord_120657
  simp only [CollatzResearch.WordTrace]
  refine ⟨4400722323887770420136225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2933814882591846946757483 4400722323887770420136225)
  ·
    refine ⟨3300541742915827815102169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4400722323887770420136225 3300541742915827815102169)
    ·
      refine ⟨2475406307186870861326627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3300541742915827815102169 2475406307186870861326627)
      ·
        refine ⟨3713109460780306291989941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2475406307186870861326627 3713109460780306291989941)
        ·
          refine ⟨348104011948153714874057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3713109460780306291989941 348104011948153714874057)
          ·
            refine ⟨261078008961115286155543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348104011948153714874057 261078008961115286155543)
            ·
              refine ⟨391617013441672929233315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261078008961115286155543 391617013441672929233315)
              ·
                refine ⟨587425520162509393849973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 391617013441672929233315 587425520162509393849973)
                ·
                  refine ⟨55071142515235255673435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 587425520162509393849973 55071142515235255673435)
                  ·
                    rfl

theorem cell20_120657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_120657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120657 prefixEnd_120657 := by exact prefixLift 120657
  have htrace : WordTrace (prefixWord ++ tailWord_120657) baseStart_120657 baseEnd_120657 := by
    simpa [prefixWord, tailWord_120657, baseEnd_120657] using wordTrace_append hprefix tailTrace_120657
  have hstable : (prefixWord ++ tailWord_120657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120657).length < 2 ^ (prefixWord ++ tailWord_120657).sum := by decide
  have hdescent : baseEnd_120657 < baseStart_120657 := by decide
  rcases family_descends (prefixWord ++ tailWord_120657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120660 : List Nat := [2, 4, 1, 1, 3, 1, 2, 4, 2]
def baseStart_120660 : Nat := 118140960795 + 120660 * 2 ^ 59
def prefixEnd_120660 : Nat := 4983230072969 + 3 ^ 40 * 120660 * 2
def baseEnd_120660 : Nat := 55072511796980578573423

theorem tailTrace_120660 : CollatzResearch.WordTrace tailWord_120660 prefixEnd_120660 55072511796980578573423 := by
  unfold tailWord_120660
  simp only [CollatzResearch.WordTrace]
  refine ⟨2200415871438450966247717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2933887828584601288330289 2200415871438450966247717)
  ·
    refine ⟨412577975894709556171447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2200415871438450966247717 412577975894709556171447)
    ·
      refine ⟨618866963842064334257171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412577975894709556171447 618866963842064334257171)
      ·
        refine ⟨928300445763096501385757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618866963842064334257171 928300445763096501385757)
        ·
          refine ⟨348112667161161188019659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 928300445763096501385757 348112667161161188019659)
          ·
            refine ⟨522169000741741782029489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348112667161161188019659 522169000741741782029489)
            ·
              refine ⟨391626750556306336522117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522169000741741782029489 391626750556306336522117)
              ·
                refine ⟨73430015729307438097897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 391626750556306336522117 73430015729307438097897)
                ·
                  refine ⟨55072511796980578573423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73430015729307438097897 55072511796980578573423)
                  ·
                    rfl

theorem cell20_120660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_120660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120660 prefixEnd_120660 := by exact prefixLift 120660
  have htrace : WordTrace (prefixWord ++ tailWord_120660) baseStart_120660 baseEnd_120660 := by
    simpa [prefixWord, tailWord_120660, baseEnd_120660] using wordTrace_append hprefix tailTrace_120660
  have hstable : (prefixWord ++ tailWord_120660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120660).length < 2 ^ (prefixWord ++ tailWord_120660).sum := by decide
  have hdescent : baseEnd_120660 < baseStart_120660 := by decide
  rcases family_descends (prefixWord ++ tailWord_120660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120694 : List Nat := [5, 1, 1, 3, 2, 2, 1, 3, 2]
def baseStart_120694 : Nat := 118140960795 + 120694 * 2 ^ 59
def prefixEnd_120694 : Nat := 4983230072969 + 3 ^ 40 * 120694 * 2
def baseEnd_120694 : Nat := 55088030323427571439951

theorem tailTrace_120694 : CollatzResearch.WordTrace tailWord_120694 prefixEnd_120694 55088030323427571439951 := by
  unfold tailWord_120694
  simp only [CollatzResearch.WordTrace]
  refine ⟨275129489047107858702071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2934714549835817159488757 275129489047107858702071)
  ·
    refine ⟨412694233570661788053107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275129489047107858702071 412694233570661788053107)
    ·
      refine ⟨619041350355992682079661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412694233570661788053107 619041350355992682079661)
      ·
        refine ⟨232140506383497255779873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 619041350355992682079661 232140506383497255779873)
        ·
          refine ⟨174105379787622941834905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232140506383497255779873 174105379787622941834905)
          ·
            refine ⟨130579034840717206376179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174105379787622941834905 130579034840717206376179)
            ·
              refine ⟨195868552261075809564269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130579034840717206376179 195868552261075809564269)
              ·
                refine ⟨73450707097903428586601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195868552261075809564269 73450707097903428586601)
                ·
                  refine ⟨55088030323427571439951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73450707097903428586601 55088030323427571439951)
                  ·
                    rfl

theorem cell20_120694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_120694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120694 prefixEnd_120694 := by exact prefixLift 120694
  have htrace : WordTrace (prefixWord ++ tailWord_120694) baseStart_120694 baseEnd_120694 := by
    simpa [prefixWord, tailWord_120694, baseEnd_120694] using wordTrace_append hprefix tailTrace_120694
  have hstable : (prefixWord ++ tailWord_120694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120694).length < 2 ^ (prefixWord ++ tailWord_120694).sum := by decide
  have hdescent : baseEnd_120694 < baseStart_120694 := by decide
  rcases family_descends (prefixWord ++ tailWord_120694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120705 : List Nat := [1, 2, 4, 4, 1, 2, 6]
def baseStart_120705 : Nat := 118140960795 + 120705 * 2 ^ 59
def prefixEnd_120705 : Nat := 4983230072969 + 3 ^ 40 * 120705 * 2
def baseEnd_120705 : Nat := 6121450113684491341471

theorem tailTrace_120705 : CollatzResearch.WordTrace tailWord_120705 prefixEnd_120705 6121450113684491341471 := by
  unfold tailWord_120705
  simp only [CollatzResearch.WordTrace]
  refine ⟨4402473027713874617883569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2934982018475916411922379 4402473027713874617883569)
  ·
    refine ⟨3301854770785405963412677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4402473027713874617883569 3301854770785405963412677)
    ·
      refine ⟨619097769522263618139877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3301854770785405963412677 619097769522263618139877)
      ·
        refine ⟨116080831785424428401227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 619097769522263618139877 116080831785424428401227)
        ·
          refine ⟨174121247678136642601841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116080831785424428401227 174121247678136642601841)
          ·
            refine ⟨130590935758602481951381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174121247678136642601841 130590935758602481951381)
            ·
              refine ⟨6121450113684491341471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130590935758602481951381 6121450113684491341471)
              ·
                rfl

theorem cell20_120705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 6].length) (baseStart_120705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120705 prefixEnd_120705 := by exact prefixLift 120705
  have htrace : WordTrace (prefixWord ++ tailWord_120705) baseStart_120705 baseEnd_120705 := by
    simpa [prefixWord, tailWord_120705, baseEnd_120705] using wordTrace_append hprefix tailTrace_120705
  have hstable : (prefixWord ++ tailWord_120705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120705).length < 2 ^ (prefixWord ++ tailWord_120705).sum := by decide
  have hdescent : baseEnd_120705 < baseStart_120705 := by decide
  rcases family_descends (prefixWord ++ tailWord_120705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120754 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_120754 : Nat := 118140960795 + 120754 * 2 ^ 59
def prefixEnd_120754 : Nat := 4983230072969 + 3 ^ 40 * 120754 * 2
def baseEnd_120754 : Nat := 55115415958334029439705

theorem tailTrace_120754 : CollatzResearch.WordTrace tailWord_120754 prefixEnd_120754 55115415958334029439705 := by
  unfold tailWord_120754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1101065051134088996604329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2936173469690903990944877 1101065051134088996604329)
  ·
    refine ⟨825798788350566747453247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1101065051134088996604329 825798788350566747453247)
    ·
      refine ⟨1238698182525850121179871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 825798788350566747453247 1238698182525850121179871)
      ·
        refine ⟨1858047273788775181769807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1238698182525850121179871 1858047273788775181769807)
        ·
          refine ⟨2787070910683162772654711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1858047273788775181769807 2787070910683162772654711)
          ·
            refine ⟨4180606366024744158982067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2787070910683162772654711 4180606366024744158982067)
            ·
              refine ⟨6270909549037116238473101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4180606366024744158982067 6270909549037116238473101)
              ·
                refine ⟨2351591080888918589427413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6270909549037116238473101 2351591080888918589427413)
                ·
                  refine ⟨55115415958334029439705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2351591080888918589427413 55115415958334029439705)
                  ·
                    rfl

theorem cell20_120754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_120754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120754 prefixEnd_120754 := by exact prefixLift 120754
  have htrace : WordTrace (prefixWord ++ tailWord_120754) baseStart_120754 baseEnd_120754 := by
    simpa [prefixWord, tailWord_120754, baseEnd_120754] using wordTrace_append hprefix tailTrace_120754
  have hstable : (prefixWord ++ tailWord_120754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120754).length < 2 ^ (prefixWord ++ tailWord_120754).sum := by decide
  have hdescent : baseEnd_120754 < baseStart_120754 := by decide
  rcases family_descends (prefixWord ++ tailWord_120754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120764 : List Nat := [2, 2, 2, 5, 1, 8]
def baseStart_120764 : Nat := 118140960795 + 120764 * 2 ^ 59
def prefixEnd_120764 : Nat := 4983230072969 + 3 ^ 40 * 120764 * 2
def baseEnd_120764 : Nat := 2041480749289571818753

theorem tailTrace_120764 : CollatzResearch.WordTrace tailWord_120764 prefixEnd_120764 2041480749289571818753 := by
  unfold tailWord_120764
  simp only [CollatzResearch.WordTrace]
  refine ⟨2202312467250063847140673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2936416623000085129520897 2202312467250063847140673)
  ·
    refine ⟨1651734350437547885355505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2202312467250063847140673 1651734350437547885355505)
    ·
      refine ⟨1238800762828160914016629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1651734350437547885355505 1238800762828160914016629)
      ·
        refine ⟨116137571515140085689059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1238800762828160914016629 116137571515140085689059)
        ·
          refine ⟨174206357272710128533589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116137571515140085689059 174206357272710128533589)
          ·
            refine ⟨2041480749289571818753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 174206357272710128533589 2041480749289571818753)
            ·
              rfl

theorem cell20_120764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 8].length) (baseStart_120764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120764 prefixEnd_120764 := by exact prefixLift 120764
  have htrace : WordTrace (prefixWord ++ tailWord_120764) baseStart_120764 baseEnd_120764 := by
    simpa [prefixWord, tailWord_120764, baseEnd_120764] using wordTrace_append hprefix tailTrace_120764
  have hstable : (prefixWord ++ tailWord_120764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120764).length < 2 ^ (prefixWord ++ tailWord_120764).sum := by decide
  have hdescent : baseEnd_120764 < baseStart_120764 := by decide
  rcases family_descends (prefixWord ++ tailWord_120764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120822 : List Nat := [5, 1, 1, 1, 5, 1, 1, 2, 3]
def baseStart_120822 : Nat := 118140960795 + 120822 * 2 ^ 59
def prefixEnd_120822 : Nat := 4983230072969 + 3 ^ 40 * 120822 * 2
def baseEnd_120822 : Nat := 55146453011228015172761

theorem tailTrace_120822 : CollatzResearch.WordTrace tailWord_120822 prefixEnd_120822 55146453011228015172761 := by
  unfold tailWord_120822
  simp only [CollatzResearch.WordTrace]
  refine ⟨275421273018125224993295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2937826912193335733261813 275421273018125224993295)
  ·
    refine ⟨413131909527187837489943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275421273018125224993295 413131909527187837489943)
    ·
      refine ⟨619697864290781756234915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413131909527187837489943 619697864290781756234915)
      ·
        refine ⟨929546796436172634352373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619697864290781756234915 929546796436172634352373)
        ·
          refine ⟨87145012165891184470535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 929546796436172634352373 87145012165891184470535)
          ·
            refine ⟨130717518248836776705803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87145012165891184470535 130717518248836776705803)
            ·
              refine ⟨196076277373255165058705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130717518248836776705803 196076277373255165058705)
              ·
                refine ⟨147057208029941373794029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196076277373255165058705 147057208029941373794029)
                ·
                  refine ⟨55146453011228015172761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147057208029941373794029 55146453011228015172761)
                  ·
                    rfl

theorem cell20_120822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_120822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120822 prefixEnd_120822 := by exact prefixLift 120822
  have htrace : WordTrace (prefixWord ++ tailWord_120822) baseStart_120822 baseEnd_120822 := by
    simpa [prefixWord, tailWord_120822, baseEnd_120822] using wordTrace_append hprefix tailTrace_120822
  have hstable : (prefixWord ++ tailWord_120822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120822).length < 2 ^ (prefixWord ++ tailWord_120822).sum := by decide
  have hdescent : baseEnd_120822 < baseStart_120822 := by decide
  rcases family_descends (prefixWord ++ tailWord_120822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120833 : List Nat := [1, 2, 4, 1, 2, 1, 1, 6, 2]
def baseStart_120833 : Nat := 118140960795 + 120833 * 2 ^ 59
def prefixEnd_120833 : Nat := 4983230072969 + 3 ^ 40 * 120833 * 2
def baseEnd_120833 : Nat := 55151473710960865806049

theorem tailTrace_120833 : CollatzResearch.WordTrace tailWord_120833 prefixEnd_120833 55151473710960865806049 := by
  unfold tailWord_120833
  simp only [CollatzResearch.WordTrace]
  refine ⟨4407141571250152478543153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2938094380833434985695435 4407141571250152478543153)
  ·
    refine ⟨3305356178437614358907365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4407141571250152478543153 3305356178437614358907365)
    ·
      refine ⟨619754283457052692295131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3305356178437614358907365 619754283457052692295131)
      ·
        refine ⟨929631425185579038442697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619754283457052692295131 929631425185579038442697)
        ·
          refine ⟨697223568889184278832023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 929631425185579038442697 697223568889184278832023)
          ·
            refine ⟨1045835353333776418248035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697223568889184278832023 1045835353333776418248035)
            ·
              refine ⟨1568753030000664627372053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045835353333776418248035 1568753030000664627372053)
              ·
                refine ⟨73535298281281154408065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1568753030000664627372053 73535298281281154408065)
                ·
                  refine ⟨55151473710960865806049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73535298281281154408065 55151473710960865806049)
                  ·
                    rfl

theorem cell20_120833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 2].length) (baseStart_120833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120833 prefixEnd_120833 := by exact prefixLift 120833
  have htrace : WordTrace (prefixWord ++ tailWord_120833) baseStart_120833 baseEnd_120833 := by
    simpa [prefixWord, tailWord_120833, baseEnd_120833] using wordTrace_append hprefix tailTrace_120833
  have hstable : (prefixWord ++ tailWord_120833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120833).length < 2 ^ (prefixWord ++ tailWord_120833).sum := by decide
  have hdescent : baseEnd_120833 < baseStart_120833 := by decide
  rcases family_descends (prefixWord ++ tailWord_120833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120878 : List Nat := [4, 1, 3, 1, 1, 4, 6]
def baseStart_120878 : Nat := 118140960795 + 120878 * 2 ^ 59
def prefixEnd_120878 : Nat := 4983230072969 + 3 ^ 40 * 120878 * 2
def baseEnd_120878 : Nat := 6130223659682301033985

theorem tailTrace_120878 : CollatzResearch.WordTrace tailWord_120878 prefixEnd_120878 6130223659682301033985 := by
  unfold tailWord_120878
  simp only [CollatzResearch.WordTrace]
  refine ⟨551097857010890645491411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2939188570724750109287525 551097857010890645491411)
  ·
    refine ⟨826646785516335968237117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 551097857010890645491411 826646785516335968237117)
    ·
      refine ⟨309992544568625988088919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 826646785516335968237117 309992544568625988088919)
      ·
        refine ⟨464988816852938982133379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309992544568625988088919 464988816852938982133379)
        ·
          refine ⟨697483225279408473200069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464988816852938982133379 697483225279408473200069)
          ·
            refine ⟨130778104739889088725013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 697483225279408473200069 130778104739889088725013)
            ·
              refine ⟨6130223659682301033985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130778104739889088725013 6130223659682301033985)
              ·
                rfl

theorem cell20_120878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 6].length) (baseStart_120878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120878 prefixEnd_120878 := by exact prefixLift 120878
  have htrace : WordTrace (prefixWord ++ tailWord_120878) baseStart_120878 baseEnd_120878 := by
    simpa [prefixWord, tailWord_120878, baseEnd_120878] using wordTrace_append hprefix tailTrace_120878
  have hstable : (prefixWord ++ tailWord_120878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120878).length < 2 ^ (prefixWord ++ tailWord_120878).sum := by decide
  have hdescent : baseEnd_120878 < baseStart_120878 := by decide
  rcases family_descends (prefixWord ++ tailWord_120878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120884 : List Nat := [2, 5, 1, 2, 2, 1, 3, 2, 2]
def baseStart_120884 : Nat := 118140960795 + 120884 * 2 ^ 59
def prefixEnd_120884 : Nat := 4983230072969 + 3 ^ 40 * 120884 * 2
def baseEnd_120884 : Nat := 55174751500631355105841

theorem tailTrace_120884 : CollatzResearch.WordTrace tailWord_120884 prefixEnd_120884 55174751500631355105841 := by
  unfold tailWord_120884
  simp only [CollatzResearch.WordTrace]
  refine ⟨2204500847032694094324853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2939334462710258792433137 2204500847032694094324853)
  ·
    refine ⟨206671954409315071342955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2204500847032694094324853 206671954409315071342955)
    ·
      refine ⟨310007931613972607014433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206671954409315071342955 310007931613972607014433)
      ·
        refine ⟨232505948710479455260825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310007931613972607014433 232505948710479455260825)
        ·
          refine ⟨174379461532859591445619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232505948710479455260825 174379461532859591445619)
          ·
            refine ⟨261569192299289387168429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174379461532859591445619 261569192299289387168429)
            ·
              refine ⟨98088447112233520188161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261569192299289387168429 98088447112233520188161)
              ·
                refine ⟨73566335334175140141121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98088447112233520188161 73566335334175140141121)
                ·
                  refine ⟨55174751500631355105841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73566335334175140141121 55174751500631355105841)
                  ·
                    rfl

theorem cell20_120884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_120884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120884 prefixEnd_120884 := by exact prefixLift 120884
  have htrace : WordTrace (prefixWord ++ tailWord_120884) baseStart_120884 baseEnd_120884 := by
    simpa [prefixWord, tailWord_120884, baseEnd_120884] using wordTrace_append hprefix tailTrace_120884
  have hstable : (prefixWord ++ tailWord_120884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120884).length < 2 ^ (prefixWord ++ tailWord_120884).sum := by decide
  have hdescent : baseEnd_120884 < baseStart_120884 := by decide
  rcases family_descends (prefixWord ++ tailWord_120884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120888 : List Nat := [2, 1, 2, 1, 7, 1, 1, 1, 4]
def baseStart_120888 : Nat := 118140960795 + 120888 * 2 ^ 59
def prefixEnd_120888 : Nat := 4983230072969 + 3 ^ 40 * 120888 * 2
def baseEnd_120888 : Nat := 55176577209625118972491

theorem tailTrace_120888 : CollatzResearch.WordTrace tailWord_120888 prefixEnd_120888 55176577209625118972491 := by
  unfold tailWord_120888
  simp only [CollatzResearch.WordTrace]
  refine ⟨2204573793025448435897659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2939431724033931247863545 2204573793025448435897659)
  ·
    refine ⟨3306860689538172653846489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2204573793025448435897659 3306860689538172653846489)
    ·
      refine ⟨2480145517153629490384867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3306860689538172653846489 2480145517153629490384867)
      ·
        refine ⟨3720218275730444235577301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480145517153629490384867 3720218275730444235577301)
        ·
          refine ⟨87192615837432286771343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 3720218275730444235577301 87192615837432286771343)
          ·
            refine ⟨130788923756148430157015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87192615837432286771343 130788923756148430157015)
            ·
              refine ⟨196183385634222645235523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130788923756148430157015 196183385634222645235523)
              ·
                refine ⟨294275078451333967853285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196183385634222645235523 294275078451333967853285)
                ·
                  refine ⟨55176577209625118972491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 294275078451333967853285 55176577209625118972491)
                  ·
                    rfl

theorem cell20_120888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 4].length) (baseStart_120888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120888 prefixEnd_120888 := by exact prefixLift 120888
  have htrace : WordTrace (prefixWord ++ tailWord_120888) baseStart_120888 baseEnd_120888 := by
    simpa [prefixWord, tailWord_120888, baseEnd_120888] using wordTrace_append hprefix tailTrace_120888
  have hstable : (prefixWord ++ tailWord_120888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120888).length < 2 ^ (prefixWord ++ tailWord_120888).sum := by decide
  have hdescent : baseEnd_120888 < baseStart_120888 := by decide
  rcases family_descends (prefixWord ++ tailWord_120888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120913 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 6]
def baseStart_120913 : Nat := 118140960795 + 120913 * 2 ^ 59
def prefixEnd_120913 : Nat := 4983230072969 + 3 ^ 40 * 120913 * 2
def baseEnd_120913 : Nat := 55187987890836143139055

theorem tailTrace_120913 : CollatzResearch.WordTrace tailWord_120913 prefixEnd_120913 55187987890836143139055 := by
  unfold tailWord_120913
  simp only [CollatzResearch.WordTrace]
  refine ⟨4410059410960326141455393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2940039607306884094303595 4410059410960326141455393)
  ·
    refine ⟨3307544558220244606091545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4410059410960326141455393 3307544558220244606091545)
    ·
      refine ⟨2480658418665183454568659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3307544558220244606091545 2480658418665183454568659)
      ·
        refine ⟨3720987627997775181852989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480658418665183454568659 3720987627997775181852989)
        ·
          refine ⟨1395370360499165693194871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3720987627997775181852989 1395370360499165693194871)
          ·
            refine ⟨2093055540748748539792307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1395370360499165693194871 2093055540748748539792307)
            ·
              refine ⟨3139583311123122809688461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2093055540748748539792307 3139583311123122809688461)
              ·
                refine ⟨1177343741671171053633173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3139583311123122809688461 1177343741671171053633173)
                ·
                  refine ⟨55187987890836143139055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1177343741671171053633173 55187987890836143139055)
                  ·
                    rfl

theorem cell20_120913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_120913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120913 prefixEnd_120913 := by exact prefixLift 120913
  have htrace : WordTrace (prefixWord ++ tailWord_120913) baseStart_120913 baseEnd_120913 := by
    simpa [prefixWord, tailWord_120913, baseEnd_120913] using wordTrace_append hprefix tailTrace_120913
  have hstable : (prefixWord ++ tailWord_120913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120913).length < 2 ^ (prefixWord ++ tailWord_120913).sum := by decide
  have hdescent : baseEnd_120913 < baseStart_120913 := by decide
  rcases family_descends (prefixWord ++ tailWord_120913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120968 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 6]
def baseStart_120968 : Nat := 118140960795 + 120968 * 2 ^ 59
def prefixEnd_120968 : Nat := 4983230072969 + 3 ^ 40 * 120968 * 2
def baseEnd_120968 : Nat := 55213091389500396305497

theorem tailTrace_120968 : CollatzResearch.WordTrace tailWord_120968 prefixEnd_120968 55213091389500396305497 := by
  unfold tailWord_120968
  simp only [CollatzResearch.WordTrace]
  refine ⟨2206032712880535267353779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2941376950507380356471705 2206032712880535267353779)
  ·
    refine ⟨3309049069320802901030669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2206032712880535267353779 3309049069320802901030669)
    ·
      refine ⟨1240893400995301087886501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3309049069320802901030669 1240893400995301087886501)
      ·
        refine ⟨232667512686618953978719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1240893400995301087886501 232667512686618953978719)
        ·
          refine ⟨349001269029928430968079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232667512686618953978719 349001269029928430968079)
          ·
            refine ⟨523501903544892646452119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349001269029928430968079 523501903544892646452119)
            ·
              refine ⟨785252855317338969678179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523501903544892646452119 785252855317338969678179)
              ·
                refine ⟨1177879282976008454517269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785252855317338969678179 1177879282976008454517269)
                ·
                  refine ⟨55213091389500396305497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1177879282976008454517269 55213091389500396305497)
                  ·
                    rfl

theorem cell20_120968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_120968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_120968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_120968 prefixEnd_120968 := by exact prefixLift 120968
  have htrace : WordTrace (prefixWord ++ tailWord_120968) baseStart_120968 baseEnd_120968 := by
    simpa [prefixWord, tailWord_120968, baseEnd_120968] using wordTrace_append hprefix tailTrace_120968
  have hstable : (prefixWord ++ tailWord_120968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120968).length < 2 ^ (prefixWord ++ tailWord_120968).sum := by decide
  have hdescent : baseEnd_120968 < baseStart_120968 := by decide
  rcases family_descends (prefixWord ++ tailWord_120968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121002 : List Nat := [3, 1, 5, 1, 2, 1, 2, 1, 4]
def baseStart_121002 : Nat := 118140960795 + 121002 * 2 ^ 59
def prefixEnd_121002 : Nat := 4983230072969 + 3 ^ 40 * 121002 * 2
def baseEnd_121002 : Nat := 55228609915947389172025

theorem tailTrace_121002 : CollatzResearch.WordTrace tailWord_121002 prefixEnd_121002 55228609915947389172025 := by
  unfold tailWord_121002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1103326376909473585361315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2942203671758596227630173 1103326376909473585361315)
  ·
    refine ⟨1654989565364210378041973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1103326376909473585361315 1654989565364210378041973)
    ·
      refine ⟨155155271752894722941435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1654989565364210378041973 155155271752894722941435)
      ·
        refine ⟨232732907629342084412153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155155271752894722941435 232732907629342084412153)
        ·
          refine ⟨174549680722006563309115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232732907629342084412153 174549680722006563309115)
          ·
            refine ⟨261824521083009844963673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174549680722006563309115 261824521083009844963673)
            ·
              refine ⟨196368390812257383722755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261824521083009844963673 196368390812257383722755)
              ·
                refine ⟨294552586218386075584133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196368390812257383722755 294552586218386075584133)
                ·
                  refine ⟨55228609915947389172025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 294552586218386075584133 55228609915947389172025)
                  ·
                    rfl

theorem cell20_121002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_121002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121002 prefixEnd_121002 := by exact prefixLift 121002
  have htrace : WordTrace (prefixWord ++ tailWord_121002) baseStart_121002 baseEnd_121002 := by
    simpa [prefixWord, tailWord_121002, baseEnd_121002] using wordTrace_append hprefix tailTrace_121002
  have hstable : (prefixWord ++ tailWord_121002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121002).length < 2 ^ (prefixWord ++ tailWord_121002).sum := by decide
  have hdescent : baseEnd_121002 < baseStart_121002 := by decide
  rcases family_descends (prefixWord ++ tailWord_121002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121026 : List Nat := [3, 5, 1, 1, 1, 1, 4, 4]
def baseStart_121026 : Nat := 118140960795 + 121026 * 2 ^ 59
def prefixEnd_121026 : Nat := 4983230072969 + 3 ^ 40 * 121026 * 2
def baseEnd_121026 : Nat := 18413188056636657457309

theorem tailTrace_121026 : CollatzResearch.WordTrace tailWord_121026 prefixEnd_121026 18413188056636657457309 := by
  unfold tailWord_121026
  simp only [CollatzResearch.WordTrace]
  refine ⟨1103545214887736610079733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2942787239700630960212621 1103545214887736610079733)
  ·
    refine ⟨103457363895725307194975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1103545214887736610079733 103457363895725307194975)
    ·
      refine ⟨155186045843587960792463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103457363895725307194975 155186045843587960792463)
      ·
        refine ⟨232779068765381941188695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155186045843587960792463 232779068765381941188695)
        ·
          refine ⟨349168603148072911783043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232779068765381941188695 349168603148072911783043)
          ·
            refine ⟨523752904722109367674565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349168603148072911783043 523752904722109367674565)
            ·
              refine ⟨98203669635395506438981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 523752904722109367674565 98203669635395506438981)
              ·
                refine ⟨18413188056636657457309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98203669635395506438981 18413188056636657457309)
                ·
                  rfl

theorem cell20_121026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_121026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121026 prefixEnd_121026 := by exact prefixLift 121026
  have htrace : WordTrace (prefixWord ++ tailWord_121026) baseStart_121026 baseEnd_121026 := by
    simpa [prefixWord, tailWord_121026, baseEnd_121026] using wordTrace_append hprefix tailTrace_121026
  have hstable : (prefixWord ++ tailWord_121026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121026).length < 2 ^ (prefixWord ++ tailWord_121026).sum := by decide
  have hdescent : baseEnd_121026 < baseStart_121026 := by decide
  rcases family_descends (prefixWord ++ tailWord_121026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121036 : List Nat := [2, 2, 1, 6, 2, 1, 1, 3, 2]
def baseStart_121036 : Nat := 118140960795 + 121036 * 2 ^ 59
def prefixEnd_121036 : Nat := 4983230072969 + 3 ^ 40 * 121036 * 2
def baseEnd_121036 : Nat := 55244128442394382038553

theorem tailTrace_121036 : CollatzResearch.WordTrace tailWord_121036 prefixEnd_121036 55244128442394382038553 := by
  unfold tailWord_121036
  simp only [CollatzResearch.WordTrace]
  refine ⟨2207272794757359074091481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2943030393009812098788641 2207272794757359074091481)
  ·
    refine ⟨1655454596068019305568611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2207272794757359074091481 1655454596068019305568611)
    ·
      refine ⟨2483181894102028958352917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1655454596068019305568611 2483181894102028958352917)
      ·
        refine ⟨116399151286032607422793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2483181894102028958352917 116399151286032607422793)
        ·
          refine ⟨87299363464524455567095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116399151286032607422793 87299363464524455567095)
          ·
            refine ⟨130949045196786683350643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87299363464524455567095 130949045196786683350643)
            ·
              refine ⟨196423567795180025025965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130949045196786683350643 196423567795180025025965)
              ·
                refine ⟨73658837923192509384737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196423567795180025025965 73658837923192509384737)
                ·
                  refine ⟨55244128442394382038553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73658837923192509384737 55244128442394382038553)
                  ·
                    rfl

theorem cell20_121036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_121036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121036 prefixEnd_121036 := by exact prefixLift 121036
  have htrace : WordTrace (prefixWord ++ tailWord_121036) baseStart_121036 baseEnd_121036 := by
    simpa [prefixWord, tailWord_121036, baseEnd_121036] using wordTrace_append hprefix tailTrace_121036
  have hstable : (prefixWord ++ tailWord_121036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121036).length < 2 ^ (prefixWord ++ tailWord_121036).sum := by decide
  have hdescent : baseEnd_121036 < baseStart_121036 := by decide
  rcases family_descends (prefixWord ++ tailWord_121036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121061 : List Nat := [1, 3, 1, 4, 2, 3, 1, 1, 4]
def baseStart_121061 : Nat := 118140960795 + 121061 * 2 ^ 59
def prefixEnd_121061 : Nat := 4983230072969 + 3 ^ 40 * 121061 * 2
def baseEnd_121061 : Nat := 55255539123605406205117

theorem tailTrace_121061 : CollatzResearch.WordTrace tailWord_121061 prefixEnd_121061 55255539123605406205117 := by
  unfold tailWord_121061
  simp only [CollatzResearch.WordTrace]
  refine ⟨4415457414424147417843037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2943638276282764945228691 4415457414424147417843037)
  ·
    refine ⟨1655796530409055281691139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4415457414424147417843037 1655796530409055281691139)
    ·
      refine ⟨2483694795613582922536709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1655796530409055281691139 2483694795613582922536709)
      ·
        refine ⟨465692774177546797975633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2483694795613582922536709 465692774177546797975633)
        ·
          refine ⟨349269580633160098481725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 465692774177546797975633 349269580633160098481725)
          ·
            refine ⟨130976092737435036930647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 349269580633160098481725 130976092737435036930647)
            ·
              refine ⟨196464139106152555395971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130976092737435036930647 196464139106152555395971)
              ·
                refine ⟨294696208659228833093957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196464139106152555395971 294696208659228833093957)
                ·
                  refine ⟨55255539123605406205117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 294696208659228833093957 55255539123605406205117)
                  ·
                    rfl

theorem cell20_121061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_121061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121061 prefixEnd_121061 := by exact prefixLift 121061
  have htrace : WordTrace (prefixWord ++ tailWord_121061) baseStart_121061 baseEnd_121061 := by
    simpa [prefixWord, tailWord_121061, baseEnd_121061] using wordTrace_append hprefix tailTrace_121061
  have hstable : (prefixWord ++ tailWord_121061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121061).length < 2 ^ (prefixWord ++ tailWord_121061).sum := by decide
  have hdescent : baseEnd_121061 < baseStart_121061 := by decide
  rcases family_descends (prefixWord ++ tailWord_121061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121213 : List Nat := [1, 4, 1, 1, 2, 3, 3, 3, 2]
def baseStart_121213 : Nat := 118140960795 + 121213 * 2 ^ 59
def prefixEnd_121213 : Nat := 4983230072969 + 3 ^ 40 * 121213 * 2
def baseEnd_121213 : Nat := 55324916065368433137829

theorem tailTrace_121213 : CollatzResearch.WordTrace tailWord_121213 prefixEnd_121213 55324916065368433137829 := by
  unfold tailWord_121213
  simp only [CollatzResearch.WordTrace]
  refine ⟨4421001309873477377376293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2947334206582318251584195 4421001309873477377376293)
  ·
    refine ⟨828937745601277008258055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4421001309873477377376293 828937745601277008258055)
    ·
      refine ⟨1243406618401915512387083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 828937745601277008258055 1243406618401915512387083)
      ·
        refine ⟨1865109927602873268580625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1243406618401915512387083 1865109927602873268580625)
        ·
          refine ⟨1398832445702154951435469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1865109927602873268580625 1398832445702154951435469)
          ·
            refine ⟨524562167138308106788301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1398832445702154951435469 524562167138308106788301)
            ·
              refine ⟨196710812676865540045613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 524562167138308106788301 196710812676865540045613)
              ·
                refine ⟨73766554753824577517105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196710812676865540045613 73766554753824577517105)
                ·
                  refine ⟨55324916065368433137829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73766554753824577517105 55324916065368433137829)
                  ·
                    rfl

theorem cell20_121213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_121213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121213 prefixEnd_121213 := by exact prefixLift 121213
  have htrace : WordTrace (prefixWord ++ tailWord_121213) baseStart_121213 baseEnd_121213 := by
    simpa [prefixWord, tailWord_121213, baseEnd_121213] using wordTrace_append hprefix tailTrace_121213
  have hstable : (prefixWord ++ tailWord_121213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121213).length < 2 ^ (prefixWord ++ tailWord_121213).sum := by decide
  have hdescent : baseEnd_121213 < baseStart_121213 := by decide
  rcases family_descends (prefixWord ++ tailWord_121213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121272 : List Nat := [2, 1, 2, 1, 2, 2, 1, 7, 2]
def baseStart_121272 : Nat := 118140960795 + 121272 * 2 ^ 59
def prefixEnd_121272 : Nat := 4983230072969 + 3 ^ 40 * 121272 * 2
def baseEnd_121272 : Nat := 55351845273026450170921

theorem tailTrace_121272 : CollatzResearch.WordTrace tailWord_121272 prefixEnd_121272 55351845273026450170921 := by
  unfold tailWord_121272
  simp only [CollatzResearch.WordTrace]
  refine ⟨2211576608329865226887035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2948768811106486969182713 2211576608329865226887035)
  ·
    refine ⟨3317364912494797840330553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2211576608329865226887035 3317364912494797840330553)
    ·
      refine ⟨2488023684371098380247915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3317364912494797840330553 2488023684371098380247915)
      ·
        refine ⟨3732035526556647570371873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2488023684371098380247915 3732035526556647570371873)
        ·
          refine ⟨2799026644917485677778905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3732035526556647570371873 2799026644917485677778905)
          ·
            refine ⟨2099269983688114258334179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2799026644917485677778905 2099269983688114258334179)
            ·
              refine ⟨3148904975532171387501269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2099269983688114258334179 3148904975532171387501269)
              ·
                refine ⟨73802460364035266894561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3148904975532171387501269 73802460364035266894561)
                ·
                  refine ⟨55351845273026450170921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73802460364035266894561 55351845273026450170921)
                  ·
                    rfl

theorem cell20_121272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 2].length) (baseStart_121272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121272 prefixEnd_121272 := by exact prefixLift 121272
  have htrace : WordTrace (prefixWord ++ tailWord_121272) baseStart_121272 baseEnd_121272 := by
    simpa [prefixWord, tailWord_121272, baseEnd_121272] using wordTrace_append hprefix tailTrace_121272
  have hstable : (prefixWord ++ tailWord_121272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121272).length < 2 ^ (prefixWord ++ tailWord_121272).sum := by decide
  have hdescent : baseEnd_121272 < baseStart_121272 := by decide
  rcases family_descends (prefixWord ++ tailWord_121272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121281 : List Nat := [1, 2, 7, 1, 1, 2, 2, 2, 2]
def baseStart_121281 : Nat := 118140960795 + 121281 * 2 ^ 59
def prefixEnd_121281 : Nat := 4983230072969 + 3 ^ 40 * 121281 * 2
def baseEnd_121281 : Nat := 55355953118262418870885

theorem tailTrace_121281 : CollatzResearch.WordTrace tailWord_121281 prefixEnd_121281 55355953118262418870885 := by
  unfold tailWord_121281
  simp only [CollatzResearch.WordTrace]
  refine ⟨4423481473627124990851697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2948987649084749993901131 4423481473627124990851697)
  ·
    refine ⟨3317611105220343743138773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4423481473627124990851697 3317611105220343743138773)
    ·
      refine ⟨77756510278601806479815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 3317611105220343743138773 77756510278601806479815)
      ·
        refine ⟨116634765417902709719723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77756510278601806479815 116634765417902709719723)
        ·
          refine ⟨174952148126854064579585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116634765417902709719723 174952148126854064579585)
          ·
            refine ⟨131214111095140548434689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174952148126854064579585 131214111095140548434689)
            ·
              refine ⟨98410583321355411326017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131214111095140548434689 98410583321355411326017)
              ·
                refine ⟨73807937491016558494513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98410583321355411326017 73807937491016558494513)
                ·
                  refine ⟨55355953118262418870885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73807937491016558494513 55355953118262418870885)
                  ·
                    rfl

theorem cell20_121281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 2].length) (baseStart_121281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_121281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_121281 prefixEnd_121281 := by exact prefixLift 121281
  have htrace : WordTrace (prefixWord ++ tailWord_121281) baseStart_121281 baseEnd_121281 := by
    simpa [prefixWord, tailWord_121281, baseEnd_121281] using wordTrace_append hprefix tailTrace_121281
  have hstable : (prefixWord ++ tailWord_121281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121281).length < 2 ^ (prefixWord ++ tailWord_121281).sum := by decide
  have hdescent : baseEnd_121281 < baseStart_121281 := by decide
  rcases family_descends (prefixWord ++ tailWord_121281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
