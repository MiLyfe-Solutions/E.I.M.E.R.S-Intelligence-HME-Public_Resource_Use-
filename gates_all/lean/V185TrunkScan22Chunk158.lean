import V185TrunkScan22Chunk157

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1409951 : List Nat := [1, 1, 2, 5, 2, 2, 2, 1, 3, 3]
def baseStart_1409951 : Nat := 118140960795 + 1409951 * 2 ^ 59
def prefixEnd_1409951 : Nat := 4983230072969 + 3 ^ 40 * 1409951 * 2
def baseEnd_1409951 : Nat := 482655041525012195952173

theorem tailTrace_1409951 : CollatzResearch.WordTrace tailWord_1409951 prefixEnd_1409951 482655041525012195952173 := by
  unfold tailWord_1409951
  simp only [CollatzResearch.WordTrace]
  refine ⟨51425137714995802304805707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34283425143330534869870471 51425137714995802304805707)
  ·
    refine ⟨77137706572493703457208561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51425137714995802304805707 77137706572493703457208561)
    ·
      refine ⟨57853279929370277592906421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77137706572493703457208561 57853279929370277592906421)
      ·
        refine ⟨5423744993378463524334977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57853279929370277592906421 5423744993378463524334977)
        ·
          refine ⟨4067808745033847643251233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5423744993378463524334977 4067808745033847643251233)
          ·
            refine ⟨3050856558775385732438425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4067808745033847643251233 3050856558775385732438425)
            ·
              refine ⟨2288142419081539299328819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3050856558775385732438425 2288142419081539299328819)
              ·
                refine ⟨3432213628622308948993229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2288142419081539299328819 3432213628622308948993229)
                ·
                  refine ⟨1287080110733365855872461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3432213628622308948993229 1287080110733365855872461)
                  ·
                    refine ⟨482655041525012195952173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1287080110733365855872461 482655041525012195952173)
                    ·
                      rfl

theorem cell22_1409951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 3].length) (baseStart_1409951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1409951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1409951 prefixEnd_1409951 := by exact prefixLift 1409951
  have htrace : WordTrace (prefixWord ++ tailWord_1409951) baseStart_1409951 baseEnd_1409951 := by
    simpa [prefixWord, tailWord_1409951, baseEnd_1409951] using wordTrace_append hprefix tailTrace_1409951
  have hstable : (prefixWord ++ tailWord_1409951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1409951).length < 2 ^ (prefixWord ++ tailWord_1409951).sum := by decide
  have hdescent : baseEnd_1409951 < baseStart_1409951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1409951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410007 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 5, 5]
def baseStart_1410007 : Nat := 118140960795 + 1410007 * 2 ^ 59
def prefixEnd_1410007 : Nat := 4983230072969 + 3 ^ 40 * 1410007 * 2
def baseEnd_1410007 : Nat := 482674211469446716552001

theorem tailTrace_1410007 : CollatzResearch.WordTrace tailWord_1410007 prefixEnd_1410007 482674211469446716552001 := by
  unfold tailWord_1410007
  simp only [CollatzResearch.WordTrace]
  refine ⟨51427180202792923868844275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34284786801861949245896183 51427180202792923868844275)
  ·
    refine ⟨77140770304189385803266413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51427180202792923868844275 77140770304189385803266413)
    ·
      refine ⟨28927788864071019676224905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77140770304189385803266413 28927788864071019676224905)
      ·
        refine ⟨21695841648053264757168679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28927788864071019676224905 21695841648053264757168679)
        ·
          refine ⟨32543762472079897135753019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21695841648053264757168679 32543762472079897135753019)
          ·
            refine ⟨48815643708119845703629529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32543762472079897135753019 48815643708119845703629529)
            ·
              refine ⟨36611732781089884277722147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48815643708119845703629529 36611732781089884277722147)
              ·
                refine ⟨54917599171634826416583221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36611732781089884277722147 54917599171634826416583221)
                ·
                  refine ⟨5148524922340764976554677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54917599171634826416583221 5148524922340764976554677)
                  ·
                    refine ⟨482674211469446716552001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5148524922340764976554677 482674211469446716552001)
                    ·
                      rfl

theorem cell22_1410007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_1410007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410007 prefixEnd_1410007 := by exact prefixLift 1410007
  have htrace : WordTrace (prefixWord ++ tailWord_1410007) baseStart_1410007 baseEnd_1410007 := by
    simpa [prefixWord, tailWord_1410007, baseEnd_1410007] using wordTrace_append hprefix tailTrace_1410007
  have hstable : (prefixWord ++ tailWord_1410007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410007).length < 2 ^ (prefixWord ++ tailWord_1410007).sum := by decide
  have hdescent : baseEnd_1410007 < baseStart_1410007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410009 : List Nat := [1, 2, 1, 2, 5, 1, 3, 1, 6]
def baseStart_1410009 : Nat := 118140960795 + 1410009 * 2 ^ 59
def prefixEnd_1410009 : Nat := 4983230072969 + 3 ^ 40 * 1410009 * 2
def baseEnd_1410009 : Nat := 160891632036773126000665

theorem tailTrace_1410009 : CollatzResearch.WordTrace tailWord_1410009 prefixEnd_1410009 160891632036773126000665 := by
  unfold tailWord_1410009
  simp only [CollatzResearch.WordTrace]
  refine ⟨51427253148785678210417081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34284835432523785473611387 51427253148785678210417081)
  ·
    refine ⟨38570439861589258657812811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51427253148785678210417081 38570439861589258657812811)
    ·
      refine ⟨57855659792383887986719217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38570439861589258657812811 57855659792383887986719217)
      ·
        refine ⟨43391744844287915990039413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57855659792383887986719217 43391744844287915990039413)
        ·
          refine ⟨4067976079151992124066195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43391744844287915990039413 4067976079151992124066195)
          ·
            refine ⟨6101964118727988186099293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4067976079151992124066195 6101964118727988186099293)
            ·
              refine ⟨2288236544522995569787235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6101964118727988186099293 2288236544522995569787235)
              ·
                refine ⟨3432354816784493354680853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2288236544522995569787235 3432354816784493354680853)
                ·
                  refine ⟨160891632036773126000665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3432354816784493354680853 160891632036773126000665)
                  ·
                    rfl

theorem cell22_1410009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 6].length) (baseStart_1410009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410009 prefixEnd_1410009 := by exact prefixLift 1410009
  have htrace : WordTrace (prefixWord ++ tailWord_1410009) baseStart_1410009 baseEnd_1410009 := by
    simpa [prefixWord, tailWord_1410009, baseEnd_1410009] using wordTrace_append hprefix tailTrace_1410009
  have hstable : (prefixWord ++ tailWord_1410009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410009).length < 2 ^ (prefixWord ++ tailWord_1410009).sum := by decide
  have hdescent : baseEnd_1410009 < baseStart_1410009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410058 : List Nat := [3, 1, 2, 2, 3, 2, 2, 2, 2, 3]
def baseStart_1410058 : Nat := 118140960795 + 1410058 * 2 ^ 59
def prefixEnd_1410058 : Nat := 4983230072969 + 3 ^ 40 * 1410058 * 2
def baseEnd_1410058 : Nat := 482691669811699583526845

theorem tailTrace_1410058 : CollatzResearch.WordTrace tailWord_1410058 prefixEnd_1410058 482691669811699583526845 := by
  unfold tailWord_1410058
  simp only [CollatzResearch.WordTrace]
  refine ⟨12857260081402039894737707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34286026883738773052633885 12857260081402039894737707)
  ·
    refine ⟨19285890122103059842106561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12857260081402039894737707 19285890122103059842106561)
    ·
      refine ⟨14464417591577294881579921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19285890122103059842106561 14464417591577294881579921)
      ·
        refine ⟨10848313193682971161184941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14464417591577294881579921 10848313193682971161184941)
        ·
          refine ⟨4068117447631114185444353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10848313193682971161184941 4068117447631114185444353)
          ·
            refine ⟨3051088085723335639083265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4068117447631114185444353 3051088085723335639083265)
            ·
              refine ⟨2288316064292501729312449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3051088085723335639083265 2288316064292501729312449)
              ·
                refine ⟨1716237048219376296984337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2288316064292501729312449 1716237048219376296984337)
                ·
                  refine ⟨1287177786164532222738253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1716237048219376296984337 1287177786164532222738253)
                  ·
                    refine ⟨482691669811699583526845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1287177786164532222738253 482691669811699583526845)
                    ·
                      rfl

theorem cell22_1410058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_1410058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410058 prefixEnd_1410058 := by exact prefixLift 1410058
  have htrace : WordTrace (prefixWord ++ tailWord_1410058) baseStart_1410058 baseEnd_1410058 := by
    simpa [prefixWord, tailWord_1410058, baseEnd_1410058] using wordTrace_append hprefix tailTrace_1410058
  have hstable : (prefixWord ++ tailWord_1410058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410058).length < 2 ^ (prefixWord ++ tailWord_1410058).sum := by decide
  have hdescent : baseEnd_1410058 < baseStart_1410058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410071 : List Nat := [1, 1, 3, 5, 1, 3, 1, 7]
def baseStart_1410071 : Nat := 118140960795 + 1410071 * 2 ^ 59
def prefixEnd_1410071 : Nat := 4983230072969 + 3 ^ 40 * 1410071 * 2
def baseEnd_1410071 : Nat := 53632902219707986994645

theorem tailTrace_1410071 : CollatzResearch.WordTrace tailWord_1410071 prefixEnd_1410071 53632902219707986994645 := by
  unfold tailWord_1410071
  simp only [CollatzResearch.WordTrace]
  refine ⟨51429514474561062799174067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34286342983040708532782711 51429514474561062799174067)
  ·
    refine ⟨77144271711841594198761101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51429514474561062799174067 77144271711841594198761101)
    ·
      refine ⟨28929101891940597824535413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77144271711841594198761101 28929101891940597824535413)
      ·
        refine ⟨2712103302369431046050195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28929101891940597824535413 2712103302369431046050195)
        ·
          refine ⟨4068154953554146569075293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2712103302369431046050195 4068154953554146569075293)
          ·
            refine ⟨1525558107582804963403235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4068154953554146569075293 1525558107582804963403235)
            ·
              refine ⟨2288337161374207445104853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1525558107582804963403235 2288337161374207445104853)
              ·
                refine ⟨53632902219707986994645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2288337161374207445104853 53632902219707986994645)
                ·
                  rfl

theorem cell22_1410071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 7].length) (baseStart_1410071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410071 prefixEnd_1410071 := by exact prefixLift 1410071
  have htrace : WordTrace (prefixWord ++ tailWord_1410071) baseStart_1410071 baseEnd_1410071 := by
    simpa [prefixWord, tailWord_1410071, baseEnd_1410071] using wordTrace_append hprefix tailTrace_1410071
  have hstable : (prefixWord ++ tailWord_1410071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410071).length < 2 ^ (prefixWord ++ tailWord_1410071).sum := by decide
  have hdescent : baseEnd_1410071 < baseStart_1410071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410090 : List Nat := [3, 1, 4, 1, 4, 1, 1, 1, 2, 4]
def baseStart_1410090 : Nat := 118140960795 + 1410090 * 2 ^ 59
def prefixEnd_1410090 : Nat := 4983230072969 + 3 ^ 40 * 1410090 * 2
def baseEnd_1410090 : Nat := 482702624065662166726747

theorem tailTrace_1410090 : CollatzResearch.WordTrace tailWord_1410090 prefixEnd_1410090 482702624065662166726747 := by
  unfold tailWord_1410090
  simp only [CollatzResearch.WordTrace]
  refine ⟨12857551865373057261028931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34286804974328152696077149 12857551865373057261028931)
  ·
    refine ⟨19286327798059585891543397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12857551865373057261028931 19286327798059585891543397)
    ·
      refine ⟨3616186462136172354664387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19286327798059585891543397 3616186462136172354664387)
      ·
        refine ⟨5424279693204258531996581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3616186462136172354664387 5424279693204258531996581)
        ·
          refine ⟨1017052442475798474749359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5424279693204258531996581 1017052442475798474749359)
          ·
            refine ⟨1525578663713697712124039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017052442475798474749359 1525578663713697712124039)
            ·
              refine ⟨2288367995570546568186059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1525578663713697712124039 2288367995570546568186059)
              ·
                refine ⟨3432551993355819852279089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2288367995570546568186059 3432551993355819852279089)
                ·
                  refine ⟨2574413995016864889209317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3432551993355819852279089 2574413995016864889209317)
                  ·
                    refine ⟨482702624065662166726747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2574413995016864889209317 482702624065662166726747)
                    ·
                      rfl

theorem cell22_1410090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_1410090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410090 prefixEnd_1410090 := by exact prefixLift 1410090
  have htrace : WordTrace (prefixWord ++ tailWord_1410090) baseStart_1410090 baseEnd_1410090 := by
    simpa [prefixWord, tailWord_1410090, baseEnd_1410090] using wordTrace_append hprefix tailTrace_1410090
  have hstable : (prefixWord ++ tailWord_1410090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410090).length < 2 ^ (prefixWord ++ tailWord_1410090).sum := by decide
  have hdescent : baseEnd_1410090 < baseStart_1410090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410129 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 5, 4]
def baseStart_1410129 : Nat := 118140960795 + 1410129 * 2 ^ 59
def prefixEnd_1410129 : Nat := 4983230072969 + 3 ^ 40 * 1410129 * 2
def baseEnd_1410129 : Nat := 482715974562679065001627

theorem tailTrace_1410129 : CollatzResearch.WordTrace tailWord_1410129 prefixEnd_1410129 482715974562679065001627 := by
  unfold tailWord_1410129
  simp only [CollatzResearch.WordTrace]
  refine ⟨51431629908350938704785441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34287753272233959136523627 51431629908350938704785441)
  ·
    refine ⟨38573722431263204028589081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51431629908350938704785441 38573722431263204028589081)
    ·
      refine ⟨28930291823447403021441811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38573722431263204028589081 28930291823447403021441811)
      ·
        refine ⟨43395437735171104532162717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28930291823447403021441811 43395437735171104532162717)
        ·
          refine ⟨16273289150689164199561019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43395437735171104532162717 16273289150689164199561019)
          ·
            refine ⟨24409933726033746299341529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16273289150689164199561019 24409933726033746299341529)
            ·
              refine ⟨18307450294525309724506147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24409933726033746299341529 18307450294525309724506147)
              ·
                refine ⟨27461175441787964586759221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18307450294525309724506147 27461175441787964586759221)
                ·
                  refine ⟨2574485197667621680008677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27461175441787964586759221 2574485197667621680008677)
                  ·
                    refine ⟨482715974562679065001627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2574485197667621680008677 482715974562679065001627)
                    ·
                      rfl

theorem cell22_1410129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_1410129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410129 prefixEnd_1410129 := by exact prefixLift 1410129
  have htrace : WordTrace (prefixWord ++ tailWord_1410129) baseStart_1410129 baseEnd_1410129 := by
    simpa [prefixWord, tailWord_1410129, baseEnd_1410129] using wordTrace_append hprefix tailTrace_1410129
  have hstable : (prefixWord ++ tailWord_1410129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410129).length < 2 ^ (prefixWord ++ tailWord_1410129).sum := by decide
  have hdescent : baseEnd_1410129 < baseStart_1410129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410144 : List Nat := [2, 1, 1, 3, 2, 2, 1, 4, 6]
def baseStart_1410144 : Nat := 118140960795 + 1410144 * 2 ^ 59
def prefixEnd_1410144 : Nat := 4983230072969 + 3 ^ 40 * 1410144 * 2
def baseEnd_1410144 : Nat := 160907036456408008625527

theorem tailTrace_1410144 : CollatzResearch.WordTrace tailWord_1410144 prefixEnd_1410144 160907036456408008625527 := by
  unfold tailWord_1410144
  simp only [CollatzResearch.WordTrace]
  refine ⟨25716088501648298133290743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34288118002197730844387657 25716088501648298133290743)
  ·
    refine ⟨38574132752472447199936115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25716088501648298133290743 38574132752472447199936115)
    ·
      refine ⟨57861199128708670799904173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38574132752472447199936115 57861199128708670799904173)
      ·
        refine ⟨21697949673265751549964065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57861199128708670799904173 21697949673265751549964065)
        ·
          refine ⟨16273462254949313662473049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21697949673265751549964065 16273462254949313662473049)
          ·
            refine ⟨12205096691211985246854787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16273462254949313662473049 12205096691211985246854787)
            ·
              refine ⟨18307645036817977870282181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12205096691211985246854787 18307645036817977870282181)
              ·
                refine ⟨3432683444403370850677909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18307645036817977870282181 3432683444403370850677909)
                ·
                  refine ⟨160907036456408008625527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3432683444403370850677909 160907036456408008625527)
                  ·
                    rfl

theorem cell22_1410144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 6].length) (baseStart_1410144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410144 prefixEnd_1410144 := by exact prefixLift 1410144
  have htrace : WordTrace (prefixWord ++ tailWord_1410144) baseStart_1410144 baseEnd_1410144 := by
    simpa [prefixWord, tailWord_1410144, baseEnd_1410144] using wordTrace_append hprefix tailTrace_1410144
  have hstable : (prefixWord ++ tailWord_1410144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410144).length < 2 ^ (prefixWord ++ tailWord_1410144).sum := by decide
  have hdescent : baseEnd_1410144 < baseStart_1410144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410159 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 3, 5]
def baseStart_1410159 : Nat := 118140960795 + 1410159 * 2 ^ 59
def prefixEnd_1410159 : Nat := 4983230072969 + 3 ^ 40 * 1410159 * 2
def baseEnd_1410159 : Nat := 482726244175768986751535

theorem tailTrace_1410159 : CollatzResearch.WordTrace tailWord_1410159 prefixEnd_1410159 482726244175768986751535 := by
  unfold tailWord_1410159
  simp only [CollatzResearch.WordTrace]
  refine ⟨51432724098242253828377531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34288482732161502552251687 51432724098242253828377531)
  ·
    refine ⟨77149086147363380742566297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51432724098242253828377531 77149086147363380742566297)
    ·
      refine ⟨57861814610522535556924723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77149086147363380742566297 57861814610522535556924723)
      ·
        refine ⟨86792721915783803335387085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57861814610522535556924723 86792721915783803335387085)
        ·
          refine ⟨32547270718418926250770157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86792721915783803335387085 32547270718418926250770157)
          ·
            refine ⟨12205226519407097344038809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32547270718418926250770157 12205226519407097344038809)
            ·
              refine ⟨9153919889555323008029107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12205226519407097344038809 9153919889555323008029107)
              ·
                refine ⟨13730879834332984512043661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9153919889555323008029107 13730879834332984512043661)
                ·
                  refine ⟨5149079937874869192016373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13730879834332984512043661 5149079937874869192016373)
                  ·
                    refine ⟨482726244175768986751535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5149079937874869192016373 482726244175768986751535)
                    ·
                      rfl

theorem cell22_1410159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_1410159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410159 prefixEnd_1410159 := by exact prefixLift 1410159
  have htrace : WordTrace (prefixWord ++ tailWord_1410159) baseStart_1410159 baseEnd_1410159 := by
    simpa [prefixWord, tailWord_1410159, baseEnd_1410159] using wordTrace_append hprefix tailTrace_1410159
  have hstable : (prefixWord ++ tailWord_1410159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410159).length < 2 ^ (prefixWord ++ tailWord_1410159).sum := by decide
  have hdescent : baseEnd_1410159 < baseStart_1410159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410161 : List Nat := [1, 2, 2, 2, 1, 1, 2, 7, 4]
def baseStart_1410161 : Nat := 118140960795 + 1410161 * 2 ^ 59
def prefixEnd_1410161 : Nat := 4983230072969 + 3 ^ 40 * 1410161 * 2
def baseEnd_1410161 : Nat := 160908976272213882733843

theorem tailTrace_1410161 : CollatzResearch.WordTrace tailWord_1410161 prefixEnd_1410161 160908976272213882733843 := by
  unfold tailWord_1410161
  simp only [CollatzResearch.WordTrace]
  refine ⟨51432797044235008169950337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34288531362823338779966891 51432797044235008169950337)
  ·
    refine ⟨38574597783176256127462753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51432797044235008169950337 38574597783176256127462753)
    ·
      refine ⟨28930948337382192095597065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38574597783176256127462753 28930948337382192095597065)
      ·
        refine ⟨21698211253036644071697799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28930948337382192095597065 21698211253036644071697799)
        ·
          refine ⟨32547316879554966107546699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21698211253036644071697799 32547316879554966107546699)
          ·
            refine ⟨48820975319332449161320049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32547316879554966107546699 48820975319332449161320049)
            ·
              refine ⟨36615731489499336870990037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48820975319332449161320049 36615731489499336870990037)
              ·
                refine ⟨858181206785140707913829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 36615731489499336870990037 858181206785140707913829)
                ·
                  refine ⟨160908976272213882733843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 858181206785140707913829 160908976272213882733843)
                  ·
                    rfl

theorem cell22_1410161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 4].length) (baseStart_1410161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410161 prefixEnd_1410161 := by exact prefixLift 1410161
  have htrace : WordTrace (prefixWord ++ tailWord_1410161) baseStart_1410161 baseEnd_1410161 := by
    simpa [prefixWord, tailWord_1410161, baseEnd_1410161] using wordTrace_append hprefix tailTrace_1410161
  have hstable : (prefixWord ++ tailWord_1410161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410161).length < 2 ^ (prefixWord ++ tailWord_1410161).sum := by decide
  have hdescent : baseEnd_1410161 < baseStart_1410161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410176 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 4, 3]
def baseStart_1410176 : Nat := 118140960795 + 1410176 * 2 ^ 59
def prefixEnd_1410176 : Nat := 4983230072969 + 3 ^ 40 * 1410176 * 2
def baseEnd_1410176 : Nat := 482732063623186609076483

theorem tailTrace_1410176 : CollatzResearch.WordTrace tailWord_1410176 prefixEnd_1410176 482732063623186609076483 := by
  unfold tailWord_1410176
  simp only [CollatzResearch.WordTrace]
  refine ⟨25716672069590332865873191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34288896092787110487830921 25716672069590332865873191)
  ·
    refine ⟨38575008104385499298809787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25716672069590332865873191 38575008104385499298809787)
    ·
      refine ⟨57862512156578248948214681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38575008104385499298809787 57862512156578248948214681)
      ·
        refine ⟨43396884117433686711161011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57862512156578248948214681 43396884117433686711161011)
        ·
          refine ⟨65095326176150530066741517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43396884117433686711161011 65095326176150530066741517)
          ·
            refine ⟨24410747316056448775028069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65095326176150530066741517 24410747316056448775028069)
            ·
              refine ⟨4577015121760584145317763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24410747316056448775028069 4577015121760584145317763)
              ·
                refine ⟨6865522682640876217976645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4577015121760584145317763 6865522682640876217976645)
                ·
                  refine ⟨1287285502995164290870621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6865522682640876217976645 1287285502995164290870621)
                  ·
                    refine ⟨482732063623186609076483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1287285502995164290870621 482732063623186609076483)
                    ·
                      rfl

theorem cell22_1410176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 4, 3].length) (baseStart_1410176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410176 prefixEnd_1410176 := by exact prefixLift 1410176
  have htrace : WordTrace (prefixWord ++ tailWord_1410176) baseStart_1410176 baseEnd_1410176 := by
    simpa [prefixWord, tailWord_1410176, baseEnd_1410176] using wordTrace_append hprefix tailTrace_1410176
  have hstable : (prefixWord ++ tailWord_1410176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410176).length < 2 ^ (prefixWord ++ tailWord_1410176).sum := by decide
  have hdescent : baseEnd_1410176 < baseStart_1410176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410236 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 2, 6]
def baseStart_1410236 : Nat := 118140960795 + 1410236 * 2 ^ 59
def prefixEnd_1410236 : Nat := 4983230072969 + 3 ^ 40 * 1410236 * 2
def baseEnd_1410236 : Nat := 482752602849366452576299

theorem tailTrace_1410236 : CollatzResearch.WordTrace tailWord_1410236 prefixEnd_1410236 482752602849366452576299 := by
  unfold tailWord_1410236
  simp only [CollatzResearch.WordTrace]
  refine ⟨25717766259481647989465281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34290355012642197319287041 25717766259481647989465281)
  ·
    refine ⟨19288324694611235992098961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25717766259481647989465281 19288324694611235992098961)
    ·
      refine ⟨14466243520958426994074221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19288324694611235992098961 14466243520958426994074221)
      ·
        refine ⟨5424841320359410122777833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14466243520958426994074221 5424841320359410122777833)
        ·
          refine ⟨4068630990269557592083375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5424841320359410122777833 4068630990269557592083375)
          ·
            refine ⟨6102946485404336388125063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4068630990269557592083375 6102946485404336388125063)
            ·
              refine ⟨9154419728106504582187595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6102946485404336388125063 9154419728106504582187595)
              ·
                refine ⟨13731629592159756873281393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9154419728106504582187595 13731629592159756873281393)
                ·
                  refine ⟨10298722194119817654961045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13731629592159756873281393 10298722194119817654961045)
                  ·
                    refine ⟨482752602849366452576299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10298722194119817654961045 482752602849366452576299)
                    ·
                      rfl

theorem cell22_1410236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_1410236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410236 prefixEnd_1410236 := by exact prefixLift 1410236
  have htrace : WordTrace (prefixWord ++ tailWord_1410236) baseStart_1410236 baseEnd_1410236 := by
    simpa [prefixWord, tailWord_1410236, baseEnd_1410236] using wordTrace_append hprefix tailTrace_1410236
  have hstable : (prefixWord ++ tailWord_1410236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410236).length < 2 ^ (prefixWord ++ tailWord_1410236).sum := by decide
  have hdescent : baseEnd_1410236 < baseStart_1410236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410285 : List Nat := [1, 5, 1, 2, 2, 3, 1, 2, 5]
def baseStart_1410285 : Nat := 118140960795 + 1410285 * 2 ^ 59
def prefixEnd_1410285 : Nat := 4983230072969 + 3 ^ 40 * 1410285 * 2
def baseEnd_1410285 : Nat := 160923125516915552700383

theorem tailTrace_1410285 : CollatzResearch.WordTrace tailWord_1410285 prefixEnd_1410285 160923125516915552700383 := by
  unfold tailWord_1410285
  simp only [CollatzResearch.WordTrace]
  refine ⟨51437319695785777347464309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34291546463857184898309539 51437319695785777347464309)
  ·
    refine ⟨4822248721479916626324779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51437319695785777347464309 4822248721479916626324779)
    ·
      refine ⟨7233373082219874939487169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4822248721479916626324779 7233373082219874939487169)
      ·
        refine ⟨5425029811664906204615377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7233373082219874939487169 5425029811664906204615377)
        ·
          refine ⟨4068772358748679653461533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5425029811664906204615377 4068772358748679653461533)
          ·
            refine ⟨1525789634530754870048075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4068772358748679653461533 1525789634530754870048075)
            ·
              refine ⟨2288684451796132305072113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1525789634530754870048075 2288684451796132305072113)
              ·
                refine ⟨1716513338847099228804085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2288684451796132305072113 1716513338847099228804085)
                ·
                  refine ⟨160923125516915552700383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1716513338847099228804085 160923125516915552700383)
                  ·
                    rfl

theorem cell22_1410285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_1410285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410285 prefixEnd_1410285 := by exact prefixLift 1410285
  have htrace : WordTrace (prefixWord ++ tailWord_1410285) baseStart_1410285 baseEnd_1410285 := by
    simpa [prefixWord, tailWord_1410285, baseEnd_1410285] using wordTrace_append hprefix tailTrace_1410285
  have hstable : (prefixWord ++ tailWord_1410285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410285).length < 2 ^ (prefixWord ++ tailWord_1410285).sum := by decide
  have hdescent : baseEnd_1410285 < baseStart_1410285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410328 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 4, 3]
def baseStart_1410328 : Nat := 118140960795 + 1410328 * 2 ^ 59
def prefixEnd_1410328 : Nat := 4983230072969 + 3 ^ 40 * 1410328 * 2
def baseEnd_1410328 : Nat := 482784096329508879276017

theorem tailTrace_1410328 : CollatzResearch.WordTrace tailWord_1410328 prefixEnd_1410328 482784096329508879276017 := by
  unfold tailWord_1410328
  simp only [CollatzResearch.WordTrace]
  refine ⟨25719444017314997845639819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34292592023086663794186425 25719444017314997845639819)
  ·
    refine ⟨38579166025972496768459729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25719444017314997845639819 38579166025972496768459729)
    ·
      refine ⟨28934374519479372576344797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38579166025972496768459729 28934374519479372576344797)
      ·
        refine ⟨10850390444804764716129299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28934374519479372576344797 10850390444804764716129299)
        ·
          refine ⟨16275585667207147074193949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10850390444804764716129299 16275585667207147074193949)
          ·
            refine ⟨6103344625202680152822731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16275585667207147074193949 6103344625202680152822731)
            ·
              refine ⟨9155016937804020229234097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6103344625202680152822731 9155016937804020229234097)
              ·
                refine ⟨6866262703353015171925573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9155016937804020229234097 6866262703353015171925573)
                ·
                  refine ⟨1287424256878690344736045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6866262703353015171925573 1287424256878690344736045)
                  ·
                    refine ⟨482784096329508879276017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1287424256878690344736045 482784096329508879276017)
                    ·
                      rfl

theorem cell22_1410328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 4, 3].length) (baseStart_1410328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410328 prefixEnd_1410328 := by exact prefixLift 1410328
  have htrace : WordTrace (prefixWord ++ tailWord_1410328) baseStart_1410328 baseEnd_1410328 := by
    simpa [prefixWord, tailWord_1410328, baseEnd_1410328] using wordTrace_append hprefix tailTrace_1410328
  have hstable : (prefixWord ++ tailWord_1410328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410328).length < 2 ^ (prefixWord ++ tailWord_1410328).sum := by decide
  have hdescent : baseEnd_1410328 < baseStart_1410328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410330 : List Nat := [3, 1, 1, 3, 3, 1, 3, 3, 4]
def baseStart_1410330 : Nat := 118140960795 + 1410330 * 2 ^ 59
def prefixEnd_1410330 : Nat := 4983230072969 + 3 ^ 40 * 1410330 * 2
def baseEnd_1410330 : Nat := 160928260323460513575337

theorem tailTrace_1410330 : CollatzResearch.WordTrace tailWord_1410330 prefixEnd_1410330 160928260323460513575337 := by
  unfold tailWord_1410330
  simp only [CollatzResearch.WordTrace]
  refine ⟨12859740245155687508213111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34292640653748500021901629 12859740245155687508213111)
  ·
    refine ⟨19289610367733531262319667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12859740245155687508213111 19289610367733531262319667)
    ·
      refine ⟨28934415551600296893479501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19289610367733531262319667 28934415551600296893479501)
      ·
        refine ⟨10850405831850111335054813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28934415551600296893479501 10850405831850111335054813)
        ·
          refine ⟨4068902186943791750645555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10850405831850111335054813 4068902186943791750645555)
          ·
            refine ⟨6103353280415687625968333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4068902186943791750645555 6103353280415687625968333)
            ·
              refine ⟨2288757480155882859738125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6103353280415687625968333 2288757480155882859738125)
              ·
                refine ⟨858284055058456072401797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2288757480155882859738125 858284055058456072401797)
                ·
                  refine ⟨160928260323460513575337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 858284055058456072401797 160928260323460513575337)
                  ·
                    rfl

theorem cell22_1410330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 4].length) (baseStart_1410330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410330 prefixEnd_1410330 := by exact prefixLift 1410330
  have htrace : WordTrace (prefixWord ++ tailWord_1410330) baseStart_1410330 baseEnd_1410330 := by
    simpa [prefixWord, tailWord_1410330, baseEnd_1410330] using wordTrace_append hprefix tailTrace_1410330
  have hstable : (prefixWord ++ tailWord_1410330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410330).length < 2 ^ (prefixWord ++ tailWord_1410330).sum := by decide
  have hdescent : baseEnd_1410330 < baseStart_1410330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410341 : List Nat := [1, 3, 1, 2, 4, 1, 10]
def baseStart_1410341 : Nat := 118140960795 + 1410341 * 2 ^ 59
def prefixEnd_1410341 : Nat := 4983230072969 + 3 ^ 40 * 1410341 * 2
def baseEnd_1410341 : Nat := 17881057277599302914851

theorem tailTrace_1410341 : CollatzResearch.WordTrace tailWord_1410341 prefixEnd_1410341 17881057277599302914851 := by
  unfold tailWord_1410341
  simp only [CollatzResearch.WordTrace]
  refine ⟨51439362183582898911502877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34292908122388599274335251 51439362183582898911502877)
  ·
    refine ⟨19289760818843587091813579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51439362183582898911502877 19289760818843587091813579)
    ·
      refine ⟨28934641228265380637720369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19289760818843587091813579 28934641228265380637720369)
      ·
        refine ⟨21700980921199035478290277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28934641228265380637720369 21700980921199035478290277)
        ·
          refine ⟨4068933922724819152179427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21700980921199035478290277 4068933922724819152179427)
          ·
            refine ⟨6103400884087228728269141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4068933922724819152179427 6103400884087228728269141)
            ·
              refine ⟨17881057277599302914851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6103400884087228728269141 17881057277599302914851)
              ·
                rfl

theorem cell22_1410341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 10].length) (baseStart_1410341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410341 prefixEnd_1410341 := by exact prefixLift 1410341
  have htrace : WordTrace (prefixWord ++ tailWord_1410341) baseStart_1410341 baseEnd_1410341 := by
    simpa [prefixWord, tailWord_1410341, baseEnd_1410341] using wordTrace_append hprefix tailTrace_1410341
  have hstable : (prefixWord ++ tailWord_1410341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410341).length < 2 ^ (prefixWord ++ tailWord_1410341).sum := by decide
  have hdescent : baseEnd_1410341 < baseStart_1410341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410373 : List Nat := [1, 3, 1, 1, 1, 2, 1, 6, 3, 3]
def baseStart_1410373 : Nat := 118140960795 + 1410373 * 2 ^ 59
def prefixEnd_1410373 : Nat := 4983230072969 + 3 ^ 40 * 1410373 * 2
def baseEnd_1410373 : Nat := 482799500749143761900879

theorem tailTrace_1410373 : CollatzResearch.WordTrace tailWord_1410373 prefixEnd_1410373 482799500749143761900879 := by
  unfold tailWord_1410373
  simp only [CollatzResearch.WordTrace]
  refine ⟨51440529319466968376667773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34293686212977978917778515 51440529319466968376667773)
  ·
    refine ⟨19290198494800113141250415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51440529319466968376667773 19290198494800113141250415)
    ·
      refine ⟨28935297742200169711875623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19290198494800113141250415 28935297742200169711875623)
      ·
        refine ⟨43402946613300254567813435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28935297742200169711875623 43402946613300254567813435)
        ·
          refine ⟨65104419919950381851720153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43402946613300254567813435 65104419919950381851720153)
          ·
            refine ⟨48828314939962786388790115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65104419919950381851720153 48828314939962786388790115)
            ·
              refine ⟨73242472409944179583185173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48828314939962786388790115 73242472409944179583185173)
              ·
                refine ⟨3433240894216133417961805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73242472409944179583185173 3433240894216133417961805)
                ·
                  refine ⟨1287465335331050031735677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3433240894216133417961805 1287465335331050031735677)
                  ·
                    refine ⟨482799500749143761900879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1287465335331050031735677 482799500749143761900879)
                    ·
                      rfl

theorem cell22_1410373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 3, 3].length) (baseStart_1410373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410373 prefixEnd_1410373 := by exact prefixLift 1410373
  have htrace : WordTrace (prefixWord ++ tailWord_1410373) baseStart_1410373 baseEnd_1410373 := by
    simpa [prefixWord, tailWord_1410373, baseEnd_1410373] using wordTrace_append hprefix tailTrace_1410373
  have hstable : (prefixWord ++ tailWord_1410373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410373).length < 2 ^ (prefixWord ++ tailWord_1410373).sum := by decide
  have hdescent : baseEnd_1410373 < baseStart_1410373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410401 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 3, 7]
def baseStart_1410401 : Nat := 118140960795 + 1410401 * 2 ^ 59
def prefixEnd_1410401 : Nat := 4983230072969 + 3 ^ 40 * 1410401 * 2
def baseEnd_1410401 : Nat := 482809085721361022200793

theorem tailTrace_1410401 : CollatzResearch.WordTrace tailWord_1410401 prefixEnd_1410401 482809085721361022200793 := by
  unfold tailWord_1410401
  simp only [CollatzResearch.WordTrace]
  refine ⟨51441550563365529158687057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34294367042243686105791371 51441550563365529158687057)
  ·
    refine ⟨38581162922524146869015293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51441550563365529158687057 38581162922524146869015293)
    ·
      refine ⟨14467936095946555075880735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38581162922524146869015293 14467936095946555075880735)
      ·
        refine ⟨21701904143919832613821103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14467936095946555075880735 21701904143919832613821103)
        ·
          refine ⟨32552856215879748920731655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21701904143919832613821103 32552856215879748920731655)
          ·
            refine ⟨48829284323819623381097483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32552856215879748920731655 48829284323819623381097483)
            ·
              refine ⟨73243926485729435071646225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48829284323819623381097483 73243926485729435071646225)
              ·
                refine ⟨54932944864297076303734669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73243926485729435071646225 54932944864297076303734669)
                ·
                  refine ⟨20599854324111403613900501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54932944864297076303734669 20599854324111403613900501)
                  ·
                    refine ⟨482809085721361022200793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20599854324111403613900501 482809085721361022200793)
                    ·
                      rfl

theorem cell22_1410401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_1410401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410401 prefixEnd_1410401 := by exact prefixLift 1410401
  have htrace : WordTrace (prefixWord ++ tailWord_1410401) baseStart_1410401 baseEnd_1410401 := by
    simpa [prefixWord, tailWord_1410401, baseEnd_1410401] using wordTrace_append hprefix tailTrace_1410401
  have hstable : (prefixWord ++ tailWord_1410401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410401).length < 2 ^ (prefixWord ++ tailWord_1410401).sum := by decide
  have hdescent : baseEnd_1410401 < baseStart_1410401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410403 : List Nat := [1, 1, 1, 5, 2, 2, 1, 4, 5]
def baseStart_1410403 : Nat := 118140960795 + 1410403 * 2 ^ 59
def prefixEnd_1410403 : Nat := 4983230072969 + 3 ^ 40 * 1410403 * 2
def baseEnd_1410403 : Nat := 160936590120744561216929

theorem tailTrace_1410403 : CollatzResearch.WordTrace tailWord_1410403 prefixEnd_1410403 160936590120744561216929 := by
  unfold tailWord_1410403
  simp only [CollatzResearch.WordTrace]
  refine ⟨51441623509358283500259863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34294415672905522333506575 51441623509358283500259863)
  ·
    refine ⟨77162435264037425250389795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51441623509358283500259863 77162435264037425250389795)
    ·
      refine ⟨115743652896056137875584693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77162435264037425250389795 115743652896056137875584693)
      ·
        refine ⟨10850967459005262925836065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115743652896056137875584693 10850967459005262925836065)
        ·
          refine ⟨8138225594253947194377049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10850967459005262925836065 8138225594253947194377049)
          ·
            refine ⟨6103669195690460395782787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8138225594253947194377049 6103669195690460395782787)
            ·
              refine ⟨9155503793535690593674181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6103669195690460395782787 9155503793535690593674181)
              ·
                refine ⟨1716656961287941986313909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9155503793535690593674181 1716656961287941986313909)
                ·
                  refine ⟨160936590120744561216929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1716656961287941986313909 160936590120744561216929)
                  ·
                    rfl

theorem cell22_1410403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 5].length) (baseStart_1410403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410403 prefixEnd_1410403 := by exact prefixLift 1410403
  have htrace : WordTrace (prefixWord ++ tailWord_1410403) baseStart_1410403 baseEnd_1410403 := by
    simpa [prefixWord, tailWord_1410403, baseEnd_1410403] using wordTrace_append hprefix tailTrace_1410403
  have hstable : (prefixWord ++ tailWord_1410403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410403).length < 2 ^ (prefixWord ++ tailWord_1410403).sum := by decide
  have hdescent : baseEnd_1410403 < baseStart_1410403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410418 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 2, 5]
def baseStart_1410418 : Nat := 118140960795 + 1410418 * 2 ^ 59
def prefixEnd_1410418 : Nat := 4983230072969 + 3 ^ 40 * 1410418 * 2
def baseEnd_1410418 : Nat := 482814905168778644525741

theorem tailTrace_1410418 : CollatzResearch.WordTrace tailWord_1410418 prefixEnd_1410418 482814905168778644525741 := by
  unfold tailWord_1410418
  simp only [CollatzResearch.WordTrace]
  refine ⟨12860542651075985265513977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34294780402869294041370605 12860542651075985265513977)
  ·
    refine ⟨9645406988306988949135483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12860542651075985265513977 9645406988306988949135483)
    ·
      refine ⟨14468110482460483423703225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9645406988306988949135483 14468110482460483423703225)
      ·
        refine ⟨10851082861845362567777419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14468110482460483423703225 10851082861845362567777419)
        ·
          refine ⟨16276624292768043851666129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10851082861845362567777419 16276624292768043851666129)
          ·
            refine ⟨12207468219576032888749597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16276624292768043851666129 12207468219576032888749597)
            ·
              refine ⟨4577800582341012333281099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12207468219576032888749597 4577800582341012333281099)
              ·
                refine ⟨6866700873511518499921649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4577800582341012333281099 6866700873511518499921649)
                ·
                  refine ⟨5150025655133638874941237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6866700873511518499921649 5150025655133638874941237)
                  ·
                    refine ⟨482814905168778644525741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5150025655133638874941237 482814905168778644525741)
                    ·
                      rfl

theorem cell22_1410418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_1410418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410418 prefixEnd_1410418 := by exact prefixLift 1410418
  have htrace : WordTrace (prefixWord ++ tailWord_1410418) baseStart_1410418 baseEnd_1410418 := by
    simpa [prefixWord, tailWord_1410418, baseEnd_1410418] using wordTrace_append hprefix tailTrace_1410418
  have hstable : (prefixWord ++ tailWord_1410418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410418).length < 2 ^ (prefixWord ++ tailWord_1410418).sum := by decide
  have hdescent : baseEnd_1410418 < baseStart_1410418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410493 : List Nat := [1, 4, 1, 2, 2, 1, 3, 8]
def baseStart_1410493 : Nat := 118140960795 + 1410493 * 2 ^ 59
def prefixEnd_1410493 : Nat := 4983230072969 + 3 ^ 40 * 1410493 * 2
def baseEnd_1410493 : Nat := 53648953244611494322279

theorem tailTrace_1410493 : CollatzResearch.WordTrace tailWord_1410493 prefixEnd_1410493 53648953244611494322279 := by
  unfold tailWord_1410493
  simp only [CollatzResearch.WordTrace]
  refine ⟨51444906079032228871036133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34296604052688152580690755 51444906079032228871036133)
  ·
    refine ⟨9645919889818542913319275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51444906079032228871036133 9645919889818542913319275)
    ·
      refine ⟨14468879834727814369978913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9645919889818542913319275 14468879834727814369978913)
      ·
        refine ⟨10851659876045860777484185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14468879834727814369978913 10851659876045860777484185)
        ·
          refine ⟨8138744907034395583113139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10851659876045860777484185 8138744907034395583113139)
          ·
            refine ⟨12208117360551593374669709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8138744907034395583113139 12208117360551593374669709)
            ·
              refine ⟨4578044010206847515501141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12208117360551593374669709 4578044010206847515501141)
              ·
                refine ⟨53648953244611494322279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4578044010206847515501141 53648953244611494322279)
                ·
                  rfl

theorem cell22_1410493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 8].length) (baseStart_1410493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410493 prefixEnd_1410493 := by exact prefixLift 1410493
  have htrace : WordTrace (prefixWord ++ tailWord_1410493) baseStart_1410493 baseEnd_1410493 := by
    simpa [prefixWord, tailWord_1410493, baseEnd_1410493] using wordTrace_append hprefix tailTrace_1410493
  have hstable : (prefixWord ++ tailWord_1410493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410493).length < 2 ^ (prefixWord ++ tailWord_1410493).sum := by decide
  have hdescent : baseEnd_1410493 < baseStart_1410493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410553 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 4, 5]
def baseStart_1410553 : Nat := 118140960795 + 1410553 * 2 ^ 59
def prefixEnd_1410553 : Nat := 4983230072969 + 3 ^ 40 * 1410553 * 2
def baseEnd_1410553 : Nat := 482861118427683292400327

theorem tailTrace_1410553 : CollatzResearch.WordTrace tailWord_1410553 prefixEnd_1410553 482861118427683292400327 := by
  unfold tailWord_1410553
  simp only [CollatzResearch.WordTrace]
  refine ⟨51447094458814859118220313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34298062972543239412146875 51447094458814859118220313)
  ·
    refine ⟨38585320844111144338665235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51447094458814859118220313 38585320844111144338665235)
    ·
      refine ⟨57877981266166716507997853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38585320844111144338665235 57877981266166716507997853)
      ·
        refine ⟨21704242974812518690499195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57877981266166716507997853 21704242974812518690499195)
        ·
          refine ⟨32556364462218778035748793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21704242974812518690499195 32556364462218778035748793)
          ·
            refine ⟨24417273346664083526811595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32556364462218778035748793 24417273346664083526811595)
            ·
              refine ⟨36625910019996125290217393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24417273346664083526811595 36625910019996125290217393)
              ·
                refine ⟨27469432514997093967663045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36625910019996125290217393 27469432514997093967663045)
                ·
                  refine ⟨5150518596561955118936821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27469432514997093967663045 5150518596561955118936821)
                  ·
                    refine ⟨482861118427683292400327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5150518596561955118936821 482861118427683292400327)
                    ·
                      rfl

theorem cell22_1410553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_1410553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410553 prefixEnd_1410553 := by exact prefixLift 1410553
  have htrace : WordTrace (prefixWord ++ tailWord_1410553) baseStart_1410553 baseEnd_1410553 := by
    simpa [prefixWord, tailWord_1410553, baseEnd_1410553] using wordTrace_append hprefix tailTrace_1410553
  have hstable : (prefixWord ++ tailWord_1410553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410553).length < 2 ^ (prefixWord ++ tailWord_1410553).sum := by decide
  have hdescent : baseEnd_1410553 < baseStart_1410553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410572 : List Nat := [2, 2, 1, 2, 5, 1, 2, 2, 5]
def baseStart_1410572 : Nat := 118140960795 + 1410572 * 2 ^ 59
def prefixEnd_1410572 : Nat := 4983230072969 + 3 ^ 40 * 1410572 * 2
def baseEnd_1410572 : Nat := 160955874171991192058423

theorem tailTrace_1410572 : CollatzResearch.WordTrace tailWord_1410572 prefixEnd_1410572 160955874171991192058423 := by
  unfold tailWord_1410572
  simp only [CollatzResearch.WordTrace]
  refine ⟨25723893722873012681580985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34298524963830683575441313 25723893722873012681580985)
  ·
    refine ⟨19292920292154759511185739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25723893722873012681580985 19292920292154759511185739)
    ·
      refine ⟨28939380438232139266778609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19292920292154759511185739 28939380438232139266778609)
      ·
        refine ⟨21704535328674104450083957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28939380438232139266778609 21704535328674104450083957)
        ·
          refine ⟨2034800187063197292195371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21704535328674104450083957 2034800187063197292195371)
          ·
            refine ⟨3052200280594795938293057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2034800187063197292195371 3052200280594795938293057)
            ·
              refine ⟨2289150210446096953719793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3052200280594795938293057 2289150210446096953719793)
              ·
                refine ⟨1716862657834572715289845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2289150210446096953719793 1716862657834572715289845)
                ·
                  refine ⟨160955874171991192058423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1716862657834572715289845 160955874171991192058423)
                  ·
                    rfl

theorem cell22_1410572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_1410572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410572 prefixEnd_1410572 := by exact prefixLift 1410572
  have htrace : WordTrace (prefixWord ++ tailWord_1410572) baseStart_1410572 baseEnd_1410572 := by
    simpa [prefixWord, tailWord_1410572, baseEnd_1410572] using wordTrace_append hprefix tailTrace_1410572
  have hstable : (prefixWord ++ tailWord_1410572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410572).length < 2 ^ (prefixWord ++ tailWord_1410572).sum := by decide
  have hdescent : baseEnd_1410572 < baseStart_1410572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410602 : List Nat := [3, 1, 4, 1, 1, 1, 2, 4, 1, 4]
def baseStart_1410602 : Nat := 118140960795 + 1410602 * 2 ^ 59
def prefixEnd_1410602 : Nat := 4983230072969 + 3 ^ 40 * 1410602 * 2
def baseEnd_1410602 : Nat := 482877892129063497925177

theorem tailTrace_1410602 : CollatzResearch.WordTrace tailWord_1410602 prefixEnd_1410602 482877892129063497925177 := by
  unfold tailWord_1410602
  simp only [CollatzResearch.WordTrace]
  refine ⟨12862220408909335121688515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34299254423758226991169373 12862220408909335121688515)
  ·
    refine ⟨19293330613364002682532773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12862220408909335121688515 19293330613364002682532773)
    ·
      refine ⟨3617499490005750502974895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19293330613364002682532773 3617499490005750502974895)
      ·
        refine ⟨5426249235008625754462343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3617499490005750502974895 5426249235008625754462343)
        ·
          refine ⟨8139373852512938631693515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5426249235008625754462343 8139373852512938631693515)
          ·
            refine ⟨12209060778769407947540273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8139373852512938631693515 12209060778769407947540273)
            ·
              refine ⟨9156795584077055960655205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12209060778769407947540273 9156795584077055960655205)
              ·
                refine ⟨1716899172014447992622851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9156795584077055960655205 1716899172014447992622851)
                ·
                  refine ⟨2575348758021671988934277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1716899172014447992622851 2575348758021671988934277)
                  ·
                    refine ⟨482877892129063497925177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2575348758021671988934277 482877892129063497925177)
                    ·
                      rfl

theorem cell22_1410602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_1410602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410602 prefixEnd_1410602 := by exact prefixLift 1410602
  have htrace : WordTrace (prefixWord ++ tailWord_1410602) baseStart_1410602 baseEnd_1410602 := by
    simpa [prefixWord, tailWord_1410602, baseEnd_1410602] using wordTrace_append hprefix tailTrace_1410602
  have hstable : (prefixWord ++ tailWord_1410602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410602).length < 2 ^ (prefixWord ++ tailWord_1410602).sum := by decide
  have hdescent : baseEnd_1410602 < baseStart_1410602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410615 : List Nat := [1, 1, 3, 1, 2, 4, 2, 2, 1, 5]
def baseStart_1410615 : Nat := 118140960795 + 1410615 * 2 ^ 59
def prefixEnd_1410615 : Nat := 4983230072969 + 3 ^ 40 * 1410615 * 2
def baseEnd_1410615 : Nat := 482882342294735797350137

theorem tailTrace_1410615 : CollatzResearch.WordTrace tailWord_1410615 prefixEnd_1410615 482882342294735797350137 := by
  unfold tailWord_1410615
  simp only [CollatzResearch.WordTrace]
  refine ⟨51449355784590243706977299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34299570523060162471318199 51449355784590243706977299)
  ·
    refine ⟨77174033676885365560465949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51449355784590243706977299 77174033676885365560465949)
    ·
      refine ⟨28940262628832012085174731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77174033676885365560465949 28940262628832012085174731)
      ·
        refine ⟨43410393943248018127762097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28940262628832012085174731 43410393943248018127762097)
        ·
          refine ⟨32557795457436013595821573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43410393943248018127762097 32557795457436013595821573)
          ·
            refine ⟨6104586648269252549216545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32557795457436013595821573 6104586648269252549216545)
            ·
              refine ⟨4578439986201939411912409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6104586648269252549216545 4578439986201939411912409)
              ·
                refine ⟨3433829989651454558934307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4578439986201939411912409 3433829989651454558934307)
                ·
                  refine ⟨5150744984477181838401461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3433829989651454558934307 5150744984477181838401461)
                  ·
                    refine ⟨482882342294735797350137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5150744984477181838401461 482882342294735797350137)
                    ·
                      rfl

theorem cell22_1410615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_1410615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410615 prefixEnd_1410615 := by exact prefixLift 1410615
  have htrace : WordTrace (prefixWord ++ tailWord_1410615) baseStart_1410615 baseEnd_1410615 := by
    simpa [prefixWord, tailWord_1410615, baseEnd_1410615] using wordTrace_append hprefix tailTrace_1410615
  have hstable : (prefixWord ++ tailWord_1410615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410615).length < 2 ^ (prefixWord ++ tailWord_1410615).sum := by decide
  have hdescent : baseEnd_1410615 < baseStart_1410615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410617 : List Nat := [1, 2, 1, 5, 1, 2, 1, 5, 4]
def baseStart_1410617 : Nat := 118140960795 + 1410617 * 2 ^ 59
def prefixEnd_1410617 : Nat := 4983230072969 + 3 ^ 40 * 1410617 * 2
def baseEnd_1410617 : Nat := 160961008978536152933377

theorem tailTrace_1410617 : CollatzResearch.WordTrace tailWord_1410617 prefixEnd_1410617 160961008978536152933377 := by
  unfold tailWord_1410617
  simp only [CollatzResearch.WordTrace]
  refine ⟨51449428730582998048550105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34299619153721998699033403 51449428730582998048550105)
  ·
    refine ⟨38587071547937248536412579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51449428730582998048550105 38587071547937248536412579)
    ·
      refine ⟨57880607321905872804618869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38587071547937248536412579 57880607321905872804618869)
      ·
        refine ⟨5426306936428675575433019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57880607321905872804618869 5426306936428675575433019)
        ·
          refine ⟨8139460404643013363149529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5426306936428675575433019 8139460404643013363149529)
          ·
            refine ⟨6104595303482260022362147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8139460404643013363149529 6104595303482260022362147)
            ·
              refine ⟨9156892955223390033543221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6104595303482260022362147 9156892955223390033543221)
              ·
                refine ⟨858458714552192815644677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9156892955223390033543221 858458714552192815644677)
                ·
                  refine ⟨160961008978536152933377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 858458714552192815644677 160961008978536152933377)
                  ·
                    rfl

theorem cell22_1410617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 4].length) (baseStart_1410617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410617 prefixEnd_1410617 := by exact prefixLift 1410617
  have htrace : WordTrace (prefixWord ++ tailWord_1410617) baseStart_1410617 baseEnd_1410617 := by
    simpa [prefixWord, tailWord_1410617, baseEnd_1410617] using wordTrace_append hprefix tailTrace_1410617
  have hstable : (prefixWord ++ tailWord_1410617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410617).length < 2 ^ (prefixWord ++ tailWord_1410617).sum := by decide
  have hdescent : baseEnd_1410617 < baseStart_1410617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410797 : List Nat := [1, 5, 1, 2, 1, 3, 9]
def baseStart_1410797 : Nat := 118140960795 + 1410797 * 2 ^ 59
def prefixEnd_1410797 : Nat := 4983230072969 + 3 ^ 40 * 1410797 * 2
def baseEnd_1410797 : Nat := 17886838689412888492577

theorem tailTrace_1410797 : CollatzResearch.WordTrace tailWord_1410797 prefixEnd_1410797 17886838689412888492577 := by
  unfold tailWord_1410797
  simp only [CollatzResearch.WordTrace]
  refine ⟨51455993869930888790102645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34303995913287259193401763 51455993869930888790102645)
  ·
    refine ⟨4823999425306020824072123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51455993869930888790102645 4823999425306020824072123)
    ·
      refine ⟨7235999137959031236108185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4823999425306020824072123 7235999137959031236108185)
      ·
        refine ⟨5426999353469273427081139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7235999137959031236108185 5426999353469273427081139)
        ·
          refine ⟨8140499030203910140621709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5426999353469273427081139 8140499030203910140621709)
          ·
            refine ⟨3052687136326466302733141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8140499030203910140621709 3052687136326466302733141)
            ·
              refine ⟨17886838689412888492577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3052687136326466302733141 17886838689412888492577)
              ·
                rfl

theorem cell22_1410797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 9].length) (baseStart_1410797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410797 prefixEnd_1410797 := by exact prefixLift 1410797
  have htrace : WordTrace (prefixWord ++ tailWord_1410797) baseStart_1410797 baseEnd_1410797 := by
    simpa [prefixWord, tailWord_1410797, baseEnd_1410797] using wordTrace_append hprefix tailTrace_1410797
  have hstable : (prefixWord ++ tailWord_1410797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410797).length < 2 ^ (prefixWord ++ tailWord_1410797).sum := by decide
  have hdescent : baseEnd_1410797 < baseStart_1410797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410801 : List Nat := [1, 2, 2, 2, 2, 5, 1, 2, 2, 3]
def baseStart_1410801 : Nat := 118140960795 + 1410801 * 2 ^ 59
def prefixEnd_1410801 : Nat := 4983230072969 + 3 ^ 40 * 1410801 * 2
def baseEnd_1410801 : Nat := 482946013895893312199567

theorem tailTrace_1410801 : CollatzResearch.WordTrace tailWord_1410801 prefixEnd_1410801 482946013895893312199567 := by
  unfold tailWord_1410801
  simp only [CollatzResearch.WordTrace]
  refine ⟨51456139761916397473248257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34304093174610931648832171 51456139761916397473248257)
  ·
    refine ⟨38592104821437298104936193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51456139761916397473248257 38592104821437298104936193)
    ·
      refine ⟨28944078616077973578702145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38592104821437298104936193 28944078616077973578702145)
      ·
        refine ⟨21708058962058480184026609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28944078616077973578702145 21708058962058480184026609)
        ·
          refine ⟨16281044221543860138019957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21708058962058480184026609 16281044221543860138019957)
          ·
            refine ⟨1526347895769736887939371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16281044221543860138019957 1526347895769736887939371)
            ·
              refine ⟨2289521843654605331909057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1526347895769736887939371 2289521843654605331909057)
              ·
                refine ⟨1717141382740953998931793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2289521843654605331909057 1717141382740953998931793)
                ·
                  refine ⟨1287856037055715499198845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1717141382740953998931793 1287856037055715499198845)
                  ·
                    refine ⟨482946013895893312199567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1287856037055715499198845 482946013895893312199567)
                    ·
                      rfl

theorem cell22_1410801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 2, 3].length) (baseStart_1410801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410801 prefixEnd_1410801 := by exact prefixLift 1410801
  have htrace : WordTrace (prefixWord ++ tailWord_1410801) baseStart_1410801 baseEnd_1410801 := by
    simpa [prefixWord, tailWord_1410801, baseEnd_1410801] using wordTrace_append hprefix tailTrace_1410801
  have hstable : (prefixWord ++ tailWord_1410801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410801).length < 2 ^ (prefixWord ++ tailWord_1410801).sum := by decide
  have hdescent : baseEnd_1410801 < baseStart_1410801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410818 : List Nat := [3, 4, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_1410818 : Nat := 118140960795 + 1410818 * 2 ^ 59
def prefixEnd_1410818 : Nat := 4983230072969 + 3 ^ 40 * 1410818 * 2
def baseEnd_1410818 : Nat := 482951833343310934524515

theorem tailTrace_1410818 : CollatzResearch.WordTrace tailWord_1410818 prefixEnd_1410818 482951833343310934524515 := by
  unfold tailWord_1410818
  simp only [CollatzResearch.WordTrace]
  refine ⟨12864189950713702344154277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34304506535236539584411405 12864189950713702344154277)
  ·
    refine ⟨2412035615758819189528927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12864189950713702344154277 2412035615758819189528927)
    ·
      refine ⟨3618053423638228784293391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2412035615758819189528927 3618053423638228784293391)
      ·
        refine ⟨5427080135457343176440087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3618053423638228784293391 5427080135457343176440087)
        ·
          refine ⟨8140620203186014764660131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5427080135457343176440087 8140620203186014764660131)
          ·
            refine ⟨12210930304779022146990197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8140620203186014764660131 12210930304779022146990197)
            ·
              refine ⟨1144774716073033326280331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12210930304779022146990197 1144774716073033326280331)
              ·
                refine ⟨1717162074109549989420497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1144774716073033326280331 1717162074109549989420497)
                ·
                  refine ⟨1287871555582162492065373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1717162074109549989420497 1287871555582162492065373)
                  ·
                    refine ⟨482951833343310934524515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1287871555582162492065373 482951833343310934524515)
                    ·
                      rfl

theorem cell22_1410818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_1410818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410818 prefixEnd_1410818 := by exact prefixLift 1410818
  have htrace : WordTrace (prefixWord ++ tailWord_1410818) baseStart_1410818 baseEnd_1410818 := by
    simpa [prefixWord, tailWord_1410818, baseEnd_1410818] using wordTrace_append hprefix tailTrace_1410818
  have hstable : (prefixWord ++ tailWord_1410818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410818).length < 2 ^ (prefixWord ++ tailWord_1410818).sum := by decide
  have hdescent : baseEnd_1410818 < baseStart_1410818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410842 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 7]
def baseStart_1410842 : Nat := 118140960795 + 1410842 * 2 ^ 59
def prefixEnd_1410842 : Nat := 4983230072969 + 3 ^ 40 * 1410842 * 2
def baseEnd_1410842 : Nat := 160986683011260957308147

theorem tailTrace_1410842 : CollatzResearch.WordTrace tailWord_1410842 prefixEnd_1410842 160986683011260957308147 := by
  unfold tailWord_1410842
  simp only [CollatzResearch.WordTrace]
  refine ⟨12864408788691965368872695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34305090103178574316993853 12864408788691965368872695)
  ·
    refine ⟨19296613183037948053309043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12864408788691965368872695 19296613183037948053309043)
    ·
      refine ⟨28944919774556922079963565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19296613183037948053309043 28944919774556922079963565)
      ·
        refine ⟨10854344915458845779986337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28944919774556922079963565 10854344915458845779986337)
        ·
          refine ⟨8140758686594134334989753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10854344915458845779986337 8140758686594134334989753)
          ·
            refine ⟨6105569014945600751242315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8140758686594134334989753 6105569014945600751242315)
            ·
              refine ⟨9158353522418401126863473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6105569014945600751242315 9158353522418401126863473)
              ·
                refine ⟨6868765141813800845147605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9158353522418401126863473 6868765141813800845147605)
                ·
                  refine ⟨160986683011260957308147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6868765141813800845147605 160986683011260957308147)
                  ·
                    rfl

theorem cell22_1410842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_1410842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410842 prefixEnd_1410842 := by exact prefixLift 1410842
  have htrace : WordTrace (prefixWord ++ tailWord_1410842) baseStart_1410842 baseEnd_1410842 := by
    simpa [prefixWord, tailWord_1410842, baseEnd_1410842] using wordTrace_append hprefix tailTrace_1410842
  have hstable : (prefixWord ++ tailWord_1410842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410842).length < 2 ^ (prefixWord ++ tailWord_1410842).sum := by decide
  have hdescent : baseEnd_1410842 < baseStart_1410842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410887 : List Nat := [1, 1, 4, 1, 2, 1, 2, 4, 6]
def baseStart_1410887 : Nat := 118140960795 + 1410887 * 2 ^ 59
def prefixEnd_1410887 : Nat := 4983230072969 + 3 ^ 40 * 1410887 * 2
def baseEnd_1410887 : Nat := 160991817817805918183101

theorem tailTrace_1410887 : CollatzResearch.WordTrace tailWord_1410887 prefixEnd_1410887 160991817817805918183101 := by
  unfold tailWord_1410887
  simp only [CollatzResearch.WordTrace]
  refine ⟨51459276439604834160878915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34306184293069889440585943 51459276439604834160878915)
  ·
    refine ⟨77188914659407251241318373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51459276439604834160878915 77188914659407251241318373)
    ·
      refine ⟨14472921498638859607747195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77188914659407251241318373 14472921498638859607747195)
      ·
        refine ⟨21709382247958289411620793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14472921498638859607747195 21709382247958289411620793)
        ·
          refine ⟨16282036685968717058715595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21709382247958289411620793 16282036685968717058715595)
          ·
            refine ⟨24423055028953075588073393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16282036685968717058715595 24423055028953075588073393)
            ·
              refine ⟨18317291271714806691055045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24423055028953075588073393 18317291271714806691055045)
              ·
                refine ⟨3434492113446526254572821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18317291271714806691055045 3434492113446526254572821)
                ·
                  refine ⟨160991817817805918183101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3434492113446526254572821 160991817817805918183101)
                  ·
                    rfl

theorem cell22_1410887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 6].length) (baseStart_1410887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410887 prefixEnd_1410887 := by exact prefixLift 1410887
  have htrace : WordTrace (prefixWord ++ tailWord_1410887) baseStart_1410887 baseEnd_1410887 := by
    simpa [prefixWord, tailWord_1410887, baseEnd_1410887] using wordTrace_append hprefix tailTrace_1410887
  have hstable : (prefixWord ++ tailWord_1410887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410887).length < 2 ^ (prefixWord ++ tailWord_1410887).sum := by decide
  have hdescent : baseEnd_1410887 < baseStart_1410887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410906 : List Nat := [3, 1, 1, 2, 1, 3, 5, 1, 1, 4]
def baseStart_1410906 : Nat := 118140960795 + 1410906 * 2 ^ 59
def prefixEnd_1410906 : Nat := 4983230072969 + 3 ^ 40 * 1410906 * 2
def baseEnd_1410906 : Nat := 482981957541708038324245

theorem tailTrace_1410906 : CollatzResearch.WordTrace tailWord_1410906 prefixEnd_1410906 482981957541708038324245 := by
  unfold tailWord_1410906
  simp only [CollatzResearch.WordTrace]
  refine ⟨12864992356634000101455143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34306646284357333603880381 12864992356634000101455143)
  ·
    refine ⟨19297488534951000152182715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12864992356634000101455143 19297488534951000152182715)
    ·
      refine ⟨28946232802426500228274073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19297488534951000152182715 28946232802426500228274073)
      ·
        refine ⟨21709674601819875171205555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28946232802426500228274073 21709674601819875171205555)
        ·
          refine ⟨32564511902729812756808333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21709674601819875171205555 32564511902729812756808333)
          ·
            refine ⟨12211691963523679783803125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32564511902729812756808333 12211691963523679783803125)
            ·
              refine ⟨1144846121580344979731543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12211691963523679783803125 1144846121580344979731543)
              ·
                refine ⟨1717269182370517469597315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1144846121580344979731543 1717269182370517469597315)
                ·
                  refine ⟨2575903773555776204395973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1717269182370517469597315 2575903773555776204395973)
                  ·
                    refine ⟨482981957541708038324245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2575903773555776204395973 482981957541708038324245)
                    ·
                      rfl

theorem cell22_1410906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 1, 4].length) (baseStart_1410906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410906 prefixEnd_1410906 := by exact prefixLift 1410906
  have htrace : WordTrace (prefixWord ++ tailWord_1410906) baseStart_1410906 baseEnd_1410906 := by
    simpa [prefixWord, tailWord_1410906, baseEnd_1410906] using wordTrace_append hprefix tailTrace_1410906
  have hstable : (prefixWord ++ tailWord_1410906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410906).length < 2 ^ (prefixWord ++ tailWord_1410906).sum := by decide
  have hdescent : baseEnd_1410906 < baseStart_1410906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410917 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 3, 6]
def baseStart_1410917 : Nat := 118140960795 + 1410917 * 2 ^ 59
def prefixEnd_1410917 : Nat := 4983230072969 + 3 ^ 40 * 1410917 * 2
def baseEnd_1410917 : Nat := 482985723066507676299211

theorem tailTrace_1410917 : CollatzResearch.WordTrace tailWord_1410917 prefixEnd_1410917 482985723066507676299211 := by
  unfold tailWord_1410917
  simp only [CollatzResearch.WordTrace]
  refine ⟨51460370629496149284471005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34306913752997432856314003 51460370629496149284471005)
  ·
    refine ⟨19297638986061055981676627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51460370629496149284471005 19297638986061055981676627)
    ·
      refine ⟨28946458479091583972514941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19297638986061055981676627 28946458479091583972514941)
      ·
        refine ⟨10854921929659343989693103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28946458479091583972514941 10854921929659343989693103)
        ·
          refine ⟨16282382894489015984539655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10854921929659343989693103 16282382894489015984539655)
          ·
            refine ⟨24423574341733523976809483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16282382894489015984539655 24423574341733523976809483)
            ·
              refine ⟨36635361512600285965214225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24423574341733523976809483 36635361512600285965214225)
              ·
                refine ⟨27476521134450214473910669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36635361512600285965214225 27476521134450214473910669)
                ·
                  refine ⟨10303695425418830427716501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27476521134450214473910669 10303695425418830427716501)
                  ·
                    refine ⟨482985723066507676299211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10303695425418830427716501 482985723066507676299211)
                    ·
                      rfl

theorem cell22_1410917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_1410917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410917 prefixEnd_1410917 := by exact prefixLift 1410917
  have htrace : WordTrace (prefixWord ++ tailWord_1410917) baseStart_1410917 baseEnd_1410917 := by
    simpa [prefixWord, tailWord_1410917, baseEnd_1410917] using wordTrace_append hprefix tailTrace_1410917
  have hstable : (prefixWord ++ tailWord_1410917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410917).length < 2 ^ (prefixWord ++ tailWord_1410917).sum := by decide
  have hdescent : baseEnd_1410917 < baseStart_1410917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410949 : List Nat := [1, 3, 1, 1, 3, 2, 5, 6]
def baseStart_1410949 : Nat := 118140960795 + 1410949 * 2 ^ 59
def prefixEnd_1410949 : Nat := 4983230072969 + 3 ^ 40 * 1410949 * 2
def baseEnd_1410949 : Nat := 53666297480052251055457

theorem tailTrace_1410949 : CollatzResearch.WordTrace tailWord_1410949 prefixEnd_1410949 53666297480052251055457 := by
  unfold tailWord_1410949
  simp only [CollatzResearch.WordTrace]
  refine ⟨51461537765380218749635901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34307691843586812499757267 51461537765380218749635901)
  ·
    refine ⟨19298076662017582031113463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51461537765380218749635901 19298076662017582031113463)
    ·
      refine ⟨28947114993026373046670195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19298076662017582031113463 28947114993026373046670195)
      ·
        refine ⟨43420672489539559570005293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28947114993026373046670195 43420672489539559570005293)
        ·
          refine ⟨16282752183577334838751985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43420672489539559570005293 16282752183577334838751985)
          ·
            refine ⟨12212064137683001129063989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16282752183577334838751985 12212064137683001129063989)
            ·
              refine ⟨1144881012907781355849749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12212064137683001129063989 1144881012907781355849749)
              ·
                refine ⟨53666297480052251055457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1144881012907781355849749 53666297480052251055457)
                ·
                  rfl

theorem cell22_1410949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 6].length) (baseStart_1410949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410949 prefixEnd_1410949 := by exact prefixLift 1410949
  have htrace : WordTrace (prefixWord ++ tailWord_1410949) baseStart_1410949 baseEnd_1410949 := by
    simpa [prefixWord, tailWord_1410949, baseEnd_1410949] using wordTrace_append hprefix tailTrace_1410949
  have hstable : (prefixWord ++ tailWord_1410949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410949).length < 2 ^ (prefixWord ++ tailWord_1410949).sum := by decide
  have hdescent : baseEnd_1410949 < baseStart_1410949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1410994 : List Nat := [3, 2, 1, 1, 1, 1, 1, 7, 5]
def baseStart_1410994 : Nat := 118140960795 + 1410994 * 2 ^ 59
def prefixEnd_1410994 : Nat := 4983230072969 + 3 ^ 40 * 1410994 * 2
def baseEnd_1410994 : Nat := 161004027246701714041325

theorem tailTrace_1410994 : CollatzResearch.WordTrace tailWord_1410994 prefixEnd_1410994 161004027246701714041325 := by
  unfold tailWord_1410994
  simp only [CollatzResearch.WordTrace]
  refine ⟨12865794762554297858756009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34308786033478127623349357 12865794762554297858756009)
  ·
    refine ⟨9649346071915723394067007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12865794762554297858756009 9649346071915723394067007)
    ·
      refine ⟨14474019107873585091100511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9649346071915723394067007 14474019107873585091100511)
      ·
        refine ⟨21711028661810377636650767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14474019107873585091100511 21711028661810377636650767)
        ·
          refine ⟨32566542992715566454976151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21711028661810377636650767 32566542992715566454976151)
          ·
            refine ⟨48849814489073349682464227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32566542992715566454976151 48849814489073349682464227)
            ·
              refine ⟨73274721733610024523696341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48849814489073349682464227 73274721733610024523696341)
              ·
                refine ⟨1717376290631484949774133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 73274721733610024523696341 1717376290631484949774133)
                ·
                  refine ⟨161004027246701714041325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1717376290631484949774133 161004027246701714041325)
                  ·
                    rfl

theorem cell22_1410994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_1410994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1410994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1410994 prefixEnd_1410994 := by exact prefixLift 1410994
  have htrace : WordTrace (prefixWord ++ tailWord_1410994) baseStart_1410994 baseEnd_1410994 := by
    simpa [prefixWord, tailWord_1410994, baseEnd_1410994] using wordTrace_append hprefix tailTrace_1410994
  have hstable : (prefixWord ++ tailWord_1410994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1410994).length < 2 ^ (prefixWord ++ tailWord_1410994).sum := by decide
  have hdescent : baseEnd_1410994 < baseStart_1410994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1410994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411069 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_1411069 : Nat := 118140960795 + 1411069 * 2 ^ 59
def prefixEnd_1411069 : Nat := 4983230072969 + 3 ^ 40 * 1411069 * 2
def baseEnd_1411069 : Nat := 483037755772829946498745

theorem tailTrace_1411069 : CollatzResearch.WordTrace tailWord_1411069 prefixEnd_1411069 483037755772829946498745 := by
  unfold tailWord_1411069
  simp only [CollatzResearch.WordTrace]
  refine ⟨51465914524945479244004261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34310609683296986162669507 51465914524945479244004261)
  ·
    refine ⟨9649858973427277358250799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51465914524945479244004261 9649858973427277358250799)
    ·
      refine ⟨14474788460140916037376199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9649858973427277358250799 14474788460140916037376199)
      ·
        refine ⟨21712182690211374056064299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14474788460140916037376199 21712182690211374056064299)
        ·
          refine ⟨32568274035317061084096449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21712182690211374056064299 32568274035317061084096449)
          ·
            refine ⟨24426205526487795813072337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32568274035317061084096449 24426205526487795813072337)
            ·
              refine ⟨18319654144865846859804253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24426205526487795813072337 18319654144865846859804253)
              ·
                refine ⟨6869870304324692572426595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18319654144865846859804253 6869870304324692572426595)
                ·
                  refine ⟨10304805456487038858639893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6869870304324692572426595 10304805456487038858639893)
                  ·
                    refine ⟨483037755772829946498745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10304805456487038858639893 483037755772829946498745)
                    ·
                      rfl

theorem cell22_1411069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_1411069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411069 prefixEnd_1411069 := by exact prefixLift 1411069
  have htrace : WordTrace (prefixWord ++ tailWord_1411069) baseStart_1411069 baseEnd_1411069 := by
    simpa [prefixWord, tailWord_1411069, baseEnd_1411069] using wordTrace_append hprefix tailTrace_1411069
  have hstable : (prefixWord ++ tailWord_1411069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411069).length < 2 ^ (prefixWord ++ tailWord_1411069).sum := by decide
  have hdescent : baseEnd_1411069 < baseStart_1411069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411086 : List Nat := [4, 1, 1, 2, 2, 1, 1, 4, 2, 4]
def baseStart_1411086 : Nat := 118140960795 + 1411086 * 2 ^ 59
def prefixEnd_1411086 : Nat := 4983230072969 + 3 ^ 40 * 1411086 * 2
def baseEnd_1411086 : Nat := 483043575220247568823693

theorem tailTrace_1411086 : CollatzResearch.WordTrace tailWord_1411086 prefixEnd_1411086 483043575220247568823693 := by
  unfold tailWord_1411086
  simp only [CollatzResearch.WordTrace]
  refine ⟨6433316820735486393421639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34311023043922594098248741 6433316820735486393421639)
  ·
    refine ⟨9649975231103229590132459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6433316820735486393421639 9649975231103229590132459)
    ·
      refine ⟨14474962846654844385198689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9649975231103229590132459 14474962846654844385198689)
      ·
        refine ⟨10856222134991133288899017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14474962846654844385198689 10856222134991133288899017)
        ·
          refine ⟨8142166601243349966674263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10856222134991133288899017 8142166601243349966674263)
          ·
            refine ⟨12213249901865024950011395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8142166601243349966674263 12213249901865024950011395)
            ·
              refine ⟨18319874852797537425017093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12213249901865024950011395 18319874852797537425017093)
              ·
                refine ⟨3434976534899538267190705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18319874852797537425017093 3434976534899538267190705)
                ·
                  refine ⟨2576232401174653700393029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3434976534899538267190705 2576232401174653700393029)
                  ·
                    refine ⟨483043575220247568823693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2576232401174653700393029 483043575220247568823693)
                    ·
                      rfl

theorem cell22_1411086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_1411086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411086 prefixEnd_1411086 := by exact prefixLift 1411086
  have htrace : WordTrace (prefixWord ++ tailWord_1411086) baseStart_1411086 baseEnd_1411086 := by
    simpa [prefixWord, tailWord_1411086, baseEnd_1411086] using wordTrace_append hprefix tailTrace_1411086
  have hstable : (prefixWord ++ tailWord_1411086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411086).length < 2 ^ (prefixWord ++ tailWord_1411086).sum := by decide
  have hdescent : baseEnd_1411086 < baseStart_1411086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411101 : List Nat := [1, 4, 2, 2, 2, 1, 3, 7]
def baseStart_1411101 : Nat := 118140960795 + 1411101 * 2 ^ 59
def prefixEnd_1411101 : Nat := 4983230072969 + 3 ^ 40 * 1411101 * 2
def baseEnd_1411101 : Nat := 53672078891865836633183

theorem tailTrace_1411101 : CollatzResearch.WordTrace tailWord_1411101 prefixEnd_1411101 53672078891865836633183 := by
  unfold tailWord_1411101
  simp only [CollatzResearch.WordTrace]
  refine ⟨51467081660829548709169157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34311387773886365806112771 51467081660829548709169157)
  ·
    refine ⟨9650077811405540382969217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51467081660829548709169157 9650077811405540382969217)
    ·
      refine ⟨7237558358554155287226913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9650077811405540382969217 7237558358554155287226913)
      ·
        refine ⟨5428168768915616465420185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7237558358554155287226913 5428168768915616465420185)
        ·
          refine ⟨4071126576686712349065139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5428168768915616465420185 4071126576686712349065139)
          ·
            refine ⟨6106689865030068523597709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4071126576686712349065139 6106689865030068523597709)
            ·
              refine ⟨2290008699386275696349141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6106689865030068523597709 2290008699386275696349141)
              ·
                refine ⟨53672078891865836633183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2290008699386275696349141 53672078891865836633183)
                ·
                  rfl

theorem cell22_1411101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 7].length) (baseStart_1411101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411101 prefixEnd_1411101 := by exact prefixLift 1411101
  have htrace : WordTrace (prefixWord ++ tailWord_1411101) baseStart_1411101 baseEnd_1411101 := by
    simpa [prefixWord, tailWord_1411101, baseEnd_1411101] using wordTrace_append hprefix tailTrace_1411101
  have hstable : (prefixWord ++ tailWord_1411101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411101).length < 2 ^ (prefixWord ++ tailWord_1411101).sum := by decide
  have hdescent : baseEnd_1411101 < baseStart_1411101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411118 : List Nat := [4, 1, 3, 1, 1, 3, 3, 6]
def baseStart_1411118 : Nat := 118140960795 + 1411118 * 2 ^ 59
def prefixEnd_1411118 : Nat := 4983230072969 + 3 ^ 40 * 1411118 * 2
def baseEnd_1411118 : Nat := 53672725497134461335955

theorem tailTrace_1411118 : CollatzResearch.WordTrace tailWord_1411118 prefixEnd_1411118 53672725497134461335955 := by
  unfold tailWord_1411118
  simp only [CollatzResearch.WordTrace]
  refine ⟨6433462712720995076567251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34311801134511973741692005 6433462712720995076567251)
  ·
    refine ⟨9650194069081492614850877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6433462712720995076567251 9650194069081492614850877)
    ·
      refine ⟨3618822775905559730569079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9650194069081492614850877 3618822775905559730569079)
      ·
        refine ⟨5428234163858339595853619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3618822775905559730569079 5428234163858339595853619)
        ·
          refine ⟨8142351245787509393780429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5428234163858339595853619 8142351245787509393780429)
          ·
            refine ⟨3053381717170316022667661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8142351245787509393780429 3053381717170316022667661)
            ·
              refine ⟨1145018143938868508500373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3053381717170316022667661 1145018143938868508500373)
              ·
                refine ⟨53672725497134461335955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1145018143938868508500373 53672725497134461335955)
                ·
                  rfl

theorem cell22_1411118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_1411118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411118 prefixEnd_1411118 := by exact prefixLift 1411118
  have htrace : WordTrace (prefixWord ++ tailWord_1411118) baseStart_1411118 baseEnd_1411118 := by
    simpa [prefixWord, tailWord_1411118, baseEnd_1411118] using wordTrace_append hprefix tailTrace_1411118
  have hstable : (prefixWord ++ tailWord_1411118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411118).length < 2 ^ (prefixWord ++ tailWord_1411118).sum := by decide
  have hdescent : baseEnd_1411118 < baseStart_1411118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411150 : List Nat := [4, 1, 1, 1, 1, 4, 2, 4, 1, 3]
def baseStart_1411150 : Nat := 118140960795 + 1411150 * 2 ^ 59
def prefixEnd_1411150 : Nat := 4983230072969 + 3 ^ 40 * 1411150 * 2
def baseEnd_1411150 : Nat := 483065483728172735223497

theorem tailTrace_1411150 : CollatzResearch.WordTrace tailWord_1411150 prefixEnd_1411150 483065483728172735223497 := by
  unfold tailWord_1411150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6433608604706503759712863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34312579225101353385135269 6433608604706503759712863)
  ·
    refine ⟨9650412907059755639569295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6433608604706503759712863 9650412907059755639569295)
    ·
      refine ⟨14475619360589633459353943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9650412907059755639569295 14475619360589633459353943)
      ·
        refine ⟨21713429040884450189030915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14475619360589633459353943 21713429040884450189030915)
        ·
          refine ⟨32570143561326675283546373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21713429040884450189030915 32570143561326675283546373)
          ·
            refine ⟨6106901917748751615664945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32570143561326675283546373 6106901917748751615664945)
            ·
              refine ⟨4580176438311563711748709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6106901917748751615664945 4580176438311563711748709)
              ·
                refine ⟨858783082183418195952883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4580176438311563711748709 858783082183418195952883)
                ·
                  refine ⟨1288174623275127293929325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 858783082183418195952883 1288174623275127293929325)
                  ·
                    refine ⟨483065483728172735223497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1288174623275127293929325 483065483728172735223497)
                    ·
                      rfl

theorem cell22_1411150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_1411150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411150 prefixEnd_1411150 := by exact prefixLift 1411150
  have htrace : WordTrace (prefixWord ++ tailWord_1411150) baseStart_1411150 baseEnd_1411150 := by
    simpa [prefixWord, tailWord_1411150, baseEnd_1411150] using wordTrace_append hprefix tailTrace_1411150
  have hstable : (prefixWord ++ tailWord_1411150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411150).length < 2 ^ (prefixWord ++ tailWord_1411150).sum := by decide
  have hdescent : baseEnd_1411150 < baseStart_1411150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411193 : List Nat := [1, 2, 1, 3, 4, 1, 2, 3, 1, 4]
def baseStart_1411193 : Nat := 118140960795 + 1411193 * 2 ^ 59
def prefixEnd_1411193 : Nat := 4983230072969 + 3 ^ 40 * 1411193 * 2
def baseEnd_1411193 : Nat := 483080203506934956398365

theorem tailTrace_1411193 : CollatzResearch.WordTrace tailWord_1411193 prefixEnd_1411193 483080203506934956398365 := by
  unfold tailWord_1411193
  simp only [CollatzResearch.WordTrace]
  refine ⟨51470437176496248421518233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34313624784330832281012155 51470437176496248421518233)
  ·
    refine ⟨38602827882372186316138675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51470437176496248421518233 38602827882372186316138675)
    ·
      refine ⟨57904241823558279474208013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38602827882372186316138675 57904241823558279474208013)
      ·
        refine ⟨21714090683834354802828005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57904241823558279474208013 21714090683834354802828005)
        ·
          refine ⟨4071392003218941525530251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21714090683834354802828005 4071392003218941525530251)
          ·
            refine ⟨6107088004828412288295377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4071392003218941525530251 6107088004828412288295377)
            ·
              refine ⟨4580316003621309216221533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6107088004828412288295377 4580316003621309216221533)
              ·
                refine ⟨1717618501357990956083075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4580316003621309216221533 1717618501357990956083075)
                ·
                  refine ⟨2576427752036986434124613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1717618501357990956083075 2576427752036986434124613)
                  ·
                    refine ⟨483080203506934956398365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2576427752036986434124613 483080203506934956398365)
                    ·
                      rfl

theorem cell22_1411193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 4].length) (baseStart_1411193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411193 prefixEnd_1411193 := by exact prefixLift 1411193
  have htrace : WordTrace (prefixWord ++ tailWord_1411193) baseStart_1411193 baseEnd_1411193 := by
    simpa [prefixWord, tailWord_1411193, baseEnd_1411193] using wordTrace_append hprefix tailTrace_1411193
  have hstable : (prefixWord ++ tailWord_1411193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411193).length < 2 ^ (prefixWord ++ tailWord_1411193).sum := by decide
  have hdescent : baseEnd_1411193 < baseStart_1411193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411208 : List Nat := [2, 1, 3, 4, 1, 1, 3, 1, 6]
def baseStart_1411208 : Nat := 118140960795 + 1411208 * 2 ^ 59
def prefixEnd_1411208 : Nat := 4983230072969 + 3 ^ 40 * 1411208 * 2
def baseEnd_1411208 : Nat := 161028446104493305757773

theorem tailTrace_1411208 : CollatzResearch.WordTrace tailWord_1411208 prefixEnd_1411208 161028446104493305757773 := by
  unfold tailWord_1411208
  simp only [CollatzResearch.WordTrace]
  refine ⟨25735492135720952991657139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34313989514294603988876185 25735492135720952991657139)
  ·
    refine ⟨38603238203581429487485709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25735492135720952991657139 38603238203581429487485709)
    ·
      refine ⟨14476214326343036057807141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38603238203581429487485709 14476214326343036057807141)
      ·
        refine ⟨2714290186189319260838839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14476214326343036057807141 2714290186189319260838839)
        ·
          refine ⟨4071435279283978891258259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2714290186189319260838839 4071435279283978891258259)
          ·
            refine ⟨6107152918925968336887389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4071435279283978891258259 6107152918925968336887389)
            ·
              refine ⟨2290182344597238126332771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6107152918925968336887389 2290182344597238126332771)
              ·
                refine ⟨3435273516895857189499157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2290182344597238126332771 3435273516895857189499157)
                ·
                  refine ⟨161028446104493305757773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3435273516895857189499157 161028446104493305757773)
                  ·
                    rfl

theorem cell22_1411208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 6].length) (baseStart_1411208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411208 prefixEnd_1411208 := by exact prefixLift 1411208
  have htrace : WordTrace (prefixWord ++ tailWord_1411208) baseStart_1411208 baseEnd_1411208 := by
    simpa [prefixWord, tailWord_1411208, baseEnd_1411208] using wordTrace_append hprefix tailTrace_1411208
  have hstable : (prefixWord ++ tailWord_1411208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411208).length < 2 ^ (prefixWord ++ tailWord_1411208).sum := by decide
  have hdescent : baseEnd_1411208 < baseStart_1411208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411221 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 4, 4]
def baseStart_1411221 : Nat := 118140960795 + 1411221 * 2 ^ 59
def prefixEnd_1411221 : Nat := 4983230072969 + 3 ^ 40 * 1411221 * 2
def baseEnd_1411221 : Nat := 483089788479152216698279

theorem tailTrace_1411221 : CollatzResearch.WordTrace tailWord_1411221 prefixEnd_1411221 483089788479152216698279 := by
  unfold tailWord_1411221
  simp only [CollatzResearch.WordTrace]
  refine ⟨51471458420394809203537517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34314305613596539469025011 51471458420394809203537517)
  ·
    refine ⟨19301796907648053451326569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51471458420394809203537517 19301796907648053451326569)
    ·
      refine ⟨14476347680736040088494927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19301796907648053451326569 14476347680736040088494927)
      ·
        refine ⟨21714521521104060132742391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14476347680736040088494927 21714521521104060132742391)
        ·
          refine ⟨32571782281656090199113587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21714521521104060132742391 32571782281656090199113587)
          ·
            refine ⟨48857673422484135298670381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32571782281656090199113587 48857673422484135298670381)
            ·
              refine ⟨18321627533431550737001393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48857673422484135298670381 18321627533431550737001393)
              ·
                refine ⟨13741220650073663052751045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18321627533431550737001393 13741220650073663052751045)
                ·
                  refine ⟨2576478871888811822390821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13741220650073663052751045 2576478871888811822390821)
                  ·
                    refine ⟨483089788479152216698279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2576478871888811822390821 483089788479152216698279)
                    ·
                      rfl

theorem cell22_1411221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_1411221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411221 prefixEnd_1411221 := by exact prefixLift 1411221
  have htrace : WordTrace (prefixWord ++ tailWord_1411221) baseStart_1411221 baseEnd_1411221 := by
    simpa [prefixWord, tailWord_1411221, baseEnd_1411221] using wordTrace_append hprefix tailTrace_1411221
  have hstable : (prefixWord ++ tailWord_1411221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411221).length < 2 ^ (prefixWord ++ tailWord_1411221).sum := by decide
  have hdescent : baseEnd_1411221 < baseStart_1411221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411253 : List Nat := [1, 3, 3, 4, 1, 10]
def baseStart_1411253 : Nat := 118140960795 + 1411253 * 2 ^ 59
def prefixEnd_1411253 : Nat := 4983230072969 + 3 ^ 40 * 1411253 * 2
def baseEnd_1411253 : Nat := 5964206700408824690101

theorem tailTrace_1411253 : CollatzResearch.WordTrace tailWord_1411253 prefixEnd_1411253 5964206700408824690101 := by
  unfold tailWord_1411253
  simp only [CollatzResearch.WordTrace]
  refine ⟨51472625556278878668702413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34315083704185919112468275 51472625556278878668702413)
  ·
    refine ⟨19302234583604579500763405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51472625556278878668702413 19302234583604579500763405)
    ·
      refine ⟨7238337968851717312786277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19302234583604579500763405 7238337968851717312786277)
      ·
        refine ⟨1357188369159696996147427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7238337968851717312786277 1357188369159696996147427)
        ·
          refine ⟨2035782553739545494221141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1357188369159696996147427 2035782553739545494221141)
          ·
            refine ⟨5964206700408824690101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2035782553739545494221141 5964206700408824690101)
            ·
              rfl

theorem cell22_1411253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 10].length) (baseStart_1411253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411253 prefixEnd_1411253 := by exact prefixLift 1411253
  have htrace : WordTrace (prefixWord ++ tailWord_1411253) baseStart_1411253 baseEnd_1411253 := by
    simpa [prefixWord, tailWord_1411253, baseEnd_1411253] using wordTrace_append hprefix tailTrace_1411253
  have hstable : (prefixWord ++ tailWord_1411253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411253).length < 2 ^ (prefixWord ++ tailWord_1411253).sum := by decide
  have hdescent : baseEnd_1411253 < baseStart_1411253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411296 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 1, 7]
def baseStart_1411296 : Nat := 118140960795 + 1411296 * 2 ^ 59
def prefixEnd_1411296 : Nat := 4983230072969 + 3 ^ 40 * 1411296 * 2
def baseEnd_1411296 : Nat := 483115462511877021073049

theorem tailTrace_1411296 : CollatzResearch.WordTrace tailWord_1411296 prefixEnd_1411296 483115462511877021073049 := by
  unfold tailWord_1411296
  simp only [CollatzResearch.WordTrace]
  refine ⟨25737096947561548506258871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34316129263415398008345161 25737096947561548506258871)
  ·
    refine ⟨38605645421342322759388307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25737096947561548506258871 38605645421342322759388307)
    ·
      refine ⟨57908468132013484139082461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38605645421342322759388307 57908468132013484139082461)
      ·
        refine ⟨21715675549505056552155923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57908468132013484139082461 21715675549505056552155923)
        ·
          refine ⟨32573513324257584828233885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21715675549505056552155923 32573513324257584828233885)
          ·
            refine ⟨12215067496596594310587707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32573513324257584828233885 12215067496596594310587707)
            ·
              refine ⟨18322601244894891465881561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12215067496596594310587707 18322601244894891465881561)
              ·
                refine ⟨13741950933671168599411171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18322601244894891465881561 13741950933671168599411171)
                ·
                  refine ⟨20612926400506752899116757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13741950933671168599411171 20612926400506752899116757)
                  ·
                    refine ⟨483115462511877021073049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20612926400506752899116757 483115462511877021073049)
                    ·
                      rfl

theorem cell22_1411296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_1411296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411296 prefixEnd_1411296 := by exact prefixLift 1411296
  have htrace : WordTrace (prefixWord ++ tailWord_1411296) baseStart_1411296 baseEnd_1411296 := by
    simpa [prefixWord, tailWord_1411296, baseEnd_1411296] using wordTrace_append hprefix tailTrace_1411296
  have hstable : (prefixWord ++ tailWord_1411296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411296).length < 2 ^ (prefixWord ++ tailWord_1411296).sum := by decide
  have hdescent : baseEnd_1411296 < baseStart_1411296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411330 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_1411330 : Nat := 118140960795 + 1411330 * 2 ^ 59
def prefixEnd_1411330 : Nat := 4983230072969 + 3 ^ 40 * 1411330 * 2
def baseEnd_1411330 : Nat := 483127101406712265722945

theorem tailTrace_1411330 : CollatzResearch.WordTrace tailWord_1411330 prefixEnd_1411330 483127101406712265722945 := by
  unfold tailWord_1411330
  simp only [CollatzResearch.WordTrace]
  refine ⟨12868858494249980204813861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34316955984666613879503629 12868858494249980204813861)
  ·
    refine ⟨2412910967671871288402599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12868858494249980204813861 2412910967671871288402599)
    ·
      refine ⟨3619366451507806932603899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2412910967671871288402599 3619366451507806932603899)
      ·
        refine ⟨5429049677261710398905849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3619366451507806932603899 5429049677261710398905849)
        ·
          refine ⟨4071787257946282799179387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5429049677261710398905849 4071787257946282799179387)
          ·
            refine ⟨6107680886919424198769081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4071787257946282799179387 6107680886919424198769081)
            ·
              refine ⟨4580760665189568149076811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6107680886919424198769081 4580760665189568149076811)
              ·
                refine ⟨6871140997784352223615217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4580760665189568149076811 6871140997784352223615217)
                ·
                  refine ⟨5153355748338264167711413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6871140997784352223615217 5153355748338264167711413)
                  ·
                    refine ⟨483127101406712265722945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5153355748338264167711413 483127101406712265722945)
                    ·
                      rfl

theorem cell22_1411330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_1411330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411330 prefixEnd_1411330 := by exact prefixLift 1411330
  have htrace : WordTrace (prefixWord ++ tailWord_1411330) baseStart_1411330 baseEnd_1411330 := by
    simpa [prefixWord, tailWord_1411330, baseEnd_1411330] using wordTrace_append hprefix tailTrace_1411330
  have hstable : (prefixWord ++ tailWord_1411330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411330).length < 2 ^ (prefixWord ++ tailWord_1411330).sum := by decide
  have hdescent : baseEnd_1411330 < baseStart_1411330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411332 : List Nat := [2, 3, 2, 2, 3, 1, 3, 1, 5]
def baseStart_1411332 : Nat := 118140960795 + 1411332 * 2 ^ 59
def prefixEnd_1411332 : Nat := 4983230072969 + 3 ^ 40 * 1411332 * 2
def baseEnd_1411332 : Nat := 161042595349194975724313

theorem tailTrace_1411332 : CollatzResearch.WordTrace tailWord_1411332 prefixEnd_1411332 161042595349194975724313 := by
  unfold tailWord_1411332
  simp only [CollatzResearch.WordTrace]
  refine ⟨25737753461496337580414125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34317004615328450107218833 25737753461496337580414125)
  ·
    refine ⟨9651657548061126592655297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25737753461496337580414125 9651657548061126592655297)
    ·
      refine ⟨7238743161045844944491473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9651657548061126592655297 7238743161045844944491473)
      ·
        refine ⟨5429057370784383708368605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7238743161045844944491473 5429057370784383708368605)
        ·
          refine ⟨2035896514044143890638227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5429057370784383708368605 2035896514044143890638227)
          ·
            refine ⟨3053844771066215835957341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035896514044143890638227 3053844771066215835957341)
            ·
              refine ⟨1145191789149830938484003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3053844771066215835957341 1145191789149830938484003)
              ·
                refine ⟨1717787683724746407726005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1145191789149830938484003 1717787683724746407726005)
                ·
                  refine ⟨161042595349194975724313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1717787683724746407726005 161042595349194975724313)
                  ·
                    rfl

theorem cell22_1411332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_1411332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411332 prefixEnd_1411332 := by exact prefixLift 1411332
  have htrace : WordTrace (prefixWord ++ tailWord_1411332) baseStart_1411332 baseEnd_1411332 := by
    simpa [prefixWord, tailWord_1411332, baseEnd_1411332] using wordTrace_append hprefix tailTrace_1411332
  have hstable : (prefixWord ++ tailWord_1411332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411332).length < 2 ^ (prefixWord ++ tailWord_1411332).sum := by decide
  have hdescent : baseEnd_1411332 < baseStart_1411332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411345 : List Nat := [1, 2, 2, 1, 1, 6, 2, 2, 1, 4]
def baseStart_1411345 : Nat := 118140960795 + 1411345 * 2 ^ 59
def prefixEnd_1411345 : Nat := 4983230072969 + 3 ^ 40 * 1411345 * 2
def baseEnd_1411345 : Nat := 483132236213257226597899

theorem tailTrace_1411345 : CollatzResearch.WordTrace tailWord_1411345 prefixEnd_1411345 483132236213257226597899 := by
  unfold tailWord_1411345
  simp only [CollatzResearch.WordTrace]
  refine ⟨51475981071945578381051489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34317320714630385587367659 51475981071945578381051489)
  ·
    refine ⟨38606985803959183785788617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51475981071945578381051489 38606985803959183785788617)
    ·
      refine ⟨28955239352969387839341463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38606985803959183785788617 28955239352969387839341463)
      ·
        refine ⟨43432859029454081759012195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28955239352969387839341463 43432859029454081759012195)
        ·
          refine ⟨65149288544181122638518293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43432859029454081759012195 65149288544181122638518293)
          ·
            refine ⟨3053872900508490123680545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65149288544181122638518293 3053872900508490123680545)
            ·
              refine ⟨2290404675381367592760409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3053872900508490123680545 2290404675381367592760409)
              ·
                refine ⟨1717803506536025694570307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2290404675381367592760409 1717803506536025694570307)
                ·
                  refine ⟨2576705259804038541855461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1717803506536025694570307 2576705259804038541855461)
                  ·
                    refine ⟨483132236213257226597899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2576705259804038541855461 483132236213257226597899)
                    ·
                      rfl

theorem cell22_1411345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_1411345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411345 prefixEnd_1411345 := by exact prefixLift 1411345
  have htrace : WordTrace (prefixWord ++ tailWord_1411345) baseStart_1411345 baseEnd_1411345 := by
    simpa [prefixWord, tailWord_1411345, baseEnd_1411345] using wordTrace_append hprefix tailTrace_1411345
  have hstable : (prefixWord ++ tailWord_1411345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411345).length < 2 ^ (prefixWord ++ tailWord_1411345).sum := by decide
  have hdescent : baseEnd_1411345 < baseStart_1411345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411377 : List Nat := [1, 2, 2, 3, 5, 1, 1, 1, 6]
def baseStart_1411377 : Nat := 118140960795 + 1411377 * 2 ^ 59
def prefixEnd_1411377 : Nat := 4983230072969 + 3 ^ 40 * 1411377 * 2
def baseEnd_1411377 : Nat := 161047730155739936599267

theorem tailTrace_1411377 : CollatzResearch.WordTrace tailWord_1411377 prefixEnd_1411377 161047730155739936599267 := by
  unfold tailWord_1411377
  simp only [CollatzResearch.WordTrace]
  refine ⟨51477148207829647846216385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34318098805219765230810923 51477148207829647846216385)
  ·
    refine ⟨38607861155872235884662289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51477148207829647846216385 38607861155872235884662289)
    ·
      refine ⟨28955895866904176913496717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38607861155872235884662289 28955895866904176913496717)
      ·
        refine ⟨10858460950089066342561269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28955895866904176913496717 10858460950089066342561269)
        ·
          refine ⟨1017980714070849969615119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10858460950089066342561269 1017980714070849969615119)
          ·
            refine ⟨1526971071106274954422679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017980714070849969615119 1526971071106274954422679)
            ·
              refine ⟨2290456606659412431634019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1526971071106274954422679 2290456606659412431634019)
              ·
                refine ⟨3435684909989118647451029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2290456606659412431634019 3435684909989118647451029)
                ·
                  refine ⟨161047730155739936599267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3435684909989118647451029 161047730155739936599267)
                  ·
                    rfl

theorem cell22_1411377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 6].length) (baseStart_1411377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411377 prefixEnd_1411377 := by exact prefixLift 1411377
  have htrace : WordTrace (prefixWord ++ tailWord_1411377) baseStart_1411377 baseEnd_1411377 := by
    simpa [prefixWord, tailWord_1411377, baseEnd_1411377] using wordTrace_append hprefix tailTrace_1411377
  have hstable : (prefixWord ++ tailWord_1411377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411377).length < 2 ^ (prefixWord ++ tailWord_1411377).sum := by decide
  have hdescent : baseEnd_1411377 < baseStart_1411377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411388 : List Nat := [2, 2, 2, 2, 1, 2, 4, 7]
def baseStart_1411388 : Nat := 118140960795 + 1411388 * 2 ^ 59
def prefixEnd_1411388 : Nat := 4983230072969 + 3 ^ 40 * 1411388 * 2
def baseEnd_1411388 : Nat := 53682995110224383085863

theorem tailTrace_1411388 : CollatzResearch.WordTrace tailWord_1411388 prefixEnd_1411388 53682995110224383085863 := by
  unfold tailWord_1411388
  simp only [CollatzResearch.WordTrace]
  refine ⟨25738774705394898362433409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34318366273859864483244545 25738774705394898362433409)
  ·
    refine ⟨19304081029046173771825057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25738774705394898362433409 19304081029046173771825057)
    ·
      refine ⟨14478060771784630328868793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19304081029046173771825057 14478060771784630328868793)
      ·
        refine ⟨10858545578838472746651595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14478060771784630328868793 10858545578838472746651595)
        ·
          refine ⟨16287818368257709119977393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10858545578838472746651595 16287818368257709119977393)
          ·
            refine ⟨12215863776193281839983045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16287818368257709119977393 12215863776193281839983045)
            ·
              refine ⟨2290474458036240344996821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12215863776193281839983045 2290474458036240344996821)
              ·
                refine ⟨53682995110224383085863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2290474458036240344996821 53682995110224383085863)
                ·
                  rfl

theorem cell22_1411388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 7].length) (baseStart_1411388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411388 prefixEnd_1411388 := by exact prefixLift 1411388
  have htrace : WordTrace (prefixWord ++ tailWord_1411388) baseStart_1411388 baseEnd_1411388 := by
    simpa [prefixWord, tailWord_1411388, baseEnd_1411388] using wordTrace_append hprefix tailTrace_1411388
  have hstable : (prefixWord ++ tailWord_1411388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411388).length < 2 ^ (prefixWord ++ tailWord_1411388).sum := by decide
  have hdescent : baseEnd_1411388 < baseStart_1411388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411396 : List Nat := [2, 3, 4, 1, 3, 1, 1, 2, 1, 4]
def baseStart_1411396 : Nat := 118140960795 + 1411396 * 2 ^ 59
def prefixEnd_1411396 : Nat := 4983230072969 + 3 ^ 40 * 1411396 * 2
def baseEnd_1411396 : Nat := 483149694555510093572743

theorem tailTrace_1411396 : CollatzResearch.WordTrace tailWord_1411396 prefixEnd_1411396 483149694555510093572743 := by
  unfold tailWord_1411396
  simp only [CollatzResearch.WordTrace]
  refine ⟨25738920597380407045579021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34318560796507209394105361 25738920597380407045579021)
  ·
    refine ⟨9652095224017652642092133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25738920597380407045579021 9652095224017652642092133)
    ·
      refine ⟨1809767854503309870392275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9652095224017652642092133 1809767854503309870392275)
      ·
        refine ⟨2714651781754964805588413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1809767854503309870392275 2714651781754964805588413)
        ·
          refine ⟨1017994418158111802095655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2714651781754964805588413 1017994418158111802095655)
          ·
            refine ⟨1526991627237167703143483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017994418158111802095655 1526991627237167703143483)
            ·
              refine ⟨2290487440855751554715225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1526991627237167703143483 2290487440855751554715225)
              ·
                refine ⟨1717865580641813666036419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2290487440855751554715225 1717865580641813666036419)
                ·
                  refine ⟨2576798370962720499054629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1717865580641813666036419 2576798370962720499054629)
                  ·
                    refine ⟨483149694555510093572743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2576798370962720499054629 483149694555510093572743)
                    ·
                      rfl

theorem cell22_1411396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_1411396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411396 prefixEnd_1411396 := by exact prefixLift 1411396
  have htrace : WordTrace (prefixWord ++ tailWord_1411396) baseStart_1411396 baseEnd_1411396 := by
    simpa [prefixWord, tailWord_1411396, baseEnd_1411396] using wordTrace_append hprefix tailTrace_1411396
  have hstable : (prefixWord ++ tailWord_1411396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411396).length < 2 ^ (prefixWord ++ tailWord_1411396).sum := by decide
  have hdescent : baseEnd_1411396 < baseStart_1411396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411495 : List Nat := [1, 1, 6, 1, 1, 2, 1, 3, 6]
def baseStart_1411495 : Nat := 118140960795 + 1411495 * 2 ^ 59
def prefixEnd_1411495 : Nat := 4983230072969 + 3 ^ 40 * 1411495 * 2
def baseEnd_1411495 : Nat := 161061194759568945115813

theorem tailTrace_1411495 : CollatzResearch.WordTrace tailWord_1411495 prefixEnd_1411495 161061194759568945115813 := by
  unfold tailWord_1411495
  simp only [CollatzResearch.WordTrace]
  refine ⟨51481452021402153999011939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34320968014268102666007959 51481452021402153999011939)
  ·
    refine ⟨77222178032103230998517909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51481452021402153999011939 77222178032103230998517909)
    ·
      refine ⟨3619789595254838953055527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77222178032103230998517909 3619789595254838953055527)
      ·
        refine ⟨5429684392882258429583291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3619789595254838953055527 5429684392882258429583291)
        ·
          refine ⟨8144526589323387644374937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5429684392882258429583291 8144526589323387644374937)
          ·
            refine ⟨6108394941992540733281203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8144526589323387644374937 6108394941992540733281203)
            ·
              refine ⟨9162592412988811099921805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6108394941992540733281203 9162592412988811099921805)
              ·
                refine ⟨3435972154870804162470677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9162592412988811099921805 3435972154870804162470677)
                ·
                  refine ⟨161061194759568945115813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3435972154870804162470677 161061194759568945115813)
                  ·
                    rfl

theorem cell22_1411495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 6].length) (baseStart_1411495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411495 prefixEnd_1411495 := by exact prefixLift 1411495
  have htrace : WordTrace (prefixWord ++ tailWord_1411495) baseStart_1411495 baseEnd_1411495 := by
    simpa [prefixWord, tailWord_1411495, baseEnd_1411495] using wordTrace_append hprefix tailTrace_1411495
  have hstable : (prefixWord ++ tailWord_1411495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411495).length < 2 ^ (prefixWord ++ tailWord_1411495).sum := by decide
  have hdescent : baseEnd_1411495 < baseStart_1411495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411540 : List Nat := [2, 4, 1, 2, 2, 1, 10]
def baseStart_1411540 : Nat := 118140960795 + 1411540 * 2 ^ 59
def prefixEnd_1411540 : Nat := 4983230072969 + 3 ^ 40 * 1411540 * 2
def baseEnd_1411540 : Nat := 17896258840679322887863

theorem tailTrace_1411540 : CollatzResearch.WordTrace tailWord_1411540 prefixEnd_1411540 17896258840679322887863 := by
  unfold tailWord_1411540
  simp only [CollatzResearch.WordTrace]
  refine ⟨25741546653119563342200037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34322062204159417789600049 25741546653119563342200037)
  ·
    refine ⟨4826539997459918126662507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25741546653119563342200037 4826539997459918126662507)
    ·
      refine ⟨7239809996189877189993761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4826539997459918126662507 7239809996189877189993761)
      ·
        refine ⟨5429857497142407892495321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7239809996189877189993761 5429857497142407892495321)
        ·
          refine ⟨4072393122856805919371491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5429857497142407892495321 4072393122856805919371491)
          ·
            refine ⟨6108589684285208879057237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4072393122856805919371491 6108589684285208879057237)
            ·
              refine ⟨17896258840679322887863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6108589684285208879057237 17896258840679322887863)
              ·
                rfl

theorem cell22_1411540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 10].length) (baseStart_1411540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411540 prefixEnd_1411540 := by exact prefixLift 1411540
  have htrace : WordTrace (prefixWord ++ tailWord_1411540) baseStart_1411540 baseEnd_1411540 := by
    simpa [prefixWord, tailWord_1411540, baseEnd_1411540] using wordTrace_append hprefix tailTrace_1411540
  have hstable : (prefixWord ++ tailWord_1411540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411540).length < 2 ^ (prefixWord ++ tailWord_1411540).sum := by decide
  have hdescent : baseEnd_1411540 < baseStart_1411540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411557 : List Nat := [1, 3, 1, 5, 2, 1, 2, 7]
def baseStart_1411557 : Nat := 118140960795 + 1411557 * 2 ^ 59
def prefixEnd_1411557 : Nat := 4983230072969 + 3 ^ 40 * 1411557 * 2
def baseEnd_1411557 : Nat := 53689423127306593366361

theorem tailTrace_1411557 : CollatzResearch.WordTrace tailWord_1411557 prefixEnd_1411557 53689423127306593366361 := by
  unfold tailWord_1411557
  simp only [CollatzResearch.WordTrace]
  refine ⟨51483713347177538587768925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34322475564785025725179283 51483713347177538587768925)
  ·
    refine ⟨19306392505191576970413347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51483713347177538587768925 19306392505191576970413347)
    ·
      refine ⟨28959588757787365455620021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19306392505191576970413347 28959588757787365455620021)
      ·
        refine ⟨2714961446042565511464377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28959588757787365455620021 2714961446042565511464377)
        ·
          refine ⟨2036221084531924133598283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2714961446042565511464377 2036221084531924133598283)
          ·
            refine ⟨3054331626797886200397425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2036221084531924133598283 3054331626797886200397425)
            ·
              refine ⟨2290748720098414650298069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3054331626797886200397425 2290748720098414650298069)
              ·
                refine ⟨53689423127306593366361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2290748720098414650298069 53689423127306593366361)
                ·
                  rfl

theorem cell22_1411557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 7].length) (baseStart_1411557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411557 prefixEnd_1411557 := by exact prefixLift 1411557
  have htrace : WordTrace (prefixWord ++ tailWord_1411557) baseStart_1411557 baseEnd_1411557 := by
    simpa [prefixWord, tailWord_1411557, baseEnd_1411557] using wordTrace_append hprefix tailTrace_1411557
  have hstable : (prefixWord ++ tailWord_1411557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411557).length < 2 ^ (prefixWord ++ tailWord_1411557).sum := by decide
  have hdescent : baseEnd_1411557 < baseStart_1411557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411649 : List Nat := [1, 2, 5, 1, 1, 3, 1, 3, 1, 4]
def baseStart_1411649 : Nat := 118140960795 + 1411649 * 2 ^ 59
def prefixEnd_1411649 : Nat := 4983230072969 + 3 ^ 40 * 1411649 * 2
def baseEnd_1411649 : Nat := 483236301625901766996967

theorem tailTrace_1411649 : CollatzResearch.WordTrace tailWord_1411649 prefixEnd_1411649 483236301625901766996967 := by
  unfold tailWord_1411649
  simp only [CollatzResearch.WordTrace]
  refine ⟨51487068862844238300118001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34324712575229492200078667 51487068862844238300118001)
  ·
    refine ⟨38615301647133178725088501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51487068862844238300118001 38615301647133178725088501)
    ·
      refine ⟨3620184529418735505477047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38615301647133178725088501 3620184529418735505477047)
      ·
        refine ⟨5430276794128103258215571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3620184529418735505477047 5430276794128103258215571)
        ·
          refine ⟨8145415191192154887323357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5430276794128103258215571 8145415191192154887323357)
          ·
            refine ⟨3054530696697058082746259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8145415191192154887323357 3054530696697058082746259)
            ·
              refine ⟨4581796045045587124119389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3054530696697058082746259 4581796045045587124119389)
              ·
                refine ⟨1718173516892095171544771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4581796045045587124119389 1718173516892095171544771)
                ·
                  refine ⟨2577260275338142757317157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1718173516892095171544771 2577260275338142757317157)
                  ·
                    refine ⟨483236301625901766996967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2577260275338142757317157 483236301625901766996967)
                    ·
                      rfl

theorem cell22_1411649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_1411649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411649 prefixEnd_1411649 := by exact prefixLift 1411649
  have htrace : WordTrace (prefixWord ++ tailWord_1411649) baseStart_1411649 baseEnd_1411649 := by
    simpa [prefixWord, tailWord_1411649, baseEnd_1411649] using wordTrace_append hprefix tailTrace_1411649
  have hstable : (prefixWord ++ tailWord_1411649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411649).length < 2 ^ (prefixWord ++ tailWord_1411649).sum := by decide
  have hdescent : baseEnd_1411649 < baseStart_1411649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411692 : List Nat := [2, 2, 1, 1, 3, 1, 6, 6]
def baseStart_1411692 : Nat := 118140960795 + 1411692 * 2 ^ 59
def prefixEnd_1411692 : Nat := 4983230072969 + 3 ^ 40 * 1411692 * 2
def baseEnd_1411692 : Nat := 53694557933851554241315

theorem tailTrace_1411692 : CollatzResearch.WordTrace tailWord_1411692 prefixEnd_1411692 53694557933851554241315 := by
  unfold tailWord_1411692
  simp only [CollatzResearch.WordTrace]
  refine ⟨25744318600844228321966665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34325758134458971095955553 25744318600844228321966665)
  ·
    refine ⟨19308238950633171241474999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25744318600844228321966665 19308238950633171241474999)
    ·
      refine ⟨28962358425949756862212499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19308238950633171241474999 28962358425949756862212499)
      ·
        refine ⟨43443537638924635293318749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28962358425949756862212499 43443537638924635293318749)
        ·
          refine ⟨16291326614596738234994531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43443537638924635293318749 16291326614596738234994531)
          ·
            refine ⟨24436989921895107352491797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16291326614596738234994531 24436989921895107352491797)
            ·
              refine ⟨1145483902588833157148053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24436989921895107352491797 1145483902588833157148053)
              ·
                refine ⟨53694557933851554241315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1145483902588833157148053 53694557933851554241315)
                ·
                  rfl

theorem cell22_1411692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 6].length) (baseStart_1411692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411692 prefixEnd_1411692 := by exact prefixLift 1411692
  have htrace : WordTrace (prefixWord ++ tailWord_1411692) baseStart_1411692 baseEnd_1411692 := by
    simpa [prefixWord, tailWord_1411692, baseEnd_1411692] using wordTrace_append hprefix tailTrace_1411692
  have hstable : (prefixWord ++ tailWord_1411692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411692).length < 2 ^ (prefixWord ++ tailWord_1411692).sum := by decide
  have hdescent : baseEnd_1411692 < baseStart_1411692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411698 : List Nat := [3, 2, 1, 2, 5, 1, 1, 3, 4]
def baseStart_1411698 : Nat := 118140960795 + 1411698 * 2 ^ 59
def prefixEnd_1411698 : Nat := 4983230072969 + 3 ^ 40 * 1411698 * 2
def baseEnd_1411698 : Nat := 161084358442427324173939

theorem tailTrace_1411698 : CollatzResearch.WordTrace tailWord_1411698 prefixEnd_1411698 161084358442427324173939 := by
  unfold tailWord_1411698
  simp only [CollatzResearch.WordTrace]
  refine ⟨12872214009916679917162937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34325904026444479779101165 12872214009916679917162937)
  ·
    refine ⟨9654160507437509937872203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12872214009916679917162937 9654160507437509937872203)
    ·
      refine ⟨14481240761156264906808305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9654160507437509937872203 14481240761156264906808305)
      ·
        refine ⟨10860930570867198680106229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14481240761156264906808305 10860930570867198680106229)
        ·
          refine ⟨1018212241018799876259959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10860930570867198680106229 1018212241018799876259959)
          ·
            refine ⟨1527318361528199814389939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018212241018799876259959 1527318361528199814389939)
            ·
              refine ⟨2290977542292299721584909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1527318361528199814389939 2290977542292299721584909)
              ·
                refine ⟨859116578359612395594341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2290977542292299721584909 859116578359612395594341)
                ·
                  refine ⟨161084358442427324173939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 859116578359612395594341 161084358442427324173939)
                  ·
                    rfl

theorem cell22_1411698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_1411698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411698 prefixEnd_1411698 := by exact prefixLift 1411698
  have htrace : WordTrace (prefixWord ++ tailWord_1411698) baseStart_1411698 baseEnd_1411698 := by
    simpa [prefixWord, tailWord_1411698, baseEnd_1411698] using wordTrace_append hprefix tailTrace_1411698
  have hstable : (prefixWord ++ tailWord_1411698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411698).length < 2 ^ (prefixWord ++ tailWord_1411698).sum := by decide
  have hdescent : baseEnd_1411698 < baseStart_1411698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411709 : List Nat := [1, 4, 1, 1, 6, 1, 8]
def baseStart_1411709 : Nat := 118140960795 + 1411709 * 2 ^ 59
def prefixEnd_1411709 : Nat := 4983230072969 + 3 ^ 40 * 1411709 * 2
def baseEnd_1411709 : Nat := 17898401513040059648029

theorem tailTrace_1411709 : CollatzResearch.WordTrace tailWord_1411709 prefixEnd_1411709 17898401513040059648029 := by
  unfold tailWord_1411709
  simp only [CollatzResearch.WordTrace]
  refine ⟨51489257242626868547302181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34326171495084579031534787 51489257242626868547302181)
  ·
    refine ⟨9654235732992537852619159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51489257242626868547302181 9654235732992537852619159)
    ·
      refine ⟨14481353599488806778928739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9654235732992537852619159 14481353599488806778928739)
      ·
        refine ⟨21722030399233210168393109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14481353599488806778928739 21722030399233210168393109)
        ·
          refine ⟨1018220174964056726643427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21722030399233210168393109 1018220174964056726643427)
          ·
            refine ⟨1527330262446085089965141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018220174964056726643427 1527330262446085089965141)
            ·
              refine ⟨17898401513040059648029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1527330262446085089965141 17898401513040059648029)
              ·
                rfl

theorem cell22_1411709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 8].length) (baseStart_1411709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411709 prefixEnd_1411709 := by exact prefixLift 1411709
  have htrace : WordTrace (prefixWord ++ tailWord_1411709) baseStart_1411709 baseEnd_1411709 := by
    simpa [prefixWord, tailWord_1411709, baseEnd_1411709] using wordTrace_append hprefix tailTrace_1411709
  have hstable : (prefixWord ++ tailWord_1411709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411709).length < 2 ^ (prefixWord ++ tailWord_1411709).sum := by decide
  have hdescent : baseEnd_1411709 < baseStart_1411709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411737 : List Nat := [1, 2, 1, 2, 1, 2, 5, 3, 5]
def baseStart_1411737 : Nat := 118140960795 + 1411737 * 2 ^ 59
def prefixEnd_1411737 : Nat := 4983230072969 + 3 ^ 40 * 1411737 * 2
def baseEnd_1411737 : Nat := 161088808608099623598899

theorem tailTrace_1411737 : CollatzResearch.WordTrace tailWord_1411737 prefixEnd_1411737 161088808608099623598899 := by
  unfold tailWord_1411737
  simp only [CollatzResearch.WordTrace]
  refine ⟨51490278486525429329321465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34326852324350286219547643 51490278486525429329321465)
  ·
    refine ⟨38617708864894071996991099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51490278486525429329321465 38617708864894071996991099)
    ·
      refine ⟨57926563297341107995486649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38617708864894071996991099 57926563297341107995486649)
      ·
        refine ⟨43444922473005830996614987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57926563297341107995486649 43444922473005830996614987)
        ·
          refine ⟨65167383709508746494922481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43444922473005830996614987 65167383709508746494922481)
          ·
            refine ⟨48875537782131559871191861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65167383709508746494922481 48875537782131559871191861)
            ·
              refine ⟨4582081667074833737924237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48875537782131559871191861 4582081667074833737924237)
              ·
                refine ⟨1718280625153062651721589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4582081667074833737924237 1718280625153062651721589)
                ·
                  refine ⟨161088808608099623598899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1718280625153062651721589 161088808608099623598899)
                  ·
                    rfl

theorem cell22_1411737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 5].length) (baseStart_1411737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411737 prefixEnd_1411737 := by exact prefixLift 1411737
  have htrace : WordTrace (prefixWord ++ tailWord_1411737) baseStart_1411737 baseEnd_1411737 := by
    simpa [prefixWord, tailWord_1411737, baseEnd_1411737] using wordTrace_append hprefix tailTrace_1411737
  have hstable : (prefixWord ++ tailWord_1411737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411737).length < 2 ^ (prefixWord ++ tailWord_1411737).sum := by decide
  have hdescent : baseEnd_1411737 < baseStart_1411737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411848 : List Nat := [2, 1, 3, 2, 2, 3, 3, 1, 2, 3]
def baseStart_1411848 : Nat := 118140960795 + 1411848 * 2 ^ 59
def prefixEnd_1411848 : Nat := 4983230072969 + 3 ^ 40 * 1411848 * 2
def baseEnd_1411848 : Nat := 483304423392731581271357

theorem tailTrace_1411848 : CollatzResearch.WordTrace tailWord_1411848 prefixEnd_1411848 483304423392731581271357 := by
  unfold tailWord_1411848
  simp only [CollatzResearch.WordTrace]
  refine ⟨25747163494561647643306099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34329551326082196857741465 25747163494561647643306099)
  ·
    refine ⟨38620745241842471464959149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25747163494561647643306099 38620745241842471464959149)
    ·
      refine ⟨14482779465690926799359681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38620745241842471464959149 14482779465690926799359681)
      ·
        refine ⟨10862084599268195099519761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14482779465690926799359681 10862084599268195099519761)
        ·
          refine ⟨8146563449451146324639821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10862084599268195099519761 8146563449451146324639821)
          ·
            refine ⟨3054961293544179871739933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8146563449451146324639821 3054961293544179871739933)
            ·
              refine ⟨1145610485079067451902475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3054961293544179871739933 1145610485079067451902475)
              ·
                refine ⟨1718415727618601177853713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1145610485079067451902475 1718415727618601177853713)
                ·
                  refine ⟨1288811795713950883390285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1718415727618601177853713 1288811795713950883390285)
                  ·
                    refine ⟨483304423392731581271357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1288811795713950883390285 483304423392731581271357)
                    ·
                      rfl

theorem cell22_1411848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_1411848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411848 prefixEnd_1411848 := by exact prefixLift 1411848
  have htrace : WordTrace (prefixWord ++ tailWord_1411848) baseStart_1411848 baseEnd_1411848 := by
    simpa [prefixWord, tailWord_1411848, baseEnd_1411848] using wordTrace_append hprefix tailTrace_1411848
  have hstable : (prefixWord ++ tailWord_1411848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411848).length < 2 ^ (prefixWord ++ tailWord_1411848).sum := by decide
  have hdescent : baseEnd_1411848 < baseStart_1411848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411857 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 2, 6]
def baseStart_1411857 : Nat := 118140960795 + 1411857 * 2 ^ 59
def prefixEnd_1411857 : Nat := 4983230072969 + 3 ^ 40 * 1411857 * 2
def baseEnd_1411857 : Nat := 483307504276658557796329

theorem tailTrace_1411857 : CollatzResearch.WordTrace tailWord_1411857 prefixEnd_1411857 483307504276658557796329 := by
  unfold tailWord_1411857
  simp only [CollatzResearch.WordTrace]
  refine ⟨51494655246090689823689825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34329770164060459882459883 51494655246090689823689825)
  ·
    refine ⟨38620991434568017367767369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51494655246090689823689825 38620991434568017367767369)
    ·
      refine ⟨28965743575926013025825527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38620991434568017367767369 28965743575926013025825527)
      ·
        refine ⟨43448615363889019538738291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28965743575926013025825527 43448615363889019538738291)
        ·
          refine ⟨65172923045833529308107437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43448615363889019538738291 65172923045833529308107437)
          ·
            refine ⟨24439846142187573490540289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65172923045833529308107437 24439846142187573490540289)
            ·
              refine ⟨18329884606640680117905217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24439846142187573490540289 18329884606640680117905217)
              ·
                refine ⟨13747413454980510088428913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18329884606640680117905217 13747413454980510088428913)
                ·
                  refine ⟨10310560091235382566321685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13747413454980510088428913 10310560091235382566321685)
                  ·
                    refine ⟨483307504276658557796329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10310560091235382566321685 483307504276658557796329)
                    ·
                      rfl

theorem cell22_1411857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_1411857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411857 prefixEnd_1411857 := by exact prefixLift 1411857
  have htrace : WordTrace (prefixWord ++ tailWord_1411857) baseStart_1411857 baseEnd_1411857 := by
    simpa [prefixWord, tailWord_1411857, baseEnd_1411857] using wordTrace_append hprefix tailTrace_1411857
  have hstable : (prefixWord ++ tailWord_1411857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411857).length < 2 ^ (prefixWord ++ tailWord_1411857).sum := by decide
  have hdescent : baseEnd_1411857 < baseStart_1411857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411859 : List Nat := [1, 1, 1, 2, 1, 3, 3, 4, 3, 3]
def baseStart_1411859 : Nat := 118140960795 + 1411859 * 2 ^ 59
def prefixEnd_1411859 : Nat := 4983230072969 + 3 ^ 40 * 1411859 * 2
def baseEnd_1411859 : Nat := 483308188917531219246323

theorem tailTrace_1411859 : CollatzResearch.WordTrace tailWord_1411859 prefixEnd_1411859 483308188917531219246323 := by
  unfold tailWord_1411859
  simp only [CollatzResearch.WordTrace]
  refine ⟨51494728192083444165262631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34329818794722296110175087 51494728192083444165262631)
  ·
    refine ⟨77242092288125166247893947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51494728192083444165262631 77242092288125166247893947)
    ·
      refine ⟨115863138432187749371840921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77242092288125166247893947 115863138432187749371840921)
      ·
        refine ⟨86897353824140812028880691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115863138432187749371840921 86897353824140812028880691)
        ·
          refine ⟨130346030736211218043321037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86897353824140812028880691 130346030736211218043321037)
          ·
            refine ⟨48879761526079206766245389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130346030736211218043321037 48879761526079206766245389)
            ·
              refine ⟨18329910572279702537342021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48879761526079206766245389 18329910572279702537342021)
              ·
                refine ⟨3436858232302444225751629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18329910572279702537342021 3436858232302444225751629)
                ·
                  refine ⟨1288821837113416584656861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3436858232302444225751629 1288821837113416584656861)
                  ·
                    refine ⟨483308188917531219246323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1288821837113416584656861 483308188917531219246323)
                    ·
                      rfl

theorem cell22_1411859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 3, 3].length) (baseStart_1411859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411859 prefixEnd_1411859 := by exact prefixLift 1411859
  have htrace : WordTrace (prefixWord ++ tailWord_1411859) baseStart_1411859 baseEnd_1411859 := by
    simpa [prefixWord, tailWord_1411859, baseEnd_1411859] using wordTrace_append hprefix tailTrace_1411859
  have hstable : (prefixWord ++ tailWord_1411859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411859).length < 2 ^ (prefixWord ++ tailWord_1411859).sum := by decide
  have hdescent : baseEnd_1411859 < baseStart_1411859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411889 : List Nat := [1, 2, 2, 3, 2, 1, 2, 4, 5]
def baseStart_1411889 : Nat := 118140960795 + 1411889 * 2 ^ 59
def prefixEnd_1411889 : Nat := 4983230072969 + 3 ^ 40 * 1411889 * 2
def baseEnd_1411889 : Nat := 161106152843540380332077

theorem tailTrace_1411889 : CollatzResearch.WordTrace tailWord_1411889 prefixEnd_1411889 161106152843540380332077 := by
  unfold tailWord_1411889
  simp only [CollatzResearch.WordTrace]
  refine ⟨51495822381974759288854721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34330548254649839525903147 51495822381974759288854721)
  ·
    refine ⟨38621866786481069466641041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51495822381974759288854721 38621866786481069466641041)
    ·
      refine ⟨28966400089860802099980781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38621866786481069466641041 28966400089860802099980781)
      ·
        refine ⟨10862400033697800787492793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28966400089860802099980781 10862400033697800787492793)
        ·
          refine ⟨8146800025273350590619595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10862400033697800787492793 8146800025273350590619595)
          ·
            refine ⟨12220200037910025885929393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8146800025273350590619595 12220200037910025885929393)
            ·
              refine ⟨9165150028432519414447045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12220200037910025885929393 9165150028432519414447045)
              ·
                refine ⟨1718465630331097390208821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9165150028432519414447045 1718465630331097390208821)
                ·
                  refine ⟨161106152843540380332077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1718465630331097390208821 161106152843540380332077)
                  ·
                    rfl

theorem cell22_1411889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 5].length) (baseStart_1411889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411889 prefixEnd_1411889 := by exact prefixLift 1411889
  have htrace : WordTrace (prefixWord ++ tailWord_1411889) baseStart_1411889 baseEnd_1411889 := by
    simpa [prefixWord, tailWord_1411889, baseEnd_1411889] using wordTrace_append hprefix tailTrace_1411889
  have hstable : (prefixWord ++ tailWord_1411889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411889).length < 2 ^ (prefixWord ++ tailWord_1411889).sum := by decide
  have hdescent : baseEnd_1411889 < baseStart_1411889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411893 : List Nat := [1, 3, 3, 1, 3, 3, 1, 1, 3, 3]
def baseStart_1411893 : Nat := 118140960795 + 1411893 * 2 ^ 59
def prefixEnd_1411893 : Nat := 4983230072969 + 3 ^ 40 * 1411893 * 2
def baseEnd_1411893 : Nat := 483319827812366463896219

theorem tailTrace_1411893 : CollatzResearch.WordTrace tailWord_1411893 prefixEnd_1411893 483319827812366463896219 := by
  unfold tailWord_1411893
  simp only [CollatzResearch.WordTrace]
  refine ⟨51495968273960267972000333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34330645515973511981333555 51495968273960267972000333)
  ·
    refine ⟨19310988102735100489500125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51495968273960267972000333 19310988102735100489500125)
    ·
      refine ⟨7241620538525662683562547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19310988102735100489500125 7241620538525662683562547)
      ·
        refine ⟨10862430807788494025343821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7241620538525662683562547 10862430807788494025343821)
        ·
          refine ⟨4073411552920685259503933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10862430807788494025343821 4073411552920685259503933)
          ·
            refine ⟨1527529332345256972313975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4073411552920685259503933 1527529332345256972313975)
            ·
              refine ⟨2291293998517885458470963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1527529332345256972313975 2291293998517885458470963)
              ·
                refine ⟨3436940997776828187706445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2291293998517885458470963 3436940997776828187706445)
                ·
                  refine ⟨1288852874166310570389917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3436940997776828187706445 1288852874166310570389917)
                  ·
                    refine ⟨483319827812366463896219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1288852874166310570389917 483319827812366463896219)
                    ·
                      rfl

theorem cell22_1411893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_1411893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411893 prefixEnd_1411893 := by exact prefixLift 1411893
  have htrace : WordTrace (prefixWord ++ tailWord_1411893) baseStart_1411893 baseEnd_1411893 := by
    simpa [prefixWord, tailWord_1411893, baseEnd_1411893] using wordTrace_append hprefix tailTrace_1411893
  have hstable : (prefixWord ++ tailWord_1411893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411893).length < 2 ^ (prefixWord ++ tailWord_1411893).sum := by decide
  have hdescent : baseEnd_1411893 < baseStart_1411893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411949 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_1411949 : Nat := 118140960795 + 1411949 * 2 ^ 59
def prefixEnd_1411949 : Nat := 4983230072969 + 3 ^ 40 * 1411949 * 2
def baseEnd_1411949 : Nat := 483338997756800984496047

theorem tailTrace_1411949 : CollatzResearch.WordTrace tailWord_1411949 prefixEnd_1411949 483338997756800984496047 := by
  unfold tailWord_1411949
  simp only [CollatzResearch.WordTrace]
  refine ⟨51498010761757389536038901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34332007174504926357359267 51498010761757389536038901)
  ·
    refine ⟨4827938508914755269003647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51498010761757389536038901 4827938508914755269003647)
    ·
      refine ⟨7241907763372132903505471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4827938508914755269003647 7241907763372132903505471)
      ·
        refine ⟨10862861645058199355258207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7241907763372132903505471 10862861645058199355258207)
        ·
          refine ⟨16294292467587299032887311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10862861645058199355258207 16294292467587299032887311)
          ·
            refine ⟨24441438701380948549330967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16294292467587299032887311 24441438701380948549330967)
            ·
              refine ⟨36662158052071422823996451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24441438701380948549330967 36662158052071422823996451)
              ·
                refine ⟨54993237078107134235994677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36662158052071422823996451 54993237078107134235994677)
                ·
                  refine ⟨5155615976072543834624501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54993237078107134235994677 5155615976072543834624501)
                  ·
                    refine ⟨483338997756800984496047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5155615976072543834624501 483338997756800984496047)
                    ·
                      rfl

theorem cell22_1411949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_1411949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411949 prefixEnd_1411949 := by exact prefixLift 1411949
  have htrace : WordTrace (prefixWord ++ tailWord_1411949) baseStart_1411949 baseEnd_1411949 := by
    simpa [prefixWord, tailWord_1411949, baseEnd_1411949] using wordTrace_append hprefix tailTrace_1411949
  have hstable : (prefixWord ++ tailWord_1411949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411949).length < 2 ^ (prefixWord ++ tailWord_1411949).sum := by decide
  have hdescent : baseEnd_1411949 < baseStart_1411949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411964 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 4, 4]
def baseStart_1411964 : Nat := 118140960795 + 1411964 * 2 ^ 59
def prefixEnd_1411964 : Nat := 4983230072969 + 3 ^ 40 * 1411964 * 2
def baseEnd_1411964 : Nat := 483344132563345945371001

theorem tailTrace_1411964 : CollatzResearch.WordTrace tailWord_1411964 prefixEnd_1411964 483344132563345945371001 := by
  unfold tailWord_1411964
  simp only [CollatzResearch.WordTrace]
  refine ⟨25749278928351523548917473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34332371904468698065223297 25749278928351523548917473)
  ·
    refine ⟨19311959196263642661688105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25749278928351523548917473 19311959196263642661688105)
    ·
      refine ⟨14483969397197731996266079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19311959196263642661688105 14483969397197731996266079)
      ·
        refine ⟨21725954095796597994399119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14483969397197731996266079 21725954095796597994399119)
        ·
          refine ⟨32588931143694896991598679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21725954095796597994399119 32588931143694896991598679)
          ·
            refine ⟨48883396715542345487398019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32588931143694896991598679 48883396715542345487398019)
            ·
              refine ⟨73325095073313518231097029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48883396715542345487398019 73325095073313518231097029)
              ·
                refine ⟨13748455326246284668330693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73325095073313518231097029 13748455326246284668330693)
                ·
                  refine ⟨2577835373671178375312005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13748455326246284668330693 2577835373671178375312005)
                  ·
                    refine ⟨483344132563345945371001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2577835373671178375312005 483344132563345945371001)
                    ·
                      rfl

theorem cell22_1411964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_1411964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411964 prefixEnd_1411964 := by exact prefixLift 1411964
  have htrace : WordTrace (prefixWord ++ tailWord_1411964) baseStart_1411964 baseEnd_1411964 := by
    simpa [prefixWord, tailWord_1411964, baseEnd_1411964] using wordTrace_append hprefix tailTrace_1411964
  have hstable : (prefixWord ++ tailWord_1411964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411964).length < 2 ^ (prefixWord ++ tailWord_1411964).sum := by decide
  have hdescent : baseEnd_1411964 < baseStart_1411964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1411996 : List Nat := [2, 2, 3, 3, 2, 1, 9]
def baseStart_1411996 : Nat := 118140960795 + 1411996 * 2 ^ 59
def prefixEnd_1411996 : Nat := 4983230072969 + 3 ^ 40 * 1411996 * 2
def baseEnd_1411996 : Nat := 17902040252492908465589

theorem tailTrace_1411996 : CollatzResearch.WordTrace tailWord_1411996 prefixEnd_1411996 17902040252492908465589 := by
  unfold tailWord_1411996
  simp only [CollatzResearch.WordTrace]
  refine ⟨25749862496293558281499921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34333149995058077708666561 25749862496293558281499921)
  ·
    refine ⟨19312396872220168711124941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25749862496293558281499921 19312396872220168711124941)
    ·
      refine ⟨7242148827082563266671853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19312396872220168711124941 7242148827082563266671853)
      ·
        refine ⟨2715805810155961225001945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7242148827082563266671853 2715805810155961225001945)
        ·
          refine ⟨2036854357616970918751459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2715805810155961225001945 2036854357616970918751459)
          ·
            refine ⟨3055281536425456378127189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2036854357616970918751459 3055281536425456378127189)
            ·
              refine ⟨17902040252492908465589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3055281536425456378127189 17902040252492908465589)
              ·
                rfl

theorem cell22_1411996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 9].length) (baseStart_1411996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1411996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1411996 prefixEnd_1411996 := by exact prefixLift 1411996
  have htrace : WordTrace (prefixWord ++ tailWord_1411996) baseStart_1411996 baseEnd_1411996 := by
    simpa [prefixWord, tailWord_1411996, baseEnd_1411996] using wordTrace_append hprefix tailTrace_1411996
  have hstable : (prefixWord ++ tailWord_1411996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1411996).length < 2 ^ (prefixWord ++ tailWord_1411996).sum := by decide
  have hdescent : baseEnd_1411996 < baseStart_1411996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1411996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412039 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 1, 7]
def baseStart_1412039 : Nat := 118140960795 + 1412039 * 2 ^ 59
def prefixEnd_1412039 : Nat := 4983230072969 + 3 ^ 40 * 1412039 * 2
def baseEnd_1412039 : Nat := 483369806596070749745771

theorem tailTrace_1412039 : CollatzResearch.WordTrace tailWord_1412039 prefixEnd_1412039 483369806596070749745771 := by
  unfold tailWord_1412039
  simp only [CollatzResearch.WordTrace]
  refine ⟨51501293331431334906815171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34334195554287556604543447 51501293331431334906815171)
  ·
    refine ⟨77251939997147002360222757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51501293331431334906815171 77251939997147002360222757)
    ·
      refine ⟨14484738749465062942541767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77251939997147002360222757 14484738749465062942541767)
      ·
        refine ⟨21727108124197594413812651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14484738749465062942541767 21727108124197594413812651)
        ·
          refine ⟨32590662186296391620718977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21727108124197594413812651 32590662186296391620718977)
          ·
            refine ⟨24442996639722293715539233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32590662186296391620718977 24442996639722293715539233)
            ·
              refine ⟨18332247479791720286654425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24442996639722293715539233 18332247479791720286654425)
              ·
                refine ⟨13749185609843790214990819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18332247479791720286654425 13749185609843790214990819)
                ·
                  refine ⟨20623778414765685322486229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13749185609843790214990819 20623778414765685322486229)
                  ·
                    refine ⟨483369806596070749745771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20623778414765685322486229 483369806596070749745771)
                    ·
                      rfl

theorem cell22_1412039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_1412039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412039 prefixEnd_1412039 := by exact prefixLift 1412039
  have htrace : WordTrace (prefixWord ++ tailWord_1412039) baseStart_1412039 baseEnd_1412039 := by
    simpa [prefixWord, tailWord_1412039, baseEnd_1412039] using wordTrace_append hprefix tailTrace_1412039
  have hstable : (prefixWord ++ tailWord_1412039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412039).length < 2 ^ (prefixWord ++ tailWord_1412039).sum := by decide
  have hdescent : baseEnd_1412039 < baseStart_1412039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412101 : List Nat := [1, 3, 1, 1, 2, 3, 3, 2, 1, 5]
def baseStart_1412101 : Nat := 118140960795 + 1412101 * 2 ^ 59
def prefixEnd_1412101 : Nat := 4983230072969 + 3 ^ 40 * 1412101 * 2
def baseEnd_1412101 : Nat := 483391030463123254695581

theorem tailTrace_1412101 : CollatzResearch.WordTrace tailWord_1412101 prefixEnd_1412101 483391030463123254695581 := by
  unfold tailWord_1412101
  simp only [CollatzResearch.WordTrace]
  refine ⟨51503554657206719495572157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34335703104804479663714771 51503554657206719495572157)
  ·
    refine ⟨19313832996452519810839559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51503554657206719495572157 19313832996452519810839559)
    ·
      refine ⟨28970749494678779716259339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19313832996452519810839559 28970749494678779716259339)
      ·
        refine ⟨43456124242018169574389009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28970749494678779716259339 43456124242018169574389009)
        ·
          refine ⟨32592093181513627180791757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43456124242018169574389009 32592093181513627180791757)
          ·
            refine ⟨12222034943067610192796909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32592093181513627180791757 12222034943067610192796909)
            ·
              refine ⟨4583263103650353822298841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12222034943067610192796909 4583263103650353822298841)
              ·
                refine ⟨3437447327737765366724131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4583263103650353822298841 3437447327737765366724131)
                ·
                  refine ⟨5156170991606648050086197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3437447327737765366724131 5156170991606648050086197)
                  ·
                    refine ⟨483391030463123254695581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5156170991606648050086197 483391030463123254695581)
                    ·
                      rfl

theorem cell22_1412101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_1412101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412101 prefixEnd_1412101 := by exact prefixLift 1412101
  have htrace : WordTrace (prefixWord ++ tailWord_1412101) baseStart_1412101 baseEnd_1412101 := by
    simpa [prefixWord, tailWord_1412101, baseEnd_1412101] using wordTrace_append hprefix tailTrace_1412101
  have hstable : (prefixWord ++ tailWord_1412101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412101).length < 2 ^ (prefixWord ++ tailWord_1412101).sum := by decide
  have hdescent : baseEnd_1412101 < baseStart_1412101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412103 : List Nat := [1, 1, 4, 3, 1, 1, 2, 5, 4]
def baseStart_1412103 : Nat := 118140960795 + 1412103 * 2 ^ 59
def prefixEnd_1412103 : Nat := 4983230072969 + 3 ^ 40 * 1412103 * 2
def baseEnd_1412103 : Nat := 161130571701331972048525

theorem tailTrace_1412103 : CollatzResearch.WordTrace tailWord_1412103 prefixEnd_1412103 161130571701331972048525 := by
  unfold tailWord_1412103
  simp only [CollatzResearch.WordTrace]
  refine ⟨51503627603199473837144963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34335751735466315891429975 51503627603199473837144963)
  ·
    refine ⟨77255441404799210755717445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51503627603199473837144963 77255441404799210755717445)
    ·
      refine ⟨14485395263399852016697021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77255441404799210755717445 14485395263399852016697021)
      ·
        refine ⟨5432023223774944506261383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14485395263399852016697021 5432023223774944506261383)
        ·
          refine ⟨8148034835662416759392075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5432023223774944506261383 8148034835662416759392075)
          ·
            refine ⟨12222052253493625139088113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8148034835662416759392075 12222052253493625139088113)
            ·
              refine ⟨9166539190120218854316085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12222052253493625139088113 9166539190120218854316085)
              ·
                refine ⟨859363049073770517592133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9166539190120218854316085 859363049073770517592133)
                ·
                  refine ⟨161130571701331972048525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 859363049073770517592133 161130571701331972048525)
                  ·
                    rfl

theorem cell22_1412103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5, 4].length) (baseStart_1412103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412103 prefixEnd_1412103 := by exact prefixLift 1412103
  have htrace : WordTrace (prefixWord ++ tailWord_1412103) baseStart_1412103 baseEnd_1412103 := by
    simpa [prefixWord, tailWord_1412103, baseEnd_1412103] using wordTrace_append hprefix tailTrace_1412103
  have hstable : (prefixWord ++ tailWord_1412103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412103).length < 2 ^ (prefixWord ++ tailWord_1412103).sum := by decide
  have hdescent : baseEnd_1412103 < baseStart_1412103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412120 : List Nat := [2, 1, 2, 3, 2, 2, 4, 2, 4]
def baseStart_1412120 : Nat := 118140960795 + 1412120 * 2 ^ 59
def prefixEnd_1412120 : Nat := 4983230072969 + 3 ^ 40 * 1412120 * 2
def baseEnd_1412120 : Nat := 161132511517137846156841

theorem tailTrace_1412120 : CollatzResearch.WordTrace tailWord_1412120 prefixEnd_1412120 161132511517137846156841 := by
  unfold tailWord_1412120
  simp only [CollatzResearch.WordTrace]
  refine ⟨25752123822068942870256907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34336165096091923827009209 25752123822068942870256907)
  ·
    refine ⟨38628185733103414305385361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25752123822068942870256907 38628185733103414305385361)
    ·
      refine ⟨28971139299827560729039021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38628185733103414305385361 28971139299827560729039021)
      ·
        refine ⟨10864177237435335273389633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28971139299827560729039021 10864177237435335273389633)
        ·
          refine ⟨8148132928076501455042225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10864177237435335273389633 8148132928076501455042225)
          ·
            refine ⟨6111099696057376091281669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8148132928076501455042225 6111099696057376091281669)
            ·
              refine ⟨1145831193010758017115313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6111099696057376091281669 1145831193010758017115313)
              ·
                refine ⟨859373394758068512836485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1145831193010758017115313 859373394758068512836485)
                ·
                  refine ⟨161132511517137846156841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 859373394758068512836485 161132511517137846156841)
                  ·
                    rfl

theorem cell22_1412120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 4].length) (baseStart_1412120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412120 prefixEnd_1412120 := by exact prefixLift 1412120
  have htrace : WordTrace (prefixWord ++ tailWord_1412120) baseStart_1412120 baseEnd_1412120 := by
    simpa [prefixWord, tailWord_1412120, baseEnd_1412120] using wordTrace_append hprefix tailTrace_1412120
  have hstable : (prefixWord ++ tailWord_1412120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412120).length < 2 ^ (prefixWord ++ tailWord_1412120).sum := by decide
  have hdescent : baseEnd_1412120 < baseStart_1412120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412131 : List Nat := [1, 1, 1, 4, 3, 2, 3, 7]
def baseStart_1412131 : Nat := 118140960795 + 1412131 * 2 ^ 59
def prefixEnd_1412131 : Nat := 4983230072969 + 3 ^ 40 * 1412131 * 2
def baseEnd_1412131 : Nat := 53711255564023686271721

theorem tailTrace_1412131 : CollatzResearch.WordTrace tailWord_1412131 prefixEnd_1412131 53711255564023686271721 := by
  unfold tailWord_1412131
  simp only [CollatzResearch.WordTrace]
  refine ⟨51504648847098034619164247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34336432564732023079442831 51504648847098034619164247)
  ·
    refine ⟨77256973270647051928746371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51504648847098034619164247 77256973270647051928746371)
    ·
      refine ⟨115885459905970577893119557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77256973270647051928746371 115885459905970577893119557)
      ·
        refine ⟨21728523732369483354959917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115885459905970577893119557 21728523732369483354959917)
        ·
          refine ⟨8148196399638556258109969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21728523732369483354959917 8148196399638556258109969)
          ·
            refine ⟨6111147299728917193582477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8148196399638556258109969 6111147299728917193582477)
            ·
              refine ⟨2291680237398343947593429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6111147299728917193582477 2291680237398343947593429)
              ·
                refine ⟨53711255564023686271721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2291680237398343947593429 53711255564023686271721)
                ·
                  rfl

theorem cell22_1412131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 7].length) (baseStart_1412131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412131 prefixEnd_1412131 := by exact prefixLift 1412131
  have htrace : WordTrace (prefixWord ++ tailWord_1412131) baseStart_1412131 baseEnd_1412131 := by
    simpa [prefixWord, tailWord_1412131, baseEnd_1412131] using wordTrace_append hprefix tailTrace_1412131
  have hstable : (prefixWord ++ tailWord_1412131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412131).length < 2 ^ (prefixWord ++ tailWord_1412131).sum := by decide
  have hdescent : baseEnd_1412131 < baseStart_1412131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412135 : List Nat := [1, 1, 7, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1412135 : Nat := 118140960795 + 1412135 * 2 ^ 59
def prefixEnd_1412135 : Nat := 4983230072969 + 3 ^ 40 * 1412135 * 2
def baseEnd_1412135 : Nat := 483402669357958499345477

theorem tailTrace_1412135 : CollatzResearch.WordTrace tailWord_1412135 prefixEnd_1412135 483402669357958499345477 := by
  unfold tailWord_1412135
  simp only [CollatzResearch.WordTrace]
  refine ⟨51504794739083543302309859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34336529826055695534873239 51504794739083543302309859)
  ·
    refine ⟨77257192108625314953464789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51504794739083543302309859 77257192108625314953464789)
    ·
      refine ⟨1810715440045905819221831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 77257192108625314953464789 1810715440045905819221831)
      ·
        refine ⟨2716073160068858728832747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1810715440045905819221831 2716073160068858728832747)
        ·
          refine ⟨4074109740103288093249121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2716073160068858728832747 4074109740103288093249121)
          ·
            refine ⟨3055582305077466069936841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4074109740103288093249121 3055582305077466069936841)
            ·
              refine ⟨2291686728808099552452631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3055582305077466069936841 2291686728808099552452631)
              ·
                refine ⟨3437530093212149328678947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2291686728808099552452631 3437530093212149328678947)
                ·
                  refine ⟨5156295139818223993018421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3437530093212149328678947 5156295139818223993018421)
                  ·
                    refine ⟨483402669357958499345477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5156295139818223993018421 483402669357958499345477)
                    ·
                      rfl

theorem cell22_1412135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1412135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412135 prefixEnd_1412135 := by exact prefixLift 1412135
  have htrace : WordTrace (prefixWord ++ tailWord_1412135) baseStart_1412135 baseEnd_1412135 := by
    simpa [prefixWord, tailWord_1412135, baseEnd_1412135] using wordTrace_append hprefix tailTrace_1412135
  have hstable : (prefixWord ++ tailWord_1412135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412135).length < 2 ^ (prefixWord ++ tailWord_1412135).sum := by decide
  have hdescent : baseEnd_1412135 < baseStart_1412135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412150 : List Nat := [5, 1, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_1412150 : Nat := 118140960795 + 1412150 * 2 ^ 59
def prefixEnd_1412150 : Nat := 4983230072969 + 3 ^ 40 * 1412150 * 2
def baseEnd_1412150 : Nat := 483407804164503460220431

theorem tailTrace_1412150 : CollatzResearch.WordTrace tailWord_1412150 prefixEnd_1412150 483407804164503460220431 := by
  unfold tailWord_1412150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3219083864626825054006619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34336894556019467242737269 3219083864626825054006619)
  ·
    refine ⟨4828625796940237581009929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3219083864626825054006619 4828625796940237581009929)
    ·
      refine ⟨3621469347705178185757447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4828625796940237581009929 3621469347705178185757447)
      ·
        refine ⟨5432204021557767278636171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3621469347705178185757447 5432204021557767278636171)
        ·
          refine ⟨8148306032336650917954257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5432204021557767278636171 8148306032336650917954257)
          ·
            refine ⟨6111229524252488188465693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8148306032336650917954257 6111229524252488188465693)
            ·
              refine ⟨2291711071594683070674635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6111229524252488188465693 2291711071594683070674635)
              ·
                refine ⟨3437566607392024606011953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2291711071594683070674635 3437566607392024606011953)
                ·
                  refine ⟨2578174955544018454508965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3437566607392024606011953 2578174955544018454508965)
                  ·
                    refine ⟨483407804164503460220431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2578174955544018454508965 483407804164503460220431)
                    ·
                      rfl

theorem cell22_1412150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_1412150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412150 prefixEnd_1412150 := by exact prefixLift 1412150
  have htrace : WordTrace (prefixWord ++ tailWord_1412150) baseStart_1412150 baseEnd_1412150 := by
    simpa [prefixWord, tailWord_1412150, baseEnd_1412150] using wordTrace_append hprefix tailTrace_1412150
  have hstable : (prefixWord ++ tailWord_1412150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412150).length < 2 ^ (prefixWord ++ tailWord_1412150).sum := by decide
  have hdescent : baseEnd_1412150 < baseStart_1412150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412191 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 2, 5]
def baseStart_1412191 : Nat := 118140960795 + 1412191 * 2 ^ 59
def prefixEnd_1412191 : Nat := 4983230072969 + 3 ^ 40 * 1412191 * 2
def baseEnd_1412191 : Nat := 483421839302393019945305

theorem tailTrace_1412191 : CollatzResearch.WordTrace tailWord_1412191 prefixEnd_1412191 483421839302393019945305 := by
  unfold tailWord_1412191
  simp only [CollatzResearch.WordTrace]
  refine ⟨51506837226880664866348427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34337891484587109910898951 51506837226880664866348427)
  ·
    refine ⟨77260255840320997299522641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51506837226880664866348427 77260255840320997299522641)
    ·
      refine ⟨57945191880240747974641981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77260255840320997299522641 57945191880240747974641981)
      ·
        refine ⟨21729446955090280490490743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57945191880240747974641981 21729446955090280490490743)
        ·
          refine ⟨32594170432635420735736115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21729446955090280490490743 32594170432635420735736115)
          ·
            refine ⟨48891255648953131103604173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32594170432635420735736115 48891255648953131103604173)
            ·
              refine ⟨18334220868357424163851565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48891255648953131103604173 18334220868357424163851565)
              ·
                refine ⟨6875332825634034061444337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18334220868357424163851565 6875332825634034061444337)
                ·
                  refine ⟨5156499619225525546083253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6875332825634034061444337 5156499619225525546083253)
                  ·
                    refine ⟨483421839302393019945305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5156499619225525546083253 483421839302393019945305)
                    ·
                      rfl

theorem cell22_1412191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_1412191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412191 prefixEnd_1412191 := by exact prefixLift 1412191
  have htrace : WordTrace (prefixWord ++ tailWord_1412191) baseStart_1412191 baseEnd_1412191 := by
    simpa [prefixWord, tailWord_1412191, baseEnd_1412191] using wordTrace_append hprefix tailTrace_1412191
  have hstable : (prefixWord ++ tailWord_1412191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412191).length < 2 ^ (prefixWord ++ tailWord_1412191).sum := by decide
  have hdescent : baseEnd_1412191 < baseStart_1412191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412253 : List Nat := [1, 4, 2, 1, 1, 2, 2, 3, 1, 5]
def baseStart_1412253 : Nat := 118140960795 + 1412253 * 2 ^ 59
def prefixEnd_1412253 : Nat := 4983230072969 + 3 ^ 40 * 1412253 * 2
def baseEnd_1412253 : Nat := 483443063169445524895115

theorem tailTrace_1412253 : CollatzResearch.WordTrace tailWord_1412253 prefixEnd_1412253 483443063169445524895115 := by
  unfold tailWord_1412253
  simp only [CollatzResearch.WordTrace]
  refine ⟨51509098552656049455105413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34339399035104032970070275 51509098552656049455105413)
  ·
    refine ⟨9657955978623009272832265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51509098552656049455105413 9657955978623009272832265)
    ·
      refine ⟨7243466983967256954624199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9657955978623009272832265 7243466983967256954624199)
      ·
        refine ⟨10865200475950885431936299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7243466983967256954624199 10865200475950885431936299)
        ·
          refine ⟨16297800713926328147904449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10865200475950885431936299 16297800713926328147904449)
          ·
            refine ⟨12223350535444746110928337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16297800713926328147904449 12223350535444746110928337)
            ·
              refine ⟨9167512901583559583196253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12223350535444746110928337 9167512901583559583196253)
              ·
                refine ⟨3437817338093834843698595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9167512901583559583196253 3437817338093834843698595)
                ·
                  refine ⟨5156726007140752265547893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3437817338093834843698595 5156726007140752265547893)
                  ·
                    refine ⟨483443063169445524895115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5156726007140752265547893 483443063169445524895115)
                    ·
                      rfl

theorem cell22_1412253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_1412253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412253 prefixEnd_1412253 := by exact prefixLift 1412253
  have htrace : WordTrace (prefixWord ++ tailWord_1412253) baseStart_1412253 baseEnd_1412253 := by
    simpa [prefixWord, tailWord_1412253, baseEnd_1412253] using wordTrace_append hprefix tailTrace_1412253
  have hstable : (prefixWord ++ tailWord_1412253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412253).length < 2 ^ (prefixWord ++ tailWord_1412253).sum := by decide
  have hdescent : baseEnd_1412253 < baseStart_1412253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412289 : List Nat := [1, 2, 6, 1, 1, 1, 4, 2, 4]
def baseStart_1412289 : Nat := 118140960795 + 1412289 * 2 ^ 59
def prefixEnd_1412289 : Nat := 4983230072969 + 3 ^ 40 * 1412289 * 2
def baseEnd_1412289 : Nat := 161151795568384476998335

theorem tailTrace_1412289 : CollatzResearch.WordTrace tailWord_1412289 prefixEnd_1412289 161151795568384476998335 := by
  unfold tailWord_1412289
  simp only [CollatzResearch.WordTrace]
  refine ⟨51510411580525627603415921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34340274387017085068943947 51510411580525627603415921)
  ·
    refine ⟨38632808685394220702561941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51510411580525627603415921 38632808685394220702561941)
    ·
      refine ⟨1810912907127854095432591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38632808685394220702561941 1810912907127854095432591)
      ·
        refine ⟨2716369360691781143148887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1810912907127854095432591 2716369360691781143148887)
        ·
          refine ⟨4074554041037671714723331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2716369360691781143148887 4074554041037671714723331)
          ·
            refine ⟨6111831061556507572084997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4074554041037671714723331 6111831061556507572084997)
            ·
              refine ⟨1145968324041845169765937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6111831061556507572084997 1145968324041845169765937)
              ·
                refine ⟨859476243031383877324453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1145968324041845169765937 859476243031383877324453)
                ·
                  refine ⟨161151795568384476998335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 859476243031383877324453 161151795568384476998335)
                  ·
                    rfl

theorem cell22_1412289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 4].length) (baseStart_1412289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412289 prefixEnd_1412289 := by exact prefixLift 1412289
  have htrace : WordTrace (prefixWord ++ tailWord_1412289) baseStart_1412289 baseEnd_1412289 := by
    simpa [prefixWord, tailWord_1412289, baseEnd_1412289] using wordTrace_append hprefix tailTrace_1412289
  have hstable : (prefixWord ++ tailWord_1412289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412289).length < 2 ^ (prefixWord ++ tailWord_1412289).sum := by decide
  have hdescent : baseEnd_1412289 < baseStart_1412289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412317 : List Nat := [1, 4, 3, 2, 2, 1, 3, 6]
def baseStart_1412317 : Nat := 118140960795 + 1412317 * 2 ^ 59
def prefixEnd_1412317 : Nat := 4983230072969 + 3 ^ 40 * 1412317 * 2
def baseEnd_1412317 : Nat := 53718330186374521254991

theorem tailTrace_1412317 : CollatzResearch.WordTrace tailWord_1412317 prefixEnd_1412317 53718330186374521254991 := by
  unfold tailWord_1412317
  simp only [CollatzResearch.WordTrace]
  refine ⟨51511432824424188385435205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34340955216282792256956803 51511432824424188385435205)
  ·
    refine ⟨9658393654579535322269101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51511432824424188385435205 9658393654579535322269101)
    ·
      refine ⟨3621897620467325745850913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9658393654579535322269101 3621897620467325745850913)
      ·
        refine ⟨2716423215350494309388185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3621897620467325745850913 2716423215350494309388185)
        ·
          refine ⟨2037317411512870732041139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2716423215350494309388185 2037317411512870732041139)
          ·
            refine ⟨3055976117269306098061709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2037317411512870732041139 3055976117269306098061709)
            ·
              refine ⟨1145991043975989786773141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3055976117269306098061709 1145991043975989786773141)
              ·
                refine ⟨53718330186374521254991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1145991043975989786773141 53718330186374521254991)
                ·
                  rfl

theorem cell22_1412317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 6].length) (baseStart_1412317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412317 prefixEnd_1412317 := by exact prefixLift 1412317
  have htrace : WordTrace (prefixWord ++ tailWord_1412317) baseStart_1412317 baseEnd_1412317 := by
    simpa [prefixWord, tailWord_1412317, baseEnd_1412317] using wordTrace_append hprefix tailTrace_1412317
  have hstable : (prefixWord ++ tailWord_1412317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412317).length < 2 ^ (prefixWord ++ tailWord_1412317).sum := by decide
  have hdescent : baseEnd_1412317 < baseStart_1412317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412328 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 7]
def baseStart_1412328 : Nat := 118140960795 + 1412328 * 2 ^ 59
def prefixEnd_1412328 : Nat := 4983230072969 + 3 ^ 40 * 1412328 * 2
def baseEnd_1412328 : Nat := 161156245734056776423295

theorem tailTrace_1412328 : CollatzResearch.WordTrace tailWord_1412328 prefixEnd_1412328 161156245734056776423295 := by
  unfold tailWord_1412328
  simp only [CollatzResearch.WordTrace]
  refine ⟨25755917013692168632042819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34341222684922891509390425 25755917013692168632042819)
  ·
    refine ⟨38633875520538252948064229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25755917013692168632042819 38633875520538252948064229)
    ·
      refine ⟨7243851660100922427762043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38633875520538252948064229 7243851660100922427762043)
      ·
        refine ⟨10865777490151383641643065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7243851660100922427762043 10865777490151383641643065)
        ·
          refine ⟨8149333117613537731232299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10865777490151383641643065 8149333117613537731232299)
          ·
            refine ⟨12223999676420306596848449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8149333117613537731232299 12223999676420306596848449)
            ·
              refine ⟨9167999757315229947636337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12223999676420306596848449 9167999757315229947636337)
              ·
                refine ⟨6875999817986422460727253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9167999757315229947636337 6875999817986422460727253)
                ·
                  refine ⟨161156245734056776423295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6875999817986422460727253 161156245734056776423295)
                  ·
                    rfl

theorem cell22_1412328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 7].length) (baseStart_1412328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412328 prefixEnd_1412328 := by exact prefixLift 1412328
  have htrace : WordTrace (prefixWord ++ tailWord_1412328) baseStart_1412328 baseEnd_1412328 := by
    simpa [prefixWord, tailWord_1412328, baseEnd_1412328] using wordTrace_append hprefix tailTrace_1412328
  have hstable : (prefixWord ++ tailWord_1412328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412328).length < 2 ^ (prefixWord ++ tailWord_1412328).sum := by decide
  have hdescent : baseEnd_1412328 < baseStart_1412328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412332 : List Nat := [2, 2, 1, 1, 2, 4, 1, 5, 1, 3]
def baseStart_1412332 : Nat := 118140960795 + 1412332 * 2 ^ 59
def prefixEnd_1412332 : Nat := 4983230072969 + 3 ^ 40 * 1412332 * 2
def baseEnd_1412332 : Nat := 483470106483915652169873

theorem tailTrace_1412332 : CollatzResearch.WordTrace tailWord_1412332 prefixEnd_1412332 483470106483915652169873 := by
  unfold tailWord_1412332
  simp only [CollatzResearch.WordTrace]
  refine ⟨25755989959684922973615625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34341319946246563964820833 25755989959684922973615625)
  ·
    refine ⟨19316992469763692230211719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25755989959684922973615625 19316992469763692230211719)
    ·
      refine ⟨28975488704645538345317579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19316992469763692230211719 28975488704645538345317579)
      ·
        refine ⟨43463233056968307517976369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28975488704645538345317579 43463233056968307517976369)
        ·
          refine ⟨32597424792726230638482277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43463233056968307517976369 32597424792726230638482277)
          ·
            refine ⟨6112017148636168244715427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32597424792726230638482277 6112017148636168244715427)
            ·
              refine ⟨9168025722954252367073141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6112017148636168244715427 9168025722954252367073141)
              ·
                refine ⟨859502411526961159413107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9168025722954252367073141 859502411526961159413107)
                ·
                  refine ⟨1289253617290441739119661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859502411526961159413107 1289253617290441739119661)
                  ·
                    refine ⟨483470106483915652169873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1289253617290441739119661 483470106483915652169873)
                    ·
                      rfl

theorem cell22_1412332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 1, 3].length) (baseStart_1412332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412332 prefixEnd_1412332 := by exact prefixLift 1412332
  have htrace : WordTrace (prefixWord ++ tailWord_1412332) baseStart_1412332 baseEnd_1412332 := by
    simpa [prefixWord, tailWord_1412332, baseEnd_1412332] using wordTrace_append hprefix tailTrace_1412332
  have hstable : (prefixWord ++ tailWord_1412332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412332).length < 2 ^ (prefixWord ++ tailWord_1412332).sum := by decide
  have hdescent : baseEnd_1412332 < baseStart_1412332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412392 : List Nat := [2, 1, 5, 1, 2, 1, 2, 3, 1, 4]
def baseStart_1412392 : Nat := 118140960795 + 1412392 * 2 ^ 59
def prefixEnd_1412392 : Nat := 4983230072969 + 3 ^ 40 * 1412392 * 2
def baseEnd_1412392 : Nat := 483490645710095495669689

theorem tailTrace_1412392 : CollatzResearch.WordTrace tailWord_1412392 prefixEnd_1412392 483490645710095495669689 := by
  unfold tailWord_1412392
  simp only [CollatzResearch.WordTrace]
  refine ⟨25757084149576238097207715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34342778866101650796276953 25757084149576238097207715)
  ·
    refine ⟨38635626224364357145811573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25757084149576238097207715 38635626224364357145811573)
    ·
      refine ⟨3622089958534158482419835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38635626224364357145811573 3622089958534158482419835)
      ·
        refine ⟨5433134937801237723629753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3622089958534158482419835 5433134937801237723629753)
        ·
          refine ⟨4074851203350928292722315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5433134937801237723629753 4074851203350928292722315)
          ·
            refine ⟨6112276805026392439083473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4074851203350928292722315 6112276805026392439083473)
            ·
              refine ⟨4584207603769794329312605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6112276805026392439083473 4584207603769794329312605)
              ·
                refine ⟨1719077851413672873492227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4584207603769794329312605 1719077851413672873492227)
                ·
                  refine ⟨2578616777120509310238341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1719077851413672873492227 2578616777120509310238341)
                  ·
                    refine ⟨483490645710095495669689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2578616777120509310238341 483490645710095495669689)
                    ·
                      rfl

theorem cell22_1412392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_1412392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412392 prefixEnd_1412392 := by exact prefixLift 1412392
  have htrace : WordTrace (prefixWord ++ tailWord_1412392) baseStart_1412392 baseEnd_1412392 := by
    simpa [prefixWord, tailWord_1412392, baseEnd_1412392] using wordTrace_append hprefix tailTrace_1412392
  have hstable : (prefixWord ++ tailWord_1412392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412392).length < 2 ^ (prefixWord ++ tailWord_1412392).sum := by decide
  have hdescent : baseEnd_1412392 < baseStart_1412392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412437 : List Nat := [1, 3, 2, 2, 3, 2, 2, 1, 2, 4]
def baseStart_1412437 : Nat := 118140960795 + 1412437 * 2 ^ 59
def prefixEnd_1412437 : Nat := 4983230072969 + 3 ^ 40 * 1412437 * 2
def baseEnd_1412437 : Nat := 483506050129730378294551

theorem tailTrace_1412437 : CollatzResearch.WordTrace tailWord_1412437 prefixEnd_1412437 483506050129730378294551 := by
  unfold tailWord_1412437
  simp only [CollatzResearch.WordTrace]
  refine ⟨51515809583989448879803565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34343873055992965919869043 51515809583989448879803565)
  ·
    refine ⟨19318428593996043329926337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51515809583989448879803565 19318428593996043329926337)
    ·
      refine ⟨14488821445497032497444753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19318428593996043329926337 14488821445497032497444753)
      ·
        refine ⟨10866616084122774373083565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14488821445497032497444753 10866616084122774373083565)
        ·
          refine ⟨4074981031546040389906337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10866616084122774373083565 4074981031546040389906337)
          ·
            refine ⟨3056235773659530292429753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4074981031546040389906337 3056235773659530292429753)
            ·
              refine ⟨2292176830244647719322315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3056235773659530292429753 2292176830244647719322315)
              ·
                refine ⟨3438265245366971578983473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2292176830244647719322315 3438265245366971578983473)
                ·
                  refine ⟨2578698934025228684237605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3438265245366971578983473 2578698934025228684237605)
                  ·
                    refine ⟨483506050129730378294551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2578698934025228684237605 483506050129730378294551)
                    ·
                      rfl

theorem cell22_1412437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_1412437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412437 prefixEnd_1412437 := by exact prefixLift 1412437
  have htrace : WordTrace (prefixWord ++ tailWord_1412437) baseStart_1412437 baseEnd_1412437 := by
    simpa [prefixWord, tailWord_1412437, baseEnd_1412437] using wordTrace_append hprefix tailTrace_1412437
  have hstable : (prefixWord ++ tailWord_1412437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412437).length < 2 ^ (prefixWord ++ tailWord_1412437).sum := by decide
  have hdescent : baseEnd_1412437 < baseStart_1412437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412458 : List Nat := [3, 1, 3, 3, 3, 1, 2, 2, 4]
def baseStart_1412458 : Nat := 118140960795 + 1412458 * 2 ^ 59
def prefixEnd_1412458 : Nat := 4983230072969 + 3 ^ 40 * 1412458 * 2
def baseEnd_1412458 : Nat := 161171079619631107839829

theorem tailTrace_1412458 : CollatzResearch.WordTrace tailWord_1412458 prefixEnd_1412458 161171079619631107839829 := by
  unfold tailWord_1412458
  simp only [CollatzResearch.WordTrace]
  refine ⟨12879143879228342366579507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34344383677942246310878685 12879143879228342366579507)
  ·
    refine ⟨19318715818842513549869261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12879143879228342366579507 19318715818842513549869261)
    ·
      refine ⟨7244518432065942581200973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19318715818842513549869261 7244518432065942581200973)
      ·
        refine ⟨2716694412024728467950365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7244518432065942581200973 2716694412024728467950365)
        ·
          refine ⟨1018760404509273175481387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2716694412024728467950365 1018760404509273175481387)
          ·
            refine ⟨1528140606763909763222081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018760404509273175481387 1528140606763909763222081)
            ·
              refine ⟨1146105455072932322416561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1528140606763909763222081 1146105455072932322416561)
              ·
                refine ⟨859579091304699241812421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1146105455072932322416561 859579091304699241812421)
                ·
                  refine ⟨161171079619631107839829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 859579091304699241812421 161171079619631107839829)
                  ·
                    rfl

theorem cell22_1412458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 4].length) (baseStart_1412458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412458 prefixEnd_1412458 := by exact prefixLift 1412458
  have htrace : WordTrace (prefixWord ++ tailWord_1412458) baseStart_1412458 baseEnd_1412458 := by
    simpa [prefixWord, tailWord_1412458, baseEnd_1412458] using wordTrace_append hprefix tailTrace_1412458
  have hstable : (prefixWord ++ tailWord_1412458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412458).length < 2 ^ (prefixWord ++ tailWord_1412458).sum := by decide
  have hdescent : baseEnd_1412458 < baseStart_1412458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412469 : List Nat := [1, 3, 4, 1, 4, 1, 1, 7]
def baseStart_1412469 : Nat := 118140960795 + 1412469 * 2 ^ 59
def prefixEnd_1412469 : Nat := 4983230072969 + 3 ^ 40 * 1412469 * 2
def baseEnd_1412469 : Nat := 53724111598188106832717

theorem tailTrace_1412469 : CollatzResearch.WordTrace tailWord_1412469 prefixEnd_1412469 53724111598188106832717 := by
  unfold tailWord_1412469
  simp only [CollatzResearch.WordTrace]
  refine ⟨51516976719873518344968461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34344651146582345563312307 51516976719873518344968461)
  ·
    refine ⟨19318866269952569379363173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51516976719873518344968461 19318866269952569379363173)
    ·
      refine ⟨3622287425616106758630595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19318866269952569379363173 3622287425616106758630595)
      ·
        refine ⟨5433431138424160137945893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3622287425616106758630595 5433431138424160137945893)
        ·
          refine ⟨1018768338454530025864855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5433431138424160137945893 1018768338454530025864855)
          ·
            refine ⟨1528152507681795038797283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018768338454530025864855 1528152507681795038797283)
            ·
              refine ⟨2292228761522692558195925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1528152507681795038797283 2292228761522692558195925)
              ·
                refine ⟨53724111598188106832717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2292228761522692558195925 53724111598188106832717)
                ·
                  rfl

theorem cell22_1412469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 7].length) (baseStart_1412469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412469 prefixEnd_1412469 := by exact prefixLift 1412469
  have htrace : WordTrace (prefixWord ++ tailWord_1412469) baseStart_1412469 baseEnd_1412469 := by
    simpa [prefixWord, tailWord_1412469, baseEnd_1412469] using wordTrace_append hprefix tailTrace_1412469
  have hstable : (prefixWord ++ tailWord_1412469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412469).length < 2 ^ (prefixWord ++ tailWord_1412469).sum := by decide
  have hdescent : baseEnd_1412469 < baseStart_1412469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412514 : List Nat := [3, 3, 1, 2, 1, 4, 1, 2, 5]
def baseStart_1412514 : Nat := 118140960795 + 1412514 * 2 ^ 59
def prefixEnd_1412514 : Nat := 4983230072969 + 3 ^ 40 * 1412514 * 2
def baseEnd_1412514 : Nat := 161177469601109281373105

theorem tailTrace_1412514 : CollatzResearch.WordTrace tailWord_1412514 prefixEnd_1412514 161177469601109281373105 := by
  unfold tailWord_1412514
  simp only [CollatzResearch.WordTrace]
  refine ⟨12879654501177622757589149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34345745336473660686904397 12879654501177622757589149)
  ·
    refine ⟨4829870437941608534095931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12879654501177622757589149 4829870437941608534095931)
    ·
      refine ⟨7244805656912412801143897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4829870437941608534095931 7244805656912412801143897)
      ·
        refine ⟨5433604242684309600857923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7244805656912412801143897 5433604242684309600857923)
        ·
          refine ⟨8150406364026464401286885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5433604242684309600857923 8150406364026464401286885)
          ·
            refine ⟨1528201193254962075241291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8150406364026464401286885 1528201193254962075241291)
            ·
              refine ⟨2292301789882443112861937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1528201193254962075241291 2292301789882443112861937)
              ·
                refine ⟨1719226342411832334646453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2292301789882443112861937 1719226342411832334646453)
                ·
                  refine ⟨161177469601109281373105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1719226342411832334646453 161177469601109281373105)
                  ·
                    rfl

theorem cell22_1412514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_1412514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412514 prefixEnd_1412514 := by exact prefixLift 1412514
  have htrace : WordTrace (prefixWord ++ tailWord_1412514) baseStart_1412514 baseEnd_1412514 := by
    simpa [prefixWord, tailWord_1412514, baseEnd_1412514] using wordTrace_append hprefix tailTrace_1412514
  have hstable : (prefixWord ++ tailWord_1412514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412514).length < 2 ^ (prefixWord ++ tailWord_1412514).sum := by decide
  have hdescent : baseEnd_1412514 < baseStart_1412514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412555 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 1, 6]
def baseStart_1412555 : Nat := 118140960795 + 1412555 * 2 ^ 59
def prefixEnd_1412555 : Nat := 4983230072969 + 3 ^ 40 * 1412555 * 2
def baseEnd_1412555 : Nat := 483546443941217403844189

theorem tailTrace_1412555 : CollatzResearch.WordTrace tailWord_1412555 prefixEnd_1412555 483546443941217403844189 := by
  unfold tailWord_1412555
  simp only [CollatzResearch.WordTrace]
  refine ⟨51520113397561955032599119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34346742265041303355066079 51520113397561955032599119)
  ·
    refine ⟨77280170096342932548898679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51520113397561955032599119 77280170096342932548898679)
    ·
      refine ⟨115920255144514398823348019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77280170096342932548898679 115920255144514398823348019)
      ·
        refine ⟨173880382716771598235022029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115920255144514398823348019 173880382716771598235022029)
        ·
          refine ⟨65205143518789349338133261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173880382716771598235022029 65205143518789349338133261)
          ·
            refine ⟨24451928819546006001799973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65205143518789349338133261 24451928819546006001799973)
            ·
              refine ⟨4584736653664876125337495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24451928819546006001799973 4584736653664876125337495)
              ·
                refine ⟨6877104980497314188006243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4584736653664876125337495 6877104980497314188006243)
                ·
                  refine ⟨10315657470745971282009365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6877104980497314188006243 10315657470745971282009365)
                  ·
                    refine ⟨483546443941217403844189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10315657470745971282009365 483546443941217403844189)
                    ·
                      rfl

theorem cell22_1412555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 6].length) (baseStart_1412555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412555 prefixEnd_1412555 := by exact prefixLift 1412555
  have htrace : WordTrace (prefixWord ++ tailWord_1412555) baseStart_1412555 baseEnd_1412555 := by
    simpa [prefixWord, tailWord_1412555, baseEnd_1412555] using wordTrace_append hprefix tailTrace_1412555
  have hstable : (prefixWord ++ tailWord_1412555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412555).length < 2 ^ (prefixWord ++ tailWord_1412555).sum := by decide
  have hdescent : baseEnd_1412555 < baseStart_1412555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412570 : List Nat := [3, 1, 1, 2, 3, 2, 10]
def baseStart_1412570 : Nat := 118140960795 + 1412570 * 2 ^ 59
def prefixEnd_1412570 : Nat := 4983230072969 + 3 ^ 40 * 1412570 * 2
def baseEnd_1412570 : Nat := 17909317731398606100709

theorem tailTrace_1412570 : CollatzResearch.WordTrace tailWord_1412570 prefixEnd_1412570 17909317731398606100709 := by
  unfold tailWord_1412570
  simp only [CollatzResearch.WordTrace]
  refine ⟨12880165123126903148598791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34347106995005075062930109 12880165123126903148598791)
  ·
    refine ⟨19320247684690354722898187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12880165123126903148598791 19320247684690354722898187)
    ·
      refine ⟨28980371527035532084347281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19320247684690354722898187 28980371527035532084347281)
      ·
        refine ⟨21735278645276649063260461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28980371527035532084347281 21735278645276649063260461)
        ·
          refine ⟨8150729491978743398722673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21735278645276649063260461 8150729491978743398722673)
          ·
            refine ⟨6113047118984057549042005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8150729491978743398722673 6113047118984057549042005)
            ·
              refine ⟨17909317731398606100709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6113047118984057549042005 17909317731398606100709)
              ·
                rfl

theorem cell22_1412570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 10].length) (baseStart_1412570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412570 prefixEnd_1412570 := by exact prefixLift 1412570
  have htrace : WordTrace (prefixWord ++ tailWord_1412570) baseStart_1412570 baseEnd_1412570 := by
    simpa [prefixWord, tailWord_1412570, baseEnd_1412570] using wordTrace_append hprefix tailTrace_1412570
  have hstable : (prefixWord ++ tailWord_1412570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412570).length < 2 ^ (prefixWord ++ tailWord_1412570).sum := by decide
  have hdescent : baseEnd_1412570 < baseStart_1412570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412602 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 5, 3]
def baseStart_1412602 : Nat := 118140960795 + 1412602 * 2 ^ 59
def prefixEnd_1412602 : Nat := 4983230072969 + 3 ^ 40 * 1412602 * 2
def baseEnd_1412602 : Nat := 483562533001724947919045

theorem tailTrace_1412602 : CollatzResearch.WordTrace tailWord_1412602 prefixEnd_1412602 483562533001724947919045 := by
  unfold tailWord_1412602
  simp only [CollatzResearch.WordTrace]
  refine ⟨12880456907097920514890015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34347885085594454706373373 12880456907097920514890015)
  ·
    refine ⟨19320685360646880772335023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12880456907097920514890015 19320685360646880772335023)
    ·
      refine ⟨28981028040970321158502535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19320685360646880772335023 28981028040970321158502535)
      ·
        refine ⟨43471542061455481737753803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28981028040970321158502535 43471542061455481737753803)
        ·
          refine ⟨65207313092183222606630705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43471542061455481737753803 65207313092183222606630705)
          ·
            refine ⟨48905484819137416954973029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65207313092183222606630705 48905484819137416954973029)
            ·
              refine ⟨9169778403588265679057443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48905484819137416954973029 9169778403588265679057443)
              ·
                refine ⟨13754667605382398518586165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9169778403588265679057443 13754667605382398518586165)
                ·
                  refine ⟨1289500088004599861117453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13754667605382398518586165 1289500088004599861117453)
                  ·
                    refine ⟨483562533001724947919045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1289500088004599861117453 483562533001724947919045)
                    ·
                      rfl

theorem cell22_1412602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 5, 3].length) (baseStart_1412602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412602 prefixEnd_1412602 := by exact prefixLift 1412602
  have htrace : WordTrace (prefixWord ++ tailWord_1412602) baseStart_1412602 baseEnd_1412602 := by
    simpa [prefixWord, tailWord_1412602, baseEnd_1412602] using wordTrace_append hprefix tailTrace_1412602
  have hstable : (prefixWord ++ tailWord_1412602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412602).length < 2 ^ (prefixWord ++ tailWord_1412602).sum := by decide
  have hdescent : baseEnd_1412602 < baseStart_1412602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412621 : List Nat := [1, 7, 1, 1, 3, 9]
def baseStart_1412621 : Nat := 118140960795 + 1412621 * 2 ^ 59
def prefixEnd_1412621 : Nat := 4983230072969 + 3 ^ 40 * 1412621 * 2
def baseEnd_1412621 : Nat := 5969988112222410267827

theorem tailTrace_1412621 : CollatzResearch.WordTrace tailWord_1412621 prefixEnd_1412621 5969988112222410267827 := by
  unfold tailWord_1412621
  simp only [CollatzResearch.WordTrace]
  refine ⟨51522520615322848304501717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34348347076881898869667811 51522520615322848304501717)
  ·
    refine ⟨1207559076921629257136759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 51522520615322848304501717 1207559076921629257136759)
    ·
      refine ⟨1811338615382443885705139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1207559076921629257136759 1811338615382443885705139)
      ·
        refine ⟨2717007923073665828557709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1811338615382443885705139 2717007923073665828557709)
        ·
          refine ⟨1018877971152624685709141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2717007923073665828557709 1018877971152624685709141)
          ·
            refine ⟨5969988112222410267827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1018877971152624685709141 5969988112222410267827)
            ·
              rfl

theorem cell22_1412621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 9].length) (baseStart_1412621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412621 prefixEnd_1412621 := by exact prefixLift 1412621
  have htrace : WordTrace (prefixWord ++ tailWord_1412621) baseStart_1412621 baseEnd_1412621 := by
    simpa [prefixWord, tailWord_1412621, baseEnd_1412621] using wordTrace_append hprefix tailTrace_1412621
  have hstable : (prefixWord ++ tailWord_1412621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412621).length < 2 ^ (prefixWord ++ tailWord_1412621).sum := by decide
  have hdescent : baseEnd_1412621 < baseStart_1412621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412636 : List Nat := [2, 2, 3, 1, 2, 1, 3, 4, 1, 3]
def baseStart_1412636 : Nat := 118140960795 + 1412636 * 2 ^ 59
def prefixEnd_1412636 : Nat := 4983230072969 + 3 ^ 40 * 1412636 * 2
def baseEnd_1412636 : Nat := 483574171896560192568941

theorem tailTrace_1412636 : CollatzResearch.WordTrace tailWord_1412636 prefixEnd_1412636 483574171896560192568941 := by
  unfold tailWord_1412636
  simp only [CollatzResearch.WordTrace]
  refine ⟨25761533855134252933148881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34348711806845670577531841 25761533855134252933148881)
  ·
    refine ⟨19321150391350689699861661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25761533855134252933148881 19321150391350689699861661)
    ·
      refine ⟨7245431396756508637448123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19321150391350689699861661 7245431396756508637448123)
      ·
        refine ⟨10868147095134762956172185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7245431396756508637448123 10868147095134762956172185)
        ·
          refine ⟨8151110321351072217129139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10868147095134762956172185 8151110321351072217129139)
          ·
            refine ⟨12226665482026608325693709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8151110321351072217129139 12226665482026608325693709)
            ·
              refine ⟨4584999555759978122135141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12226665482026608325693709 4584999555759978122135141)
              ·
                refine ⟨859687416704995897900339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4584999555759978122135141 859687416704995897900339)
                ·
                  refine ⟨1289531125057493846850509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859687416704995897900339 1289531125057493846850509)
                  ·
                    refine ⟨483574171896560192568941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1289531125057493846850509 483574171896560192568941)
                    ·
                      rfl

theorem cell22_1412636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_1412636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412636 prefixEnd_1412636 := by exact prefixLift 1412636
  have htrace : WordTrace (prefixWord ++ tailWord_1412636) baseStart_1412636 baseEnd_1412636 := by
    simpa [prefixWord, tailWord_1412636, baseEnd_1412636] using wordTrace_append hprefix tailTrace_1412636
  have hstable : (prefixWord ++ tailWord_1412636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412636).length < 2 ^ (prefixWord ++ tailWord_1412636).sum := by decide
  have hdescent : baseEnd_1412636 < baseStart_1412636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412707 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 1, 6]
def baseStart_1412707 : Nat := 118140960795 + 1412707 * 2 ^ 59
def prefixEnd_1412707 : Nat := 4983230072969 + 3 ^ 40 * 1412707 * 2
def baseEnd_1412707 : Nat := 483598476647539674043723

theorem tailTrace_1412707 : CollatzResearch.WordTrace tailWord_1412707 prefixEnd_1412707 483598476647539674043723 := by
  unfold tailWord_1412707
  simp only [CollatzResearch.WordTrace]
  refine ⟨51525657293011284992132375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34350438195340856661421583 51525657293011284992132375)
  ·
    refine ⟨77288485939516927488198563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51525657293011284992132375 77288485939516927488198563)
    ·
      refine ⟨115932728909275391232297845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77288485939516927488198563 115932728909275391232297845)
      ·
        refine ⟨10868693335244567928027923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115932728909275391232297845 10868693335244567928027923)
        ·
          refine ⟨16303040002866851892041885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10868693335244567928027923 16303040002866851892041885)
          ·
            refine ⟨6113640001075069459515707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16303040002866851892041885 6113640001075069459515707)
            ·
              refine ⟨9170460001612604189273561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6113640001075069459515707 9170460001612604189273561)
              ·
                refine ⟨6877845001209453141955171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9170460001612604189273561 6877845001209453141955171)
                ·
                  refine ⟨10316767501814179712932757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6877845001209453141955171 10316767501814179712932757)
                  ·
                    refine ⟨483598476647539674043723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10316767501814179712932757 483598476647539674043723)
                    ·
                      rfl

theorem cell22_1412707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 6].length) (baseStart_1412707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412707 prefixEnd_1412707 := by exact prefixLift 1412707
  have htrace : WordTrace (prefixWord ++ tailWord_1412707) baseStart_1412707 baseEnd_1412707 := by
    simpa [prefixWord, tailWord_1412707, baseEnd_1412707] using wordTrace_append hprefix tailTrace_1412707
  have hstable : (prefixWord ++ tailWord_1412707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412707).length < 2 ^ (prefixWord ++ tailWord_1412707).sum := by decide
  have hdescent : baseEnd_1412707 < baseStart_1412707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412709 : List Nat := [1, 3, 1, 3, 3, 1, 3, 1, 1, 5]
def baseStart_1412709 : Nat := 118140960795 + 1412709 * 2 ^ 59
def prefixEnd_1412709 : Nat := 4983230072969 + 3 ^ 40 * 1412709 * 2
def baseEnd_1412709 : Nat := 483599161288412335493717

theorem tailTrace_1412709 : CollatzResearch.WordTrace tailWord_1412709 prefixEnd_1412709 483599161288412335493717 := by
  unfold tailWord_1412709
  simp only [CollatzResearch.WordTrace]
  refine ⟨51525730239004039333705181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34350486826002692889136787 51525730239004039333705181)
  ·
    refine ⟨19322148839626514750139443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51525730239004039333705181 19322148839626514750139443)
    ·
      refine ⟨28983223259439772125209165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19322148839626514750139443 28983223259439772125209165)
      ·
        refine ⟨10868708722289914546953437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28983223259439772125209165 10868708722289914546953437)
        ·
          refine ⟨4075765770858717955107539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10868708722289914546953437 4075765770858717955107539)
          ·
            refine ⟨6113648656288076932661309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4075765770858717955107539 6113648656288076932661309)
            ·
              refine ⟨2292618246108028849747991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6113648656288076932661309 2292618246108028849747991)
              ·
                refine ⟨3438927369162043274621987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2292618246108028849747991 3438927369162043274621987)
                ·
                  refine ⟨5158391053743064911932981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3438927369162043274621987 5158391053743064911932981)
                  ·
                    refine ⟨483599161288412335493717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5158391053743064911932981 483599161288412335493717)
                    ·
                      rfl

theorem cell22_1412709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_1412709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412709 prefixEnd_1412709 := by exact prefixLift 1412709
  have htrace : WordTrace (prefixWord ++ tailWord_1412709) baseStart_1412709 baseEnd_1412709 := by
    simpa [prefixWord, tailWord_1412709, baseEnd_1412709] using wordTrace_append hprefix tailTrace_1412709
  have hstable : (prefixWord ++ tailWord_1412709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412709).length < 2 ^ (prefixWord ++ tailWord_1412709).sum := by decide
  have hdescent : baseEnd_1412709 < baseStart_1412709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412726 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 4, 3]
def baseStart_1412726 : Nat := 118140960795 + 1412726 * 2 ^ 59
def prefixEnd_1412726 : Nat := 4983230072969 + 3 ^ 40 * 1412726 * 2
def baseEnd_1412726 : Nat := 483604980735829957818665

theorem tailTrace_1412726 : CollatzResearch.WordTrace tailWord_1412726 prefixEnd_1412726 483604980735829957818665 := by
  unfold tailWord_1412726
  simp only [CollatzResearch.WordTrace]
  refine ⟨3220396892496403202317127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34350900186628300824716021 3220396892496403202317127)
  ·
    refine ⟨4830595338744604803475691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3220396892496403202317127 4830595338744604803475691)
    ·
      refine ⟨7245893008116907205213537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4830595338744604803475691 7245893008116907205213537)
      ·
        refine ⟨5434419756087680403910153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7245893008116907205213537 5434419756087680403910153)
        ·
          refine ⟨4075814817065760302932615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5434419756087680403910153 4075814817065760302932615)
          ·
            refine ⟨6113722225598640454398923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4075814817065760302932615 6113722225598640454398923)
            ·
              refine ⟨9170583338397960681598385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6113722225598640454398923 9170583338397960681598385)
              ·
                refine ⟨6877937503798470511198789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9170583338397960681598385 6877937503798470511198789)
                ·
                  refine ⟨1289613281962213220849773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6877937503798470511198789 1289613281962213220849773)
                  ·
                    refine ⟨483604980735829957818665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1289613281962213220849773 483604980735829957818665)
                    ·
                      rfl

theorem cell22_1412726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_1412726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412726 prefixEnd_1412726 := by exact prefixLift 1412726
  have htrace : WordTrace (prefixWord ++ tailWord_1412726) baseStart_1412726 baseEnd_1412726 := by
    simpa [prefixWord, tailWord_1412726, baseEnd_1412726] using wordTrace_append hprefix tailTrace_1412726
  have hstable : (prefixWord ++ tailWord_1412726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412726).length < 2 ^ (prefixWord ++ tailWord_1412726).sum := by decide
  have hdescent : baseEnd_1412726 < baseStart_1412726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412756 : List Nat := [2, 4, 2, 2, 2, 1, 2, 7]
def baseStart_1412756 : Nat := 118140960795 + 1412756 * 2 ^ 59
def prefixEnd_1412756 : Nat := 4983230072969 + 3 ^ 40 * 1412756 * 2
def baseEnd_1412756 : Nat := 53735027816546653285397

theorem tailTrace_1412756 : CollatzResearch.WordTrace tailWord_1412756 prefixEnd_1412756 53735027816546653285397 := by
  unfold tailWord_1412756
  simp only [CollatzResearch.WordTrace]
  refine ⟨25763722234916883180333061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34351629646555844240444081 25763722234916883180333061)
  ·
    refine ⟨4830697919046915596312449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25763722234916883180333061 4830697919046915596312449)
    ·
      refine ⟨3623023439285186697234337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4830697919046915596312449 3623023439285186697234337)
      ·
        refine ⟨2717267579463890022925753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3623023439285186697234337 2717267579463890022925753)
        ·
          refine ⟨2037950684597917517194315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2717267579463890022925753 2037950684597917517194315)
          ·
            refine ⟨3056926026896876275791473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2037950684597917517194315 3056926026896876275791473)
            ·
              refine ⟨2292694520172657206843605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3056926026896876275791473 2292694520172657206843605)
              ·
                refine ⟨53735027816546653285397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2292694520172657206843605 53735027816546653285397)
                ·
                  rfl

theorem cell22_1412756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 7].length) (baseStart_1412756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412756 prefixEnd_1412756 := by exact prefixLift 1412756
  have htrace : WordTrace (prefixWord ++ tailWord_1412756) baseStart_1412756 baseEnd_1412756 := by
    simpa [prefixWord, tailWord_1412756, baseEnd_1412756] using wordTrace_append hprefix tailTrace_1412756
  have hstable : (prefixWord ++ tailWord_1412756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412756).length < 2 ^ (prefixWord ++ tailWord_1412756).sum := by decide
  have hdescent : baseEnd_1412756 < baseStart_1412756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412814 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 5, 4]
def baseStart_1412814 : Nat := 118140960795 + 1412814 * 2 ^ 59
def prefixEnd_1412814 : Nat := 4983230072969 + 3 ^ 40 * 1412814 * 2
def baseEnd_1412814 : Nat := 483635104934227061618395

theorem tailTrace_1412814 : CollatzResearch.WordTrace tailWord_1412814 prefixEnd_1412814 483635104934227061618395 := by
  unfold tailWord_1412814
  simp only [CollatzResearch.WordTrace]
  refine ⟨6441194987952955283284687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34353039935749094844184997 6441194987952955283284687)
  ·
    refine ⟨9661792481929432924927031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6441194987952955283284687 9661792481929432924927031)
    ·
      refine ⟨14492688722894149387390547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9661792481929432924927031 14492688722894149387390547)
      ·
        refine ⟨21739033084341224081085821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14492688722894149387390547 21739033084341224081085821)
        ·
          refine ⟨8152137406627959030407183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21739033084341224081085821 8152137406627959030407183)
          ·
            refine ⟨12228206109941938545610775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8152137406627959030407183 12228206109941938545610775)
            ·
              refine ⟨18342309164912907818416163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12228206109941938545610775 18342309164912907818416163)
              ·
                refine ⟨27513463747369361727624245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18342309164912907818416163 27513463747369361727624245)
                ·
                  refine ⟨2579387226315877661964773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27513463747369361727624245 2579387226315877661964773)
                  ·
                    refine ⟨483635104934227061618395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2579387226315877661964773 483635104934227061618395)
                    ·
                      rfl

theorem cell22_1412814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_1412814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412814 prefixEnd_1412814 := by exact prefixLift 1412814
  have htrace : WordTrace (prefixWord ++ tailWord_1412814) baseStart_1412814 baseEnd_1412814 := by
    simpa [prefixWord, tailWord_1412814, baseEnd_1412814] using wordTrace_append hprefix tailTrace_1412814
  have hstable : (prefixWord ++ tailWord_1412814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412814).length < 2 ^ (prefixWord ++ tailWord_1412814).sum := by decide
  have hdescent : baseEnd_1412814 < baseStart_1412814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412844 : List Nat := [2, 2, 1, 1, 2, 2, 4, 2, 1, 5]
def baseStart_1412844 : Nat := 118140960795 + 1412844 * 2 ^ 59
def prefixEnd_1412844 : Nat := 4983230072969 + 3 ^ 40 * 1412844 * 2
def baseEnd_1412844 : Nat := 483645374547316983368303

theorem tailTrace_1412844 : CollatzResearch.WordTrace tailWord_1412844 prefixEnd_1412844 483645374547316983368303 := by
  unfold tailWord_1412844
  simp only [CollatzResearch.WordTrace]
  refine ⟨25765327046757478694934793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34353769395676638259913057 25765327046757478694934793)
  ·
    refine ⟨19323995285068109021201095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25765327046757478694934793 19323995285068109021201095)
    ·
      refine ⟨28985992927602163531801643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19323995285068109021201095 28985992927602163531801643)
      ·
        refine ⟨43478989391403245297702465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28985992927602163531801643 43478989391403245297702465)
        ·
          refine ⟨32609242043552433973276849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43478989391403245297702465 32609242043552433973276849)
          ·
            refine ⟨24456931532664325479957637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32609242043552433973276849 24456931532664325479957637)
            ·
              refine ⟨4585674662374561027492057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24456931532664325479957637 4585674662374561027492057)
              ·
                refine ⟨3439255996780920770619043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4585674662374561027492057 3439255996780920770619043)
                ·
                  refine ⟨5158883995171381155928565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3439255996780920770619043 5158883995171381155928565)
                  ·
                    refine ⟨483645374547316983368303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5158883995171381155928565 483645374547316983368303)
                    ·
                      rfl

theorem cell22_1412844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_1412844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412844 prefixEnd_1412844 := by exact prefixLift 1412844
  have htrace : WordTrace (prefixWord ++ tailWord_1412844) baseStart_1412844 baseEnd_1412844 := by
    simpa [prefixWord, tailWord_1412844, baseEnd_1412844] using wordTrace_append hprefix tailTrace_1412844
  have hstable : (prefixWord ++ tailWord_1412844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412844).length < 2 ^ (prefixWord ++ tailWord_1412844).sum := by decide
  have hdescent : baseEnd_1412844 < baseStart_1412844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412861 : List Nat := [1, 4, 1, 1, 1, 1, 2, 6, 2, 3]
def baseStart_1412861 : Nat := 118140960795 + 1412861 * 2 ^ 59
def prefixEnd_1412861 : Nat := 4983230072969 + 3 ^ 40 * 1412861 * 2
def baseEnd_1412861 : Nat := 483651193994734605693251

theorem tailTrace_1412861 : CollatzResearch.WordTrace tailWord_1412861 prefixEnd_1412861 483651193994734605693251 := by
  unfold tailWord_1412861
  simp only [CollatzResearch.WordTrace]
  refine ⟨51531274134453369293238437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34354182756302246195492291 51531274134453369293238437)
  ·
    refine ⟨9662113900210006742482207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51531274134453369293238437 9662113900210006742482207)
    ·
      refine ⟨14493170850315010113723311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9662113900210006742482207 14493170850315010113723311)
      ·
        refine ⟨21739756275472515170584967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14493170850315010113723311 21739756275472515170584967)
        ·
          refine ⟨32609634413208772755877451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21739756275472515170584967 32609634413208772755877451)
          ·
            refine ⟨48914451619813159133816177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32609634413208772755877451 48914451619813159133816177)
            ·
              refine ⟨36685838714859869350362133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48914451619813159133816177 36685838714859869350362133)
              ·
                refine ⟨1719648689759056375798225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36685838714859869350362133 1719648689759056375798225)
                ·
                  refine ⟨1289736517319292281848669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1719648689759056375798225 1289736517319292281848669)
                  ·
                    refine ⟨483651193994734605693251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1289736517319292281848669 483651193994734605693251)
                    ·
                      rfl

theorem cell22_1412861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_1412861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412861 prefixEnd_1412861 := by exact prefixLift 1412861
  have htrace : WordTrace (prefixWord ++ tailWord_1412861) baseStart_1412861 baseEnd_1412861 := by
    simpa [prefixWord, tailWord_1412861, baseEnd_1412861] using wordTrace_append hprefix tailTrace_1412861
  have hstable : (prefixWord ++ tailWord_1412861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412861).length < 2 ^ (prefixWord ++ tailWord_1412861).sum := by decide
  have hdescent : baseEnd_1412861 < baseStart_1412861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412936 : List Nat := [2, 1, 3, 1, 1, 5, 1, 3, 5]
def baseStart_1412936 : Nat := 118140960795 + 1412936 * 2 ^ 59
def prefixEnd_1412936 : Nat := 4983230072969 + 3 ^ 40 * 1412936 * 2
def baseEnd_1412936 : Nat := 161225622675819803356007

theorem tailTrace_1412936 : CollatzResearch.WordTrace tailWord_1412936 prefixEnd_1412936 161225622675819803356007 := by
  unfold tailWord_1412936
  simp only [CollatzResearch.WordTrace]
  refine ⟨25767004804590828551109331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34356006406121104734812441 25767004804590828551109331)
  ·
    refine ⟨38650507206886242826663997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25767004804590828551109331 38650507206886242826663997)
    ·
      refine ⟨14493940202582341059998999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38650507206886242826663997 14493940202582341059998999)
      ·
        refine ⟨21740910303873511589998499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14493940202582341059998999 21740910303873511589998499)
        ·
          refine ⟨32611365455810267384997749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21740910303873511589998499 32611365455810267384997749)
          ·
            refine ⟨3057315511482212567343539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32611365455810267384997749 3057315511482212567343539)
            ·
              refine ⟨4585973267223318851015309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3057315511482212567343539 4585973267223318851015309)
              ·
                refine ⟨1719739975208744569130741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4585973267223318851015309 1719739975208744569130741)
                ·
                  refine ⟨161225622675819803356007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1719739975208744569130741 161225622675819803356007)
                  ·
                    rfl

theorem cell22_1412936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 5].length) (baseStart_1412936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412936 prefixEnd_1412936 := by exact prefixLift 1412936
  have htrace : WordTrace (prefixWord ++ tailWord_1412936) baseStart_1412936 baseEnd_1412936 := by
    simpa [prefixWord, tailWord_1412936, baseEnd_1412936] using wordTrace_append hprefix tailTrace_1412936
  have hstable : (prefixWord ++ tailWord_1412936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412936).length < 2 ^ (prefixWord ++ tailWord_1412936).sum := by decide
  have hdescent : baseEnd_1412936 < baseStart_1412936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412970 : List Nat := [3, 1, 3, 4, 1, 1, 2, 2, 5]
def baseStart_1412970 : Nat := 118140960795 + 1412970 * 2 ^ 59
def prefixEnd_1412970 : Nat := 4983230072969 + 3 ^ 40 * 1412970 * 2
def baseEnd_1412970 : Nat := 161229502307431551572639

theorem tailTrace_1412970 : CollatzResearch.WordTrace tailWord_1412970 prefixEnd_1412970 161229502307431551572639 := by
  unfold tailWord_1412970
  simp only [CollatzResearch.WordTrace]
  refine ⟨12883812422764620227239091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34356833127372320605970909 12883812422764620227239091)
  ·
    refine ⟨19325718634146930340858637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12883812422764620227239091 19325718634146930340858637)
    ·
      refine ⟨7247144487805098877821989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19325718634146930340858637 7247144487805098877821989)
      ·
        refine ⟨1358839591463456039591623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7247144487805098877821989 1358839591463456039591623)
        ·
          refine ⟨2038259387195184059387435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1358839591463456039591623 2038259387195184059387435)
          ·
            refine ⟨3057389080792776089081153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2038259387195184059387435 3057389080792776089081153)
            ·
              refine ⟨2293041810594582066810865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3057389080792776089081153 2293041810594582066810865)
              ·
                refine ⟨1719781357945936550108149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2293041810594582066810865 1719781357945936550108149)
                ·
                  refine ⟨161229502307431551572639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1719781357945936550108149 161229502307431551572639)
                  ·
                    rfl

theorem cell22_1412970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 5].length) (baseStart_1412970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412970 prefixEnd_1412970 := by exact prefixLift 1412970
  have htrace : WordTrace (prefixWord ++ tailWord_1412970) baseStart_1412970 baseEnd_1412970 := by
    simpa [prefixWord, tailWord_1412970, baseEnd_1412970] using wordTrace_append hprefix tailTrace_1412970
  have hstable : (prefixWord ++ tailWord_1412970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412970).length < 2 ^ (prefixWord ++ tailWord_1412970).sum := by decide
  have hdescent : baseEnd_1412970 < baseStart_1412970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412974 : List Nat := [4, 1, 2, 3, 1, 3, 2, 2, 1, 3]
def baseStart_1412974 : Nat := 118140960795 + 1412974 * 2 ^ 59
def prefixEnd_1412974 : Nat := 4983230072969 + 3 ^ 40 * 1412974 * 2
def baseEnd_1412974 : Nat := 483689876204039977617905

theorem tailTrace_1412974 : CollatzResearch.WordTrace tailWord_1412974 prefixEnd_1412974 483689876204039977617905 := by
  unfold tailWord_1412974
  simp only [CollatzResearch.WordTrace]
  refine ⟨6441924447880498699012747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34356930388695993061401317 6441924447880498699012747)
  ·
    refine ⟨9662886671820748048519121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6441924447880498699012747 9662886671820748048519121)
    ·
      refine ⟨7247165003865561036389341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9662886671820748048519121 7247165003865561036389341)
      ·
        refine ⟨2717686876449585388646003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7247165003865561036389341 2717686876449585388646003)
        ·
          refine ⟨4076530314674378082969005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2717686876449585388646003 4076530314674378082969005)
          ·
            refine ⟨1528698868002891781113377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4076530314674378082969005 1528698868002891781113377)
            ·
              refine ⟨1146524151002168835835033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1528698868002891781113377 1146524151002168835835033)
              ·
                refine ⟨859893113251626626876275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1146524151002168835835033 859893113251626626876275)
                ·
                  refine ⟨1289839669877439940314413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859893113251626626876275 1289839669877439940314413)
                  ·
                    refine ⟨483689876204039977617905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1289839669877439940314413 483689876204039977617905)
                    ·
                      rfl

theorem cell22_1412974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_1412974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412974 prefixEnd_1412974 := by exact prefixLift 1412974
  have htrace : WordTrace (prefixWord ++ tailWord_1412974) baseStart_1412974 baseEnd_1412974 := by
    simpa [prefixWord, tailWord_1412974, baseEnd_1412974] using wordTrace_append hprefix tailTrace_1412974
  have hstable : (prefixWord ++ tailWord_1412974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412974).length < 2 ^ (prefixWord ++ tailWord_1412974).sum := by decide
  have hdescent : baseEnd_1412974 < baseStart_1412974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412979 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 5, 5]
def baseStart_1412979 : Nat := 118140960795 + 1412979 * 2 ^ 59
def prefixEnd_1412979 : Nat := 4983230072969 + 3 ^ 40 * 1412979 * 2
def baseEnd_1412979 : Nat := 483691587806221631242889

theorem tailTrace_1412979 : CollatzResearch.WordTrace tailWord_1412979 prefixEnd_1412979 483691587806221631242889 := by
  unfold tailWord_1412979
  simp only [CollatzResearch.WordTrace]
  refine ⟨51535577948025875446033991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34357051965350583630689327 51535577948025875446033991)
  ·
    refine ⟨77303366922038813169050987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51535577948025875446033991 77303366922038813169050987)
    ·
      refine ⟨115955050383058219753576481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77303366922038813169050987 115955050383058219753576481)
      ·
        refine ⟨86966287787293664815182361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115955050383058219753576481 86966287787293664815182361)
        ·
          refine ⟨65224715840470248611386771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86966287787293664815182361 65224715840470248611386771)
          ·
            refine ⟨97837073760705372917080157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65224715840470248611386771 97837073760705372917080157)
            ·
              refine ⟨36688902660264514843905059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97837073760705372917080157 36688902660264514843905059)
              ·
                refine ⟨55033353990396772265857589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36688902660264514843905059 55033353990396772265857589)
                ·
                  refine ⟨5159376936599697399924149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55033353990396772265857589 5159376936599697399924149)
                  ·
                    refine ⟨483691587806221631242889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5159376936599697399924149 483691587806221631242889)
                    ·
                      rfl

theorem cell22_1412979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 5].length) (baseStart_1412979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412979 prefixEnd_1412979 := by exact prefixLift 1412979
  have htrace : WordTrace (prefixWord ++ tailWord_1412979) baseStart_1412979 baseEnd_1412979 := by
    simpa [prefixWord, tailWord_1412979, baseEnd_1412979] using wordTrace_append hprefix tailTrace_1412979
  have hstable : (prefixWord ++ tailWord_1412979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412979).length < 2 ^ (prefixWord ++ tailWord_1412979).sum := by decide
  have hdescent : baseEnd_1412979 < baseStart_1412979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412981 : List Nat := [1, 3, 4, 1, 1, 1, 2, 3, 6]
def baseStart_1412981 : Nat := 118140960795 + 1412981 * 2 ^ 59
def prefixEnd_1412981 : Nat := 4983230072969 + 3 ^ 40 * 1412981 * 2
def baseEnd_1412981 : Nat := 161230757482364764230961

theorem tailTrace_1412981 : CollatzResearch.WordTrace tailWord_1412981 prefixEnd_1412981 161230757482364764230961 := by
  unfold tailWord_1412981
  simp only [CollatzResearch.WordTrace]
  refine ⟨51535650894018629787606797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34357100596012419858404531 51535650894018629787606797)
  ·
    refine ⟨19325869085256986170352549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51535650894018629787606797 19325869085256986170352549)
    ·
      refine ⟨3623600453485684906941103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19325869085256986170352549 3623600453485684906941103)
      ·
        refine ⟨5435400680228527360411655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3623600453485684906941103 5435400680228527360411655)
        ·
          refine ⟨8153101020342791040617483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5435400680228527360411655 8153101020342791040617483)
          ·
            refine ⟨12229651530514186560926225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8153101020342791040617483 12229651530514186560926225)
            ·
              refine ⟨9172238647885639920694669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12229651530514186560926225 9172238647885639920694669)
              ·
                refine ⟨3439589492957114970260501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9172238647885639920694669 3439589492957114970260501)
                ·
                  refine ⟨161230757482364764230961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3439589492957114970260501 161230757482364764230961)
                  ·
                    rfl

theorem cell22_1412981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_1412981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412981 prefixEnd_1412981 := by exact prefixLift 1412981
  have htrace : WordTrace (prefixWord ++ tailWord_1412981) baseStart_1412981 baseEnd_1412981 := by
    simpa [prefixWord, tailWord_1412981, baseEnd_1412981] using wordTrace_append hprefix tailTrace_1412981
  have hstable : (prefixWord ++ tailWord_1412981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412981).length < 2 ^ (prefixWord ++ tailWord_1412981).sum := by decide
  have hdescent : baseEnd_1412981 < baseStart_1412981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1412996 : List Nat := [2, 3, 2, 1, 1, 1, 3, 3, 1, 5]
def baseStart_1412996 : Nat := 118140960795 + 1412996 * 2 ^ 59
def prefixEnd_1412996 : Nat := 4983230072969 + 3 ^ 40 * 1412996 * 2
def baseEnd_1412996 : Nat := 483697407253639253567837

theorem tailTrace_1412996 : CollatzResearch.WordTrace tailWord_1412996 prefixEnd_1412996 483697407253639253567837 := by
  unfold tailWord_1412996
  simp only [CollatzResearch.WordTrace]
  refine ⟨25768098994482143674701421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34357465325976191566268561 25768098994482143674701421)
  ·
    refine ⟨9663037122930803878013033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25768098994482143674701421 9663037122930803878013033)
    ·
      refine ⟨7247277842198102908509775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9663037122930803878013033 7247277842198102908509775)
      ·
        refine ⟨10870916763297154362764663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7247277842198102908509775 10870916763297154362764663)
        ·
          refine ⟨16306375144945731544146995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10870916763297154362764663 16306375144945731544146995)
          ·
            refine ⟨24459562717418597316220493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16306375144945731544146995 24459562717418597316220493)
            ·
              refine ⟨9172336019031973993582685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24459562717418597316220493 9172336019031973993582685)
              ·
                refine ⟨3439626007136990247593507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9172336019031973993582685 3439626007136990247593507)
                ·
                  refine ⟨5159439010705485371390261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3439626007136990247593507 5159439010705485371390261)
                  ·
                    refine ⟨483697407253639253567837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5159439010705485371390261 483697407253639253567837)
                    ·
                      rfl

theorem cell22_1412996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_1412996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1412996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1412996 prefixEnd_1412996 := by exact prefixLift 1412996
  have htrace : WordTrace (prefixWord ++ tailWord_1412996) baseStart_1412996 baseEnd_1412996 := by
    simpa [prefixWord, tailWord_1412996, baseEnd_1412996] using wordTrace_append hprefix tailTrace_1412996
  have hstable : (prefixWord ++ tailWord_1412996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1412996).length < 2 ^ (prefixWord ++ tailWord_1412996).sum := by decide
  have hdescent : baseEnd_1412996 < baseStart_1412996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1412996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413009 : List Nat := [1, 2, 2, 1, 1, 1, 4, 10]
def baseStart_1413009 : Nat := 118140960795 + 1413009 * 2 ^ 59
def prefixEnd_1413009 : Nat := 4983230072969 + 3 ^ 40 * 1413009 * 2
def baseEnd_1413009 : Nat := 53744650824367950332533

theorem tailTrace_1413009 : CollatzResearch.WordTrace tailWord_1413009 prefixEnd_1413009 53744650824367950332533 := by
  unfold tailWord_1413009
  simp only [CollatzResearch.WordTrace]
  refine ⟨51536672137917190569626081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34357781425278127046417387 51536672137917190569626081)
  ·
    refine ⟨38652504103437892927219561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51536672137917190569626081 38652504103437892927219561)
    ·
      refine ⟨28989378077578419695414671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38652504103437892927219561 28989378077578419695414671)
      ·
        refine ⟨43484067116367629543122007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28989378077578419695414671 43484067116367629543122007)
        ·
          refine ⟨65226100674551444314683011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43484067116367629543122007 65226100674551444314683011)
          ·
            refine ⟨97839151011827166472024517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65226100674551444314683011 97839151011827166472024517)
            ·
              refine ⟨18344840814717593713504597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97839151011827166472024517 18344840814717593713504597)
              ·
                refine ⟨53744650824367950332533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18344840814717593713504597 53744650824367950332533)
                ·
                  rfl

theorem cell22_1413009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 10].length) (baseStart_1413009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413009 prefixEnd_1413009 := by exact prefixLift 1413009
  have htrace : WordTrace (prefixWord ++ tailWord_1413009) baseStart_1413009 baseEnd_1413009 := by
    simpa [prefixWord, tailWord_1413009, baseEnd_1413009] using wordTrace_append hprefix tailTrace_1413009
  have hstable : (prefixWord ++ tailWord_1413009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413009).length < 2 ^ (prefixWord ++ tailWord_1413009).sum := by decide
  have hdescent : baseEnd_1413009 < baseStart_1413009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413092 : List Nat := [2, 3, 1, 1, 1, 1, 7, 2, 1, 3]
def baseStart_1413092 : Nat := 118140960795 + 1413092 * 2 ^ 59
def prefixEnd_1413092 : Nat := 4983230072969 + 3 ^ 40 * 1413092 * 2
def baseEnd_1413092 : Nat := 483730270015527003167543

theorem tailTrace_1413092 : CollatzResearch.WordTrace tailWord_1413092 prefixEnd_1413092 483730270015527003167543 := by
  unfold tailWord_1413092
  simp only [CollatzResearch.WordTrace]
  refine ⟨25769849698308247872448765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34359799597744330496598353 25769849698308247872448765)
  ·
    refine ⟨9663693636865592952168287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25769849698308247872448765 9663693636865592952168287)
    ·
      refine ⟨14495540455298389428252431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9663693636865592952168287 14495540455298389428252431)
      ·
        refine ⟨21743310682947584142378647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14495540455298389428252431 21743310682947584142378647)
        ·
          refine ⟨32614966024421376213567971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21743310682947584142378647 32614966024421376213567971)
          ·
            refine ⟨48922449036632064320351957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32614966024421376213567971 48922449036632064320351957)
            ·
              refine ⟨1146619899296064007508249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 48922449036632064320351957 1146619899296064007508249)
              ·
                refine ⟨859964924472048005631187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1146619899296064007508249 859964924472048005631187)
                ·
                  refine ⟨1289947386708072008446781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859964924472048005631187 1289947386708072008446781)
                  ·
                    refine ⟨483730270015527003167543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1289947386708072008446781 483730270015527003167543)
                    ·
                      rfl

theorem cell22_1413092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_1413092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413092 prefixEnd_1413092 := by exact prefixLift 1413092
  have htrace : WordTrace (prefixWord ++ tailWord_1413092) baseStart_1413092 baseEnd_1413092 := by
    simpa [prefixWord, tailWord_1413092, baseEnd_1413092] using wordTrace_append hprefix tailTrace_1413092
  have hstable : (prefixWord ++ tailWord_1413092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413092).length < 2 ^ (prefixWord ++ tailWord_1413092).sum := by decide
  have hdescent : baseEnd_1413092 < baseStart_1413092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413116 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 8]
def baseStart_1413116 : Nat := 118140960795 + 1413116 * 2 ^ 59
def prefixEnd_1413116 : Nat := 4983230072969 + 3 ^ 40 * 1413116 * 2
def baseEnd_1413116 : Nat := 161246161901999646855823

theorem tailTrace_1413116 : CollatzResearch.WordTrace tailWord_1413116 prefixEnd_1413116 161246161901999646855823 := by
  unfold tailWord_1413116
  simp only [CollatzResearch.WordTrace]
  refine ⟨25770287374264773921885601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34360383165686365229180801 25770287374264773921885601)
  ·
    refine ⟨19327715530698580441414201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25770287374264773921885601 19327715530698580441414201)
    ·
      refine ⟨14495786648023935331060651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19327715530698580441414201 14495786648023935331060651)
      ·
        refine ⟨21743679972035902996590977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14495786648023935331060651 21743679972035902996590977)
        ·
          refine ⟨16307759979026927247443233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21743679972035902996590977 16307759979026927247443233)
          ·
            refine ⟨12230819984270195435582425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16307759979026927247443233 12230819984270195435582425)
            ·
              refine ⟨9173114988202646576686819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12230819984270195435582425 9173114988202646576686819)
              ·
                refine ⟨13759672482303969865030229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9173114988202646576686819 13759672482303969865030229)
                ·
                  refine ⟨161246161901999646855823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13759672482303969865030229 161246161901999646855823)
                  ·
                    rfl

theorem cell22_1413116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_1413116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413116 prefixEnd_1413116 := by exact prefixLift 1413116
  have htrace : WordTrace (prefixWord ++ tailWord_1413116) baseStart_1413116 baseEnd_1413116 := by
    simpa [prefixWord, tailWord_1413116, baseEnd_1413116] using wordTrace_append hprefix tailTrace_1413116
  have hstable : (prefixWord ++ tailWord_1413116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413116).length < 2 ^ (prefixWord ++ tailWord_1413116).sum := by decide
  have hdescent : baseEnd_1413116 < baseStart_1413116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413193 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 5, 3]
def baseStart_1413193 : Nat := 118140960795 + 1413193 * 2 ^ 59
def prefixEnd_1413193 : Nat := 4983230072969 + 3 ^ 40 * 1413193 * 2
def baseEnd_1413193 : Nat := 483764844379596406392233

theorem tailTrace_1413193 : CollatzResearch.WordTrace tailWord_1413193 prefixEnd_1413193 483764844379596406392233 := by
  unfold tailWord_1413193
  simp only [CollatzResearch.WordTrace]
  refine ⟨51543383169250589994324233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34362255446167059996216155 51543383169250589994324233)
  ·
    refine ⟨38657537376937942495743175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51543383169250589994324233 38657537376937942495743175)
    ·
      refine ⟨57986306065406913743614763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38657537376937942495743175 57986306065406913743614763)
      ·
        refine ⟨86979459098110370615422145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57986306065406913743614763 86979459098110370615422145)
        ·
          refine ⟨65234594323582777961566609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86979459098110370615422145 65234594323582777961566609)
          ·
            refine ⟨48925945742687083471174957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65234594323582777961566609 48925945742687083471174957)
            ·
              refine ⟨18347229653507656301690609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48925945742687083471174957 18347229653507656301690609)
              ·
                refine ⟨13760422240130742226267957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18347229653507656301690609 13760422240130742226267957)
                ·
                  refine ⟨1290039585012257083712621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13760422240130742226267957 1290039585012257083712621)
                  ·
                    refine ⟨483764844379596406392233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1290039585012257083712621 483764844379596406392233)
                    ·
                      rfl

theorem cell22_1413193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 3].length) (baseStart_1413193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413193 prefixEnd_1413193 := by exact prefixLift 1413193
  have htrace : WordTrace (prefixWord ++ tailWord_1413193) baseStart_1413193 baseEnd_1413193 := by
    simpa [prefixWord, tailWord_1413193, baseEnd_1413193] using wordTrace_append hprefix tailTrace_1413193
  have hstable : (prefixWord ++ tailWord_1413193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413193).length < 2 ^ (prefixWord ++ tailWord_1413193).sum := by decide
  have hdescent : baseEnd_1413193 < baseStart_1413193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413210 : List Nat := [3, 1, 1, 2, 1, 1, 6, 1, 3, 3]
def baseStart_1413210 : Nat := 118140960795 + 1413210 * 2 ^ 59
def prefixEnd_1413210 : Nat := 4983230072969 + 3 ^ 40 * 1413210 * 2
def baseEnd_1413210 : Nat := 483770663827014028717181

theorem tailTrace_1413210 : CollatzResearch.WordTrace tailWord_1413210 prefixEnd_1413210 483770663827014028717181 := by
  unfold tailWord_1413210
  simp only [CollatzResearch.WordTrace]
  refine ⟨12886000802547250474423271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34362668806792667931795389 12886000802547250474423271)
  ·
    refine ⟨19329001203820875711634907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12886000802547250474423271 19329001203820875711634907)
    ·
      refine ⟨28993501805731313567452361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19329001203820875711634907 28993501805731313567452361)
      ·
        refine ⟨21745126354298485175589271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28993501805731313567452361 21745126354298485175589271)
        ·
          refine ⟨32617689531447727763383907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21745126354298485175589271 32617689531447727763383907)
          ·
            refine ⟨48926534297171591645075861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32617689531447727763383907 48926534297171591645075861)
            ·
              refine ⟨2293431295179918358362931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48926534297171591645075861 2293431295179918358362931)
              ·
                refine ⟨3440146942769877537544397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2293431295179918358362931 3440146942769877537544397)
                ·
                  refine ⟨1290055103538704076579149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3440146942769877537544397 1290055103538704076579149)
                  ·
                    refine ⟨483770663827014028717181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1290055103538704076579149 483770663827014028717181)
                    ·
                      rfl

theorem cell22_1413210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_1413210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413210 prefixEnd_1413210 := by exact prefixLift 1413210
  have htrace : WordTrace (prefixWord ++ tailWord_1413210) baseStart_1413210 baseEnd_1413210 := by
    simpa [prefixWord, tailWord_1413210, baseEnd_1413210] using wordTrace_append hprefix tailTrace_1413210
  have hstable : (prefixWord ++ tailWord_1413210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413210).length < 2 ^ (prefixWord ++ tailWord_1413210).sum := by decide
  have hdescent : baseEnd_1413210 < baseStart_1413210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413244 : List Nat := [2, 2, 2, 1, 1, 6, 1, 3, 1, 3]
def baseStart_1413244 : Nat := 118140960795 + 1413244 * 2 ^ 59
def prefixEnd_1413244 : Nat := 4983230072969 + 3 ^ 40 * 1413244 * 2
def baseEnd_1413244 : Nat := 483782302721849273367077

theorem tailTrace_1413244 : CollatzResearch.WordTrace tailWord_1413244 prefixEnd_1413244 483782302721849273367077 := by
  unfold tailWord_1413244
  simp only [CollatzResearch.WordTrace]
  refine ⟨25772621646032912852215393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34363495528043883802953857 25772621646032912852215393)
  ·
    refine ⟨19329466234524684639161545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25772621646032912852215393 19329466234524684639161545)
    ·
      refine ⟨14497099675893513479371159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19329466234524684639161545 14497099675893513479371159)
      ·
        refine ⟨21745649513840270219056739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14497099675893513479371159 21745649513840270219056739)
        ·
          refine ⟨32618474270760405328585109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21745649513840270219056739 32618474270760405328585109)
          ·
            refine ⟨1528990981441893999777427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32618474270760405328585109 1528990981441893999777427)
            ·
              refine ⟨2293486472162840999666141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1528990981441893999777427 2293486472162840999666141)
              ·
                refine ⟨860057427061065374874803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2293486472162840999666141 860057427061065374874803)
                ·
                  refine ⟨1290086140591598062312205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 860057427061065374874803 1290086140591598062312205)
                  ·
                    refine ⟨483782302721849273367077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1290086140591598062312205 483782302721849273367077)
                    ·
                      rfl

theorem cell22_1413244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_1413244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413244 prefixEnd_1413244 := by exact prefixLift 1413244
  have htrace : WordTrace (prefixWord ++ tailWord_1413244) baseStart_1413244 baseEnd_1413244 := by
    simpa [prefixWord, tailWord_1413244, baseEnd_1413244] using wordTrace_append hprefix tailTrace_1413244
  have hstable : (prefixWord ++ tailWord_1413244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413244).length < 2 ^ (prefixWord ++ tailWord_1413244).sum := by decide
  have hdescent : baseEnd_1413244 < baseStart_1413244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413274 : List Nat := [3, 1, 1, 5, 2, 2, 2, 1, 5]
def baseStart_1413274 : Nat := 118140960795 + 1413274 * 2 ^ 59
def prefixEnd_1413274 : Nat := 4983230072969 + 3 ^ 40 * 1413274 * 2
def baseEnd_1413274 : Nat := 161264190778313065038995

theorem tailTrace_1413274 : CollatzResearch.WordTrace tailWord_1413274 prefixEnd_1413274 161264190778313065038995 := by
  unfold tailWord_1413274
  simp only [CollatzResearch.WordTrace]
  refine ⟨12886584370489285207005719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34364224987971427218681917 12886584370489285207005719)
  ·
    refine ⟨19329876555733927810508579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12886584370489285207005719 19329876555733927810508579)
    ·
      refine ⟨28994814833600891715762869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19329876555733927810508579 28994814833600891715762869)
      ·
        refine ⟨2718263890650083598352769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28994814833600891715762869 2718263890650083598352769)
        ·
          refine ⟨2038697917987562698764577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2718263890650083598352769 2038697917987562698764577)
          ·
            refine ⟨1529023438490672024073433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2038697917987562698764577 1529023438490672024073433)
            ·
              refine ⟨1146767578868004018055075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1529023438490672024073433 1146767578868004018055075)
              ·
                refine ⟨1720151368302006027082613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1146767578868004018055075 1720151368302006027082613)
                ·
                  refine ⟨161264190778313065038995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1720151368302006027082613 161264190778313065038995)
                  ·
                    rfl

theorem cell22_1413274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 5].length) (baseStart_1413274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413274 prefixEnd_1413274 := by exact prefixLift 1413274
  have htrace : WordTrace (prefixWord ++ tailWord_1413274) baseStart_1413274 baseEnd_1413274 := by
    simpa [prefixWord, tailWord_1413274, baseEnd_1413274] using wordTrace_append hprefix tailTrace_1413274
  have hstable : (prefixWord ++ tailWord_1413274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413274).length < 2 ^ (prefixWord ++ tailWord_1413274).sum := by decide
  have hdescent : baseEnd_1413274 < baseStart_1413274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413287 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 3, 4]
def baseStart_1413287 : Nat := 118140960795 + 1413287 * 2 ^ 59
def prefixEnd_1413287 : Nat := 4983230072969 + 3 ^ 40 * 1413287 * 2
def baseEnd_1413287 : Nat := 483797022500611494541945

theorem tailTrace_1413287 : CollatzResearch.WordTrace tailWord_1413287 prefixEnd_1413287 483797022500611494541945 := by
  unfold tailWord_1413287
  simp only [CollatzResearch.WordTrace]
  refine ⟨51546811630910044048246115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34364541087273362698830743 51546811630910044048246115)
  ·
    refine ⟨77320217446365066072369173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51546811630910044048246115 77320217446365066072369173)
    ·
      refine ⟨3624385192798362472142305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77320217446365066072369173 3624385192798362472142305)
      ·
        refine ⟨2718288894598771854106729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3624385192798362472142305 2718288894598771854106729)
        ·
          refine ⟨2038716670949078890580047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2718288894598771854106729 2038716670949078890580047)
          ·
            refine ⟨3058075006423618335870071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2038716670949078890580047 3058075006423618335870071)
            ·
              refine ⟨4587112509635427503805107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3058075006423618335870071 4587112509635427503805107)
              ·
                refine ⟨6880668764453141255707661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4587112509635427503805107 6880668764453141255707661)
                ·
                  refine ⟨2580250786669927970890373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6880668764453141255707661 2580250786669927970890373)
                  ·
                    refine ⟨483797022500611494541945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2580250786669927970890373 483797022500611494541945)
                    ·
                      rfl

theorem cell22_1413287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_1413287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413287 prefixEnd_1413287 := by exact prefixLift 1413287
  have htrace : WordTrace (prefixWord ++ tailWord_1413287) baseStart_1413287 baseEnd_1413287 := by
    simpa [prefixWord, tailWord_1413287, baseEnd_1413287] using wordTrace_append hprefix tailTrace_1413287
  have hstable : (prefixWord ++ tailWord_1413287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413287).length < 2 ^ (prefixWord ++ tailWord_1413287).sum := by decide
  have hdescent : baseEnd_1413287 < baseStart_1413287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413330 : List Nat := [3, 2, 2, 2, 1, 2, 3, 7]
def baseStart_1413330 : Nat := 118140960795 + 1413330 * 2 ^ 59
def prefixEnd_1413330 : Nat := 4983230072969 + 3 ^ 40 * 1413330 * 2
def baseEnd_1413330 : Nat := 53756860253263746190757

theorem tailTrace_1413330 : CollatzResearch.WordTrace tailWord_1413330 prefixEnd_1413330 53756860253263746190757 := by
  unfold tailWord_1413330
  simp only [CollatzResearch.WordTrace]
  refine ⟨12887094992438565598015361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34365586646502841594707629 12887094992438565598015361)
  ·
    refine ⟨9665321244328924198511521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12887094992438565598015361 9665321244328924198511521)
    ·
      refine ⟨7248990933246693148883641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9665321244328924198511521 7248990933246693148883641)
      ·
        refine ⟨5436743199935019861662731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7248990933246693148883641 5436743199935019861662731)
        ·
          refine ⟨8155114799902529792494097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5436743199935019861662731 8155114799902529792494097)
          ·
            refine ⟨6116336099926897344370573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8155114799902529792494097 6116336099926897344370573)
            ·
              refine ⟨2293626037472586504138965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6116336099926897344370573 2293626037472586504138965)
              ·
                refine ⟨53756860253263746190757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2293626037472586504138965 53756860253263746190757)
                ·
                  rfl

theorem cell22_1413330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 7].length) (baseStart_1413330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413330 prefixEnd_1413330 := by exact prefixLift 1413330
  have htrace : WordTrace (prefixWord ++ tailWord_1413330) baseStart_1413330 baseEnd_1413330 := by
    simpa [prefixWord, tailWord_1413330, baseEnd_1413330] using wordTrace_append hprefix tailTrace_1413330
  have hstable : (prefixWord ++ tailWord_1413330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413330).length < 2 ^ (prefixWord ++ tailWord_1413330).sum := by decide
  have hdescent : baseEnd_1413330 < baseStart_1413330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413334 : List Nat := [5, 2, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1413334 : Nat := 118140960795 + 1413334 * 2 ^ 59
def prefixEnd_1413334 : Nat := 4983230072969 + 3 ^ 40 * 1413334 * 2
def baseEnd_1413334 : Nat := 483813111561119038616801

theorem tailTrace_1413334 : CollatzResearch.WordTrace tailWord_1413334 prefixEnd_1413334 483813111561119038616801 := by
  unfold tailWord_1413334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3221782866358735692200441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34365683907826514050138037 3221782866358735692200441)
  ·
    refine ⟨2416337149769051769150331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3221782866358735692200441 2416337149769051769150331)
    ·
      refine ⟨3624505724653577653725497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2416337149769051769150331 3624505724653577653725497)
      ·
        refine ⟨2718379293490183240294123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3624505724653577653725497 2718379293490183240294123)
        ·
          refine ⟨4077568940235274860441185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2718379293490183240294123 4077568940235274860441185)
          ·
            refine ⟨3058176705176456145330889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4077568940235274860441185 3058176705176456145330889)
            ·
              refine ⟨2293632528882342108998167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3058176705176456145330889 2293632528882342108998167)
              ·
                refine ⟨3440448793323513163497251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2293632528882342108998167 3440448793323513163497251)
                ·
                  refine ⟨5160673189985269745245877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3440448793323513163497251 5160673189985269745245877)
                  ·
                    refine ⟨483813111561119038616801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5160673189985269745245877 483813111561119038616801)
                    ·
                      rfl

theorem cell22_1413334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1413334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413334 prefixEnd_1413334 := by exact prefixLift 1413334
  have htrace : WordTrace (prefixWord ++ tailWord_1413334) baseStart_1413334 baseEnd_1413334 := by
    simpa [prefixWord, tailWord_1413334, baseEnd_1413334] using wordTrace_append hprefix tailTrace_1413334
  have hstable : (prefixWord ++ tailWord_1413334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413334).length < 2 ^ (prefixWord ++ tailWord_1413334).sum := by decide
  have hdescent : baseEnd_1413334 < baseStart_1413334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413343 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 4, 6]
def baseStart_1413343 : Nat := 118140960795 + 1413343 * 2 ^ 59
def prefixEnd_1413343 : Nat := 4983230072969 + 3 ^ 40 * 1413343 * 2
def baseEnd_1413343 : Nat := 483816192445046015141773

theorem tailTrace_1413343 : CollatzResearch.WordTrace tailWord_1413343 prefixEnd_1413343 483816192445046015141773 := by
  unfold tailWord_1413343
  simp only [CollatzResearch.WordTrace]
  refine ⟨51548854118707165612284683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34365902745804777074856455 51548854118707165612284683)
  ·
    refine ⟨77323281178060748418427025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51548854118707165612284683 77323281178060748418427025)
    ·
      refine ⟨57992460883545561313820269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77323281178060748418427025 57992460883545561313820269)
      ·
        refine ⟨21747172831329585492682601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57992460883545561313820269 21747172831329585492682601)
        ·
          refine ⟨16310379623497189119511951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21747172831329585492682601 16310379623497189119511951)
          ·
            refine ⟨24465569435245783679267927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16310379623497189119511951 24465569435245783679267927)
            ·
              refine ⟨36698354152868675518901891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24465569435245783679267927 36698354152868675518901891)
              ·
                refine ⟨55047531229303013278352837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36698354152868675518901891 55047531229303013278352837)
                ·
                  refine ⟨10321412105494314989691157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55047531229303013278352837 10321412105494314989691157)
                  ·
                    refine ⟨483816192445046015141773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10321412105494314989691157 483816192445046015141773)
                    ·
                      rfl

theorem cell22_1413343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_1413343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413343 prefixEnd_1413343 := by exact prefixLift 1413343
  have htrace : WordTrace (prefixWord ++ tailWord_1413343) baseStart_1413343 baseEnd_1413343 := by
    simpa [prefixWord, tailWord_1413343, baseEnd_1413343] using wordTrace_append hprefix tailTrace_1413343
  have hstable : (prefixWord ++ tailWord_1413343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413343).length < 2 ^ (prefixWord ++ tailWord_1413343).sum := by decide
  have hdescent : baseEnd_1413343 < baseStart_1413343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413390 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_1413390 : Nat := 118140960795 + 1413390 * 2 ^ 59
def prefixEnd_1413390 : Nat := 4983230072969 + 3 ^ 40 * 1413390 * 2
def baseEnd_1413390 : Nat := 483832281505553559216629

theorem tailTrace_1413390 : CollatzResearch.WordTrace tailWord_1413390 prefixEnd_1413390 483832281505553559216629 := by
  unfold tailWord_1413390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6443821043692111579905703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34367045566357928426163749 6443821043692111579905703)
  ·
    refine ⟨9665731565538167369858555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6443821043692111579905703 9665731565538167369858555)
    ·
      refine ⟨14498597348307251054787833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9665731565538167369858555 14498597348307251054787833)
      ·
        refine ⟨10873948011230438291090875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14498597348307251054787833 10873948011230438291090875)
        ·
          refine ⟨16310922016845657436636313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10873948011230438291090875 16310922016845657436636313)
          ·
            refine ⟨12233191512634243077477235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16310922016845657436636313 12233191512634243077477235)
            ·
              refine ⟨18349787268951364616215853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12233191512634243077477235 18349787268951364616215853)
              ·
                refine ⟨6881170225856761731080945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18349787268951364616215853 6881170225856761731080945)
                ·
                  refine ⟨5160877669392571298310709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6881170225856761731080945 5160877669392571298310709)
                  ·
                    refine ⟨483832281505553559216629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5160877669392571298310709 483832281505553559216629)
                    ·
                      rfl

theorem cell22_1413390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_1413390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413390 prefixEnd_1413390 := by exact prefixLift 1413390
  have htrace : WordTrace (prefixWord ++ tailWord_1413390) baseStart_1413390 baseEnd_1413390 := by
    simpa [prefixWord, tailWord_1413390, baseEnd_1413390] using wordTrace_append hprefix tailTrace_1413390
  have hstable : (prefixWord ++ tailWord_1413390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413390).length < 2 ^ (prefixWord ++ tailWord_1413390).sum := by decide
  have hdescent : baseEnd_1413390 < baseStart_1413390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413413 : List Nat := [1, 3, 1, 2, 6, 1, 1, 3, 1, 3]
def baseStart_1413413 : Nat := 118140960795 + 1413413 * 2 ^ 59
def prefixEnd_1413413 : Nat := 4983230072969 + 3 ^ 40 * 1413413 * 2
def baseEnd_1413413 : Nat := 483840154875589165891559

theorem tailTrace_1413413 : CollatzResearch.WordTrace tailWord_1413413 prefixEnd_1413413 483840154875589165891559 := by
  unfold tailWord_1413413
  simp only [CollatzResearch.WordTrace]
  refine ⟨51551407228453567567332893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34367604818969045044888595 51551407228453567567332893)
  ·
    refine ⟨19331777710670087837749835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51551407228453567567332893 19331777710670087837749835)
    ·
      refine ⟨28997666566005131756624753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19331777710670087837749835 28997666566005131756624753)
      ·
        refine ⟨21748249924503848817468565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28997666566005131756624753 21748249924503848817468565)
        ·
          refine ⟨1019449215211117913318839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21748249924503848817468565 1019449215211117913318839)
          ·
            refine ⟨1529173822816676869978259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019449215211117913318839 1529173822816676869978259)
            ·
              refine ⟨2293760734225015304967389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529173822816676869978259 2293760734225015304967389)
              ·
                refine ⟨860160275334380739362771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2293760734225015304967389 860160275334380739362771)
                ·
                  refine ⟨1290240413001571109044157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 860160275334380739362771 1290240413001571109044157)
                  ·
                    refine ⟨483840154875589165891559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1290240413001571109044157 483840154875589165891559)
                    ·
                      rfl

theorem cell22_1413413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 1, 3].length) (baseStart_1413413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413413 prefixEnd_1413413 := by exact prefixLift 1413413
  have htrace : WordTrace (prefixWord ++ tailWord_1413413) baseStart_1413413 baseEnd_1413413 := by
    simpa [prefixWord, tailWord_1413413, baseEnd_1413413] using wordTrace_append hprefix tailTrace_1413413
  have hstable : (prefixWord ++ tailWord_1413413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413413).length < 2 ^ (prefixWord ++ tailWord_1413413).sum := by decide
  have hdescent : baseEnd_1413413 < baseStart_1413413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413497 : List Nat := [1, 2, 1, 3, 2, 1, 1, 5, 3, 3]
def baseStart_1413497 : Nat := 118140960795 + 1413497 * 2 ^ 59
def prefixEnd_1413497 : Nat := 4983230072969 + 3 ^ 40 * 1413497 * 2
def baseEnd_1413497 : Nat := 483868909792240946791301

theorem tailTrace_1413497 : CollatzResearch.WordTrace tailWord_1413497 prefixEnd_1413497 483868909792240946791301 := by
  unfold tailWord_1413497
  simp only [CollatzResearch.WordTrace]
  refine ⟨51554470960149249913390745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34369647306766166608927163 51554470960149249913390745)
  ·
    refine ⟨38665853220111937435043059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51554470960149249913390745 38665853220111937435043059)
    ·
      refine ⟨57998779830167906152564589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38665853220111937435043059 57998779830167906152564589)
      ·
        refine ⟨21749542436312964807211721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57998779830167906152564589 21749542436312964807211721)
        ·
          refine ⟨16312156827234723605408791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21749542436312964807211721 16312156827234723605408791)
          ·
            refine ⟨24468235240852085408113187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16312156827234723605408791 24468235240852085408113187)
            ·
              refine ⟨36702352861278128112169781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24468235240852085408113187 36702352861278128112169781)
              ·
                refine ⟨3440845580744824510515917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36702352861278128112169781 3440845580744824510515917)
                ·
                  refine ⟨1290317092779309191443469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3440845580744824510515917 1290317092779309191443469)
                  ·
                    refine ⟨483868909792240946791301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1290317092779309191443469 483868909792240946791301)
                    ·
                      rfl

theorem cell22_1413497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 3].length) (baseStart_1413497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413497 prefixEnd_1413497 := by exact prefixLift 1413497
  have htrace : WordTrace (prefixWord ++ tailWord_1413497) baseStart_1413497 baseEnd_1413497 := by
    simpa [prefixWord, tailWord_1413497, baseEnd_1413497] using wordTrace_append hprefix tailTrace_1413497
  have hstable : (prefixWord ++ tailWord_1413497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413497).length < 2 ^ (prefixWord ++ tailWord_1413497).sum := by decide
  have hdescent : baseEnd_1413497 < baseStart_1413497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413525 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 3, 7]
def baseStart_1413525 : Nat := 118140960795 + 1413525 * 2 ^ 59
def prefixEnd_1413525 : Nat := 4983230072969 + 3 ^ 40 * 1413525 * 2
def baseEnd_1413525 : Nat := 483878494764458207091215

theorem tailTrace_1413525 : CollatzResearch.WordTrace tailWord_1413525 prefixEnd_1413525 483878494764458207091215 := by
  unfold tailWord_1413525
  simp only [CollatzResearch.WordTrace]
  refine ⟨51555492204047810695410029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34370328136031873796940019 51555492204047810695410029)
  ·
    refine ⟨19333309576517929010778761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51555492204047810695410029 19333309576517929010778761)
    ·
      refine ⟨14499982182388446758084071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19333309576517929010778761 14499982182388446758084071)
      ·
        refine ⟨21749973273582670137126107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14499982182388446758084071 21749973273582670137126107)
        ·
          refine ⟨32624959910374005205689161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21749973273582670137126107 32624959910374005205689161)
          ·
            refine ⟨24468719932780503904266871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32624959910374005205689161 24468719932780503904266871)
            ·
              refine ⟨36703079899170755856400307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24468719932780503904266871 36703079899170755856400307)
              ·
                refine ⟨55054619848756133784600461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36703079899170755856400307 55054619848756133784600461)
                ·
                  refine ⟨20645482443283550169225173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55054619848756133784600461 20645482443283550169225173)
                  ·
                    refine ⟨483878494764458207091215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20645482443283550169225173 483878494764458207091215)
                    ·
                      rfl

theorem cell22_1413525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_1413525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413525 prefixEnd_1413525 := by exact prefixLift 1413525
  have htrace : WordTrace (prefixWord ++ tailWord_1413525) baseStart_1413525 baseEnd_1413525 := by
    simpa [prefixWord, tailWord_1413525, baseEnd_1413525] using wordTrace_append hprefix tailTrace_1413525
  have hstable : (prefixWord ++ tailWord_1413525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413525).length < 2 ^ (prefixWord ++ tailWord_1413525).sum := by decide
  have hdescent : baseEnd_1413525 < baseStart_1413525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413544 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 7]
def baseStart_1413544 : Nat := 118140960795 + 1413544 * 2 ^ 59
def prefixEnd_1413544 : Nat := 4983230072969 + 3 ^ 40 * 1413544 * 2
def baseEnd_1413544 : Nat := 161294999617582830288719

theorem tailTrace_1413544 : CollatzResearch.WordTrace tailWord_1413544 prefixEnd_1413544 161294999617582830288719 := by
  unfold tailWord_1413544
  simp only [CollatzResearch.WordTrace]
  refine ⟨25778092595489488470175843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34370790127319317960234457 25778092595489488470175843)
  ·
    refine ⟨38667138893234232705263765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25778092595489488470175843 38667138893234232705263765)
    ·
      refine ⟨1812522135620354658059239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38667138893234232705263765 1812522135620354658059239)
      ·
        refine ⟨2718783203430531987088859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1812522135620354658059239 2718783203430531987088859)
        ·
          refine ⟨4078174805145797980633289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2718783203430531987088859 4078174805145797980633289)
          ·
            refine ⟨3058631103859348485474967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4078174805145797980633289 3058631103859348485474967)
            ·
              refine ⟨4587946655789022728212451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3058631103859348485474967 4587946655789022728212451)
              ·
                refine ⟨6881919983683534092318677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4587946655789022728212451 6881919983683534092318677)
                ·
                  refine ⟨161294999617582830288719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6881919983683534092318677 161294999617582830288719)
                  ·
                    rfl

theorem cell22_1413544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 7].length) (baseStart_1413544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413544 prefixEnd_1413544 := by exact prefixLift 1413544
  have htrace : WordTrace (prefixWord ++ tailWord_1413544) baseStart_1413544 baseEnd_1413544 := by
    simpa [prefixWord, tailWord_1413544, baseEnd_1413544] using wordTrace_append hprefix tailTrace_1413544
  have hstable : (prefixWord ++ tailWord_1413544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413544).length < 2 ^ (prefixWord ++ tailWord_1413544).sum := by decide
  have hdescent : baseEnd_1413544 < baseStart_1413544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413617 : List Nat := [1, 2, 2, 2, 3, 1, 4, 7]
def baseStart_1413617 : Nat := 118140960795 + 1413617 * 2 ^ 59
def prefixEnd_1413617 : Nat := 4983230072969 + 3 ^ 40 * 1413617 * 2
def baseEnd_1413617 : Nat := 53767776471622292643437

theorem tailTrace_1413617 : CollatzResearch.WordTrace tailWord_1413617 prefixEnd_1413617 53767776471622292643437 := by
  unfold tailWord_1413617
  simp only [CollatzResearch.WordTrace]
  refine ⟨51558847719714510407759105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34372565146476340271839403 51558847719714510407759105)
  ·
    refine ⟨38669135789785882805819329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51558847719714510407759105 38669135789785882805819329)
    ·
      refine ⟨29001851842339412104364497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38669135789785882805819329 29001851842339412104364497)
      ·
        refine ⟨21751388881754559078273373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29001851842339412104364497 21751388881754559078273373)
        ·
          refine ⟨8156770830657959654352515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21751388881754559078273373 8156770830657959654352515)
          ·
            refine ⟨12235156245986939481528773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8156770830657959654352515 12235156245986939481528773)
            ·
              refine ⟨2294091796122551152786645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12235156245986939481528773 2294091796122551152786645)
              ·
                refine ⟨53767776471622292643437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2294091796122551152786645 53767776471622292643437)
                ·
                  rfl

theorem cell22_1413617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 7].length) (baseStart_1413617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413617 prefixEnd_1413617 := by exact prefixLift 1413617
  have htrace : WordTrace (prefixWord ++ tailWord_1413617) baseStart_1413617 baseEnd_1413617 := by
    simpa [prefixWord, tailWord_1413617, baseEnd_1413617] using wordTrace_append hprefix tailTrace_1413617
  have hstable : (prefixWord ++ tailWord_1413617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413617).length < 2 ^ (prefixWord ++ tailWord_1413617).sum := by decide
  have hdescent : baseEnd_1413617 < baseStart_1413617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413636 : List Nat := [2, 3, 2, 3, 1, 2, 2, 1, 2, 4]
def baseStart_1413636 : Nat := 118140960795 + 1413636 * 2 ^ 59
def prefixEnd_1413636 : Nat := 4983230072969 + 3 ^ 40 * 1413636 * 2
def baseEnd_1413636 : Nat := 483916492332890917565875

theorem tailTrace_1413636 : CollatzResearch.WordTrace tailWord_1413636 prefixEnd_1413636 483916492332890917565875 := by
  unfold tailWord_1413636
  simp only [CollatzResearch.WordTrace]
  refine ⟨25779770353322838326350381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34373027137763784435133841 25779770353322838326350381)
  ·
    refine ⟨9667413882496064372381393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25779770353322838326350381 9667413882496064372381393)
    ·
      refine ⟨7250560411872048279286045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9667413882496064372381393 7250560411872048279286045)
      ·
        refine ⟨2718960154452018104732267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7250560411872048279286045 2718960154452018104732267)
        ·
          refine ⟨4078440231678027157098401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2718960154452018104732267 4078440231678027157098401)
          ·
            refine ⟨3058830173758520367823801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4078440231678027157098401 3058830173758520367823801)
            ·
              refine ⟨2294122630318890275867851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3058830173758520367823801 2294122630318890275867851)
              ·
                refine ⟨3441183945478335413801777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2294122630318890275867851 3441183945478335413801777)
                ·
                  refine ⟨2580887959108751560351333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3441183945478335413801777 2580887959108751560351333)
                  ·
                    refine ⟨483916492332890917565875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2580887959108751560351333 483916492332890917565875)
                    ·
                      rfl

theorem cell22_1413636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_1413636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413636 prefixEnd_1413636 := by exact prefixLift 1413636
  have htrace : WordTrace (prefixWord ++ tailWord_1413636) baseStart_1413636 baseEnd_1413636 := by
    simpa [prefixWord, tailWord_1413636, baseEnd_1413636] using wordTrace_append hprefix tailTrace_1413636
  have hstable : (prefixWord ++ tailWord_1413636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413636).length < 2 ^ (prefixWord ++ tailWord_1413636).sum := by decide
  have hdescent : baseEnd_1413636 < baseStart_1413636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413638 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_1413638 : Nat := 118140960795 + 1413638 * 2 ^ 59
def prefixEnd_1413638 : Nat := 4983230072969 + 3 ^ 40 * 1413638 * 2
def baseEnd_1413638 : Nat := 483917176973763579015869

theorem tailTrace_1413638 : CollatzResearch.WordTrace tailWord_1413638 prefixEnd_1413638 483917176973763579015869 := by
  unfold tailWord_1413638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1611237926644950968571049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34373075768425620662849045 1611237926644950968571049)
  ·
    refine ⟨1208428444983713226428287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1611237926644950968571049 1208428444983713226428287)
    ·
      refine ⟨1812642667475569839642431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1208428444983713226428287 1812642667475569839642431)
      ·
        refine ⟨2718964001213354759463647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1812642667475569839642431 2718964001213354759463647)
        ·
          refine ⟨4078446001820032139195471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2718964001213354759463647 4078446001820032139195471)
          ·
            refine ⟨6117669002730048208793207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4078446001820032139195471 6117669002730048208793207)
            ·
              refine ⟨9176503504095072313189811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6117669002730048208793207 9176503504095072313189811)
              ·
                refine ⟨13764755256142608469784717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9176503504095072313189811 13764755256142608469784717)
                ·
                  refine ⟨5161783221053478176169269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13764755256142608469784717 5161783221053478176169269)
                  ·
                    refine ⟨483917176973763579015869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5161783221053478176169269 483917176973763579015869)
                    ·
                      rfl

theorem cell22_1413638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_1413638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413638 prefixEnd_1413638 := by exact prefixLift 1413638
  have htrace : WordTrace (prefixWord ++ tailWord_1413638) baseStart_1413638 baseEnd_1413638 := by
    simpa [prefixWord, tailWord_1413638, baseEnd_1413638] using wordTrace_append hprefix tailTrace_1413638
  have hstable : (prefixWord ++ tailWord_1413638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413638).length < 2 ^ (prefixWord ++ tailWord_1413638).sum := by decide
  have hdescent : baseEnd_1413638 < baseStart_1413638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413668 : List Nat := [2, 3, 1, 5, 2, 1, 1, 7]
def baseStart_1413668 : Nat := 118140960795 + 1413668 * 2 ^ 59
def prefixEnd_1413668 : Nat := 4983230072969 + 3 ^ 40 * 1413668 * 2
def baseEnd_1413668 : Nat := 53769716287428166751753

theorem tailTrace_1413668 : CollatzResearch.WordTrace tailWord_1413668 prefixEnd_1413668 53769716287428166751753 := by
  unfold tailWord_1413668
  simp only [CollatzResearch.WordTrace]
  refine ⟨25780353921264873058932829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34373805228353164078577105 25780353921264873058932829)
  ·
    refine ⟨9667632720474327397099811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25780353921264873058932829 9667632720474327397099811)
    ·
      refine ⟨14501449080711491095649717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9667632720474327397099811 14501449080711491095649717)
      ·
        refine ⟨1359510851316702290217161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14501449080711491095649717 1359510851316702290217161)
        ·
          refine ⟨1019633138487526717662871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1359510851316702290217161 1019633138487526717662871)
          ·
            refine ⟨1529449707731290076494307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019633138487526717662871 1529449707731290076494307)
            ·
              refine ⟨2294174561596935114741461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529449707731290076494307 2294174561596935114741461)
              ·
                refine ⟨53769716287428166751753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2294174561596935114741461 53769716287428166751753)
                ·
                  rfl

theorem cell22_1413668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 7].length) (baseStart_1413668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413668 prefixEnd_1413668 := by exact prefixLift 1413668
  have htrace : WordTrace (prefixWord ++ tailWord_1413668) baseStart_1413668 baseEnd_1413668 := by
    simpa [prefixWord, tailWord_1413668, baseEnd_1413668] using wordTrace_append hprefix tailTrace_1413668
  have hstable : (prefixWord ++ tailWord_1413668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413668).length < 2 ^ (prefixWord ++ tailWord_1413668).sum := by decide
  have hdescent : baseEnd_1413668 < baseStart_1413668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413722 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 2, 9]
def baseStart_1413722 : Nat := 118140960795 + 1413722 * 2 ^ 59
def prefixEnd_1413722 : Nat := 4983230072969 + 3 ^ 40 * 1413722 * 2
def baseEnd_1413722 : Nat := 483945931890415359915611

theorem tailTrace_1413722 : CollatzResearch.WordTrace tailWord_1413722 prefixEnd_1413722 483945931890415359915611 := by
  unfold tailWord_1413722
  simp only [CollatzResearch.WordTrace]
  refine ⟨12890669346083528335082855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34375118256222742226887613 12890669346083528335082855)
  ·
    refine ⟨19336004019125292502624283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12890669346083528335082855 19336004019125292502624283)
    ·
      refine ⟨29004006028687938753936425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19336004019125292502624283 29004006028687938753936425)
      ·
        refine ⟨21753004521515954065452319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29004006028687938753936425 21753004521515954065452319)
        ·
          refine ⟨32629506782273931098178479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21753004521515954065452319 32629506782273931098178479)
          ·
            refine ⟨48944260173410896647267719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32629506782273931098178479 48944260173410896647267719)
            ·
              refine ⟨73416390260116344970901579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48944260173410896647267719 73416390260116344970901579)
              ·
                refine ⟨110124585390174517456352369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73416390260116344970901579 110124585390174517456352369)
                ·
                  refine ⟨82593439042630888092264277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110124585390174517456352369 82593439042630888092264277)
                  ·
                    refine ⟨483945931890415359915611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 82593439042630888092264277 483945931890415359915611)
                    ·
                      rfl

theorem cell22_1413722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_1413722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413722 prefixEnd_1413722 := by exact prefixLift 1413722
  have htrace : WordTrace (prefixWord ++ tailWord_1413722) baseStart_1413722 baseEnd_1413722 := by
    simpa [prefixWord, tailWord_1413722, baseEnd_1413722] using wordTrace_append hprefix tailTrace_1413722
  have hstable : (prefixWord ++ tailWord_1413722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413722).length < 2 ^ (prefixWord ++ tailWord_1413722).sum := by decide
  have hdescent : baseEnd_1413722 < baseStart_1413722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413730 : List Nat := [3, 3, 2, 3, 1, 1, 3, 1, 5]
def baseStart_1413730 : Nat := 118140960795 + 1413730 * 2 ^ 59
def prefixEnd_1413730 : Nat := 4983230072969 + 3 ^ 40 * 1413730 * 2
def baseEnd_1413730 : Nat := 161316223484635335238529

theorem tailTrace_1413730 : CollatzResearch.WordTrace tailWord_1413730 prefixEnd_1413730 161316223484635335238529 := by
  unfold tailWord_1413730
  simp only [CollatzResearch.WordTrace]
  refine ⟨12890742292076282676655661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34375312778870087137748429 12890742292076282676655661)
  ·
    refine ⟨4834028359528606003745873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12890742292076282676655661 4834028359528606003745873)
    ·
      refine ⟨3625521269646454502809405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4834028359528606003745873 3625521269646454502809405)
      ·
        refine ⟨1359570476117420438553527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3625521269646454502809405 1359570476117420438553527)
        ·
          refine ⟨2039355714176130657830291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1359570476117420438553527 2039355714176130657830291)
          ·
            refine ⟨3059033571264195986745437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2039355714176130657830291 3059033571264195986745437)
            ·
              refine ⟨1147137589224073495029539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3059033571264195986745437 1147137589224073495029539)
              ·
                refine ⟨1720706383836110242544309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1147137589224073495029539 1720706383836110242544309)
                ·
                  refine ⟨161316223484635335238529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1720706383836110242544309 161316223484635335238529)
                  ·
                    rfl

theorem cell22_1413730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_1413730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413730 prefixEnd_1413730 := by exact prefixLift 1413730
  have htrace : WordTrace (prefixWord ++ tailWord_1413730) baseStart_1413730 baseEnd_1413730 := by
    simpa [prefixWord, tailWord_1413730, baseEnd_1413730] using wordTrace_append hprefix tailTrace_1413730
  have hstable : (prefixWord ++ tailWord_1413730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413730).length < 2 ^ (prefixWord ++ tailWord_1413730).sum := by decide
  have hdescent : baseEnd_1413730 < baseStart_1413730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413752 : List Nat := [2, 1, 2, 1, 1, 1, 2, 12]
def baseStart_1413752 : Nat := 118140960795 + 1413752 * 2 ^ 59
def prefixEnd_1413752 : Nat := 4983230072969 + 3 ^ 40 * 1413752 * 2
def baseEnd_1413752 : Nat := 53772911278167253518391

theorem tailTrace_1413752 : CollatzResearch.WordTrace tailWord_1413752 prefixEnd_1413752 53772911278167253518391 := by
  unfold tailWord_1413752
  simp only [CollatzResearch.WordTrace]
  refine ⟨25781885787112714231961755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34375847716150285642615673 25781885787112714231961755)
  ·
    refine ⟨38672828680669071347942633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25781885787112714231961755 38672828680669071347942633)
    ·
      refine ⟨29004621510501803510956975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38672828680669071347942633 29004621510501803510956975)
      ·
        refine ⟨43506932265752705266435463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29004621510501803510956975 43506932265752705266435463)
        ·
          refine ⟨65260398398629057899653195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43506932265752705266435463 65260398398629057899653195)
          ·
            refine ⟨97890597597943586849479793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65260398398629057899653195 97890597597943586849479793)
            ·
              refine ⟨73417948198457690137109845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97890597597943586849479793 73417948198457690137109845)
              ·
                refine ⟨53772911278167253518391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 73417948198457690137109845 53772911278167253518391)
                ·
                  rfl

theorem cell22_1413752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 12].length) (baseStart_1413752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413752 prefixEnd_1413752 := by exact prefixLift 1413752
  have htrace : WordTrace (prefixWord ++ tailWord_1413752) baseStart_1413752 baseEnd_1413752 := by
    simpa [prefixWord, tailWord_1413752, baseEnd_1413752] using wordTrace_append hprefix tailTrace_1413752
  have hstable : (prefixWord ++ tailWord_1413752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413752).length < 2 ^ (prefixWord ++ tailWord_1413752).sum := by decide
  have hdescent : baseEnd_1413752 < baseStart_1413752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413818 : List Nat := [3, 1, 1, 1, 2, 3, 2, 5, 1, 3]
def baseStart_1413818 : Nat := 118140960795 + 1413818 * 2 ^ 59
def prefixEnd_1413818 : Nat := 4983230072969 + 3 ^ 40 * 1413818 * 2
def baseEnd_1413818 : Nat := 483978794652303109515317

theorem tailTrace_1413818 : CollatzResearch.WordTrace tailWord_1413818 prefixEnd_1413818 483978794652303109515317 := by
  unfold tailWord_1413818
  simp only [CollatzResearch.WordTrace]
  refine ⟨12891544697996580433956527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34377452527990881157217405 12891544697996580433956527)
  ·
    refine ⟨19337317046994870650934791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12891544697996580433956527 19337317046994870650934791)
    ·
      refine ⟨29005975570492305976402187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19337317046994870650934791 29005975570492305976402187)
      ·
        refine ⟨43508963355738458964603281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29005975570492305976402187 43508963355738458964603281)
        ·
          refine ⟨32631722516803844223452461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43508963355738458964603281 32631722516803844223452461)
          ·
            refine ⟨12236895943801441583794673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32631722516803844223452461 12236895943801441583794673)
            ·
              refine ⟨9177671957851081187846005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12236895943801441583794673 9177671957851081187846005)
              ·
                refine ⟨860406746048538861360563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9177671957851081187846005 860406746048538861360563)
                ·
                  refine ⟨1290610119072808292040845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 860406746048538861360563 1290610119072808292040845)
                  ·
                    refine ⟨483978794652303109515317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1290610119072808292040845 483978794652303109515317)
                    ·
                      rfl

theorem cell22_1413818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 1, 3].length) (baseStart_1413818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413818 prefixEnd_1413818 := by exact prefixLift 1413818
  have htrace : WordTrace (prefixWord ++ tailWord_1413818) baseStart_1413818 baseEnd_1413818 := by
    simpa [prefixWord, tailWord_1413818, baseEnd_1413818] using wordTrace_append hprefix tailTrace_1413818
  have hstable : (prefixWord ++ tailWord_1413818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413818).length < 2 ^ (prefixWord ++ tailWord_1413818).sum := by decide
  have hdescent : baseEnd_1413818 < baseStart_1413818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413861 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 3, 4]
def baseStart_1413861 : Nat := 118140960795 + 1413861 * 2 ^ 59
def prefixEnd_1413861 : Nat := 4983230072969 + 3 ^ 40 * 1413861 * 2
def baseEnd_1413861 : Nat := 483993514431065330690185

theorem tailTrace_1413861 : CollatzResearch.WordTrace tailWord_1413861 prefixEnd_1413861 483993514431065330690185 := by
  unfold tailWord_1413861
  simp only [CollatzResearch.WordTrace]
  refine ⟨51567747130830540079641437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34378498087220360053094291 51567747130830540079641437)
  ·
    refine ⟨19337905174061452529865539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51567747130830540079641437 19337905174061452529865539)
    ·
      refine ⟨29006857761092178794798309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19337905174061452529865539 29006857761092178794798309)
      ·
        refine ⟨5438785830204783524024683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29006857761092178794798309 5438785830204783524024683)
        ·
          refine ⟨8158178745307175286037025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5438785830204783524024683 8158178745307175286037025)
          ·
            refine ⟨6118634058980381464527769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8158178745307175286037025 6118634058980381464527769)
            ·
              refine ⟨4588975544235286098395827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6118634058980381464527769 4588975544235286098395827)
              ·
                refine ⟨6883463316352929147593741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4588975544235286098395827 6883463316352929147593741)
                ·
                  refine ⟨2581298743632348430347653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6883463316352929147593741 2581298743632348430347653)
                  ·
                    refine ⟨483993514431065330690185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2581298743632348430347653 483993514431065330690185)
                    ·
                      rfl

theorem cell22_1413861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_1413861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413861 prefixEnd_1413861 := by exact prefixLift 1413861
  have htrace : WordTrace (prefixWord ++ tailWord_1413861) baseStart_1413861 baseEnd_1413861 := by
    simpa [prefixWord, tailWord_1413861, baseEnd_1413861] using wordTrace_append hprefix tailTrace_1413861
  have hstable : (prefixWord ++ tailWord_1413861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413861).length < 2 ^ (prefixWord ++ tailWord_1413861).sum := by decide
  have hdescent : baseEnd_1413861 < baseStart_1413861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413878 : List Nat := [5, 1, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_1413878 : Nat := 118140960795 + 1413878 * 2 ^ 59
def prefixEnd_1413878 : Nat := 4983230072969 + 3 ^ 40 * 1413878 * 2
def baseEnd_1413878 : Nat := 483999333878482953015133

theorem tailTrace_1413878 : CollatzResearch.WordTrace tailWord_1413878 prefixEnd_1413878 483999333878482953015133 := by
  unfold tailWord_1413878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3223022948235559498938143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34378911447845967988673525 3223022948235559498938143)
  ·
    refine ⟨4834534422353339248407215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3223022948235559498938143 4834534422353339248407215)
    ·
      refine ⟨7251801633530008872610823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4834534422353339248407215 7251801633530008872610823)
      ·
        refine ⟨10877702450295013308916235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7251801633530008872610823 10877702450295013308916235)
        ·
          refine ⟨16316553675442519963374353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10877702450295013308916235 16316553675442519963374353)
          ·
            refine ⟨12237415256581889972530765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16316553675442519963374353 12237415256581889972530765)
            ·
              refine ⟨4589030721218208739699037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12237415256581889972530765 4589030721218208739699037)
              ·
                refine ⟨1720886520456828277387139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4589030721218208739699037 1720886520456828277387139)
                ·
                  refine ⟨2581329780685242416080709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1720886520456828277387139 2581329780685242416080709)
                  ·
                    refine ⟨483999333878482953015133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2581329780685242416080709 483999333878482953015133)
                    ·
                      rfl

theorem cell22_1413878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_1413878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413878 prefixEnd_1413878 := by exact prefixLift 1413878
  have htrace : WordTrace (prefixWord ++ tailWord_1413878) baseStart_1413878 baseEnd_1413878 := by
    simpa [prefixWord, tailWord_1413878, baseEnd_1413878] using wordTrace_append hprefix tailTrace_1413878
  have hstable : (prefixWord ++ tailWord_1413878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413878).length < 2 ^ (prefixWord ++ tailWord_1413878).sum := by decide
  have hdescent : baseEnd_1413878 < baseStart_1413878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413936 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 5, 3]
def baseStart_1413936 : Nat := 118140960795 + 1413936 * 2 ^ 59
def prefixEnd_1413936 : Nat := 4983230072969 + 3 ^ 40 * 1413936 * 2
def baseEnd_1413936 : Nat := 484019188463790135064955

theorem tailTrace_1413936 : CollatzResearch.WordTrace tailWord_1413936 prefixEnd_1413936 484019188463790135064955 := by
  unfold tailWord_1413936
  simp only [CollatzResearch.WordTrace]
  refine ⟨25785241302779413944310831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34380321737039218592414441 25785241302779413944310831)
  ·
    refine ⟨38677861954169120916466247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25785241302779413944310831 38677861954169120916466247)
    ·
      refine ⟨58016792931253681374699371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38677861954169120916466247 58016792931253681374699371)
      ·
        refine ⟨87025189396880522062049057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58016792931253681374699371 87025189396880522062049057)
        ·
          refine ⟨65268892047660391546536793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87025189396880522062049057 65268892047660391546536793)
          ·
            refine ⟨48951669035745293659902595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65268892047660391546536793 48951669035745293659902595)
            ·
              refine ⟨73427503553617940489853893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48951669035745293659902595 73427503553617940489853893)
              ·
                refine ⟨13767656916303363841847605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73427503553617940489853893 13767656916303363841847605)
                ·
                  refine ⟨1290717835903440360173213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13767656916303363841847605 1290717835903440360173213)
                  ·
                    refine ⟨484019188463790135064955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1290717835903440360173213 484019188463790135064955)
                    ·
                      rfl

theorem cell22_1413936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 5, 3].length) (baseStart_1413936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413936 prefixEnd_1413936 := by exact prefixLift 1413936
  have htrace : WordTrace (prefixWord ++ tailWord_1413936) baseStart_1413936 baseEnd_1413936 := by
    simpa [prefixWord, tailWord_1413936, baseEnd_1413936] using wordTrace_append hprefix tailTrace_1413936
  have hstable : (prefixWord ++ tailWord_1413936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413936).length < 2 ^ (prefixWord ++ tailWord_1413936).sum := by decide
  have hdescent : baseEnd_1413936 < baseStart_1413936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1413940 : List Nat := [2, 5, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_1413940 : Nat := 118140960795 + 1413940 * 2 ^ 59
def prefixEnd_1413940 : Nat := 4983230072969 + 3 ^ 40 * 1413940 * 2
def baseEnd_1413940 : Nat := 484020557745535457964943

theorem tailTrace_1413940 : CollatzResearch.WordTrace tailWord_1413940 prefixEnd_1413940 484020557745535457964943 := by
  unfold tailWord_1413940
  simp only [CollatzResearch.WordTrace]
  refine ⟨25785314248772168285883637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34380418998362891047844849 25785314248772168285883637)
  ·
    refine ⟨2417373210822390776801591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25785314248772168285883637 2417373210822390776801591)
    ·
      refine ⟨3626059816233586165202387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2417373210822390776801591 3626059816233586165202387)
      ·
        refine ⟨5439089724350379247803581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3626059816233586165202387 5439089724350379247803581)
        ·
          refine ⟨2039658646631392217926343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5439089724350379247803581 2039658646631392217926343)
          ·
            refine ⟨3059487969947088326889515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2039658646631392217926343 3059487969947088326889515)
            ·
              refine ⟨4589231954920632490334273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3059487969947088326889515 4589231954920632490334273)
              ·
                refine ⟨3441923966190474367750705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4589231954920632490334273 3441923966190474367750705)
                ·
                  refine ⟨2581442974642855775813029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3441923966190474367750705 2581442974642855775813029)
                  ·
                    refine ⟨484020557745535457964943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2581442974642855775813029 484020557745535457964943)
                    ·
                      rfl

theorem cell22_1413940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_1413940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1413940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1413940 prefixEnd_1413940 := by exact prefixLift 1413940
  have htrace : WordTrace (prefixWord ++ tailWord_1413940) baseStart_1413940 baseEnd_1413940 := by
    simpa [prefixWord, tailWord_1413940, baseEnd_1413940] using wordTrace_append hprefix tailTrace_1413940
  have hstable : (prefixWord ++ tailWord_1413940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1413940).length < 2 ^ (prefixWord ++ tailWord_1413940).sum := by decide
  have hdescent : baseEnd_1413940 < baseStart_1413940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1413940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414045 : List Nat := [1, 4, 2, 1, 2, 1, 4, 3, 4]
def baseStart_1414045 : Nat := 118140960795 + 1414045 * 2 ^ 59
def prefixEnd_1414045 : Nat := 4983230072969 + 3 ^ 40 * 1414045 * 2
def baseEnd_1414045 : Nat := 161352167130450061363207

theorem tailTrace_1414045 : CollatzResearch.WordTrace tailWord_1414045 prefixEnd_1414045 161352167130450061363207 := by
  unfold tailWord_1414045
  simp only [CollatzResearch.WordTrace]
  refine ⟨51574458162163939504339589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34382972108109293002893059 51574458162163939504339589)
  ·
    refine ⟨9670210905405738657063673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51574458162163939504339589 9670210905405738657063673)
    ·
      refine ⟨7252658179054303992797755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9670210905405738657063673 7252658179054303992797755)
      ·
        refine ⟨10878987268581455989196633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7252658179054303992797755 10878987268581455989196633)
        ·
          refine ⟨8159240451436091991897475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10878987268581455989196633 8159240451436091991897475)
          ·
            refine ⟨12238860677154137987846213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8159240451436091991897475 12238860677154137987846213)
            ·
              refine ⟨2294786376966400872721165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12238860677154137987846213 2294786376966400872721165)
              ·
                refine ⟨860544891362400327270437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2294786376966400872721165 860544891362400327270437)
                ·
                  refine ⟨161352167130450061363207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 860544891362400327270437 161352167130450061363207)
                  ·
                    rfl

theorem cell22_1414045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_1414045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414045 prefixEnd_1414045 := by exact prefixLift 1414045
  have htrace : WordTrace (prefixWord ++ tailWord_1414045) baseStart_1414045 baseEnd_1414045 := by
    simpa [prefixWord, tailWord_1414045, baseEnd_1414045] using wordTrace_append hprefix tailTrace_1414045
  have hstable : (prefixWord ++ tailWord_1414045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414045).length < 2 ^ (prefixWord ++ tailWord_1414045).sum := by decide
  have hdescent : baseEnd_1414045 < baseStart_1414045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414047 : List Nat := [1, 1, 2, 5, 2, 3, 2, 1, 1, 4]
def baseStart_1414047 : Nat := 118140960795 + 1414047 * 2 ^ 59
def prefixEnd_1414047 : Nat := 4983230072969 + 3 ^ 40 * 1414047 * 2
def baseEnd_1414047 : Nat := 484057186032222845539615

theorem tailTrace_1414047 : CollatzResearch.WordTrace tailWord_1414047 prefixEnd_1414047 484057186032222845539615 := by
  unfold tailWord_1414047
  simp only [CollatzResearch.WordTrace]
  refine ⟨51574531108156693845912395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34383020738771129230608263 51574531108156693845912395)
  ·
    refine ⟨77361796662235040768868593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51574531108156693845912395 77361796662235040768868593)
    ·
      refine ⟨58021347496676280576651445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77361796662235040768868593 58021347496676280576651445)
      ·
        refine ⟨5439501327813401304061073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58021347496676280576651445 5439501327813401304061073)
        ·
          refine ⟨4079625995860050978045805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5439501327813401304061073 4079625995860050978045805)
          ·
            refine ⟨1529859748447519116767177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4079625995860050978045805 1529859748447519116767177)
            ·
              refine ⟨1147394811335639337575383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1529859748447519116767177 1147394811335639337575383)
              ·
                refine ⟨1721092217003459006363075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1147394811335639337575383 1721092217003459006363075)
                ·
                  refine ⟨2581638325505188509544613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1721092217003459006363075 2581638325505188509544613)
                  ·
                    refine ⟨484057186032222845539615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2581638325505188509544613 484057186032222845539615)
                    ·
                      rfl

theorem cell22_1414047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 1, 4].length) (baseStart_1414047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414047 prefixEnd_1414047 := by exact prefixLift 1414047
  have htrace : WordTrace (prefixWord ++ tailWord_1414047) baseStart_1414047 baseEnd_1414047 := by
    simpa [prefixWord, tailWord_1414047, baseEnd_1414047] using wordTrace_append hprefix tailTrace_1414047
  have hstable : (prefixWord ++ tailWord_1414047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414047).length < 2 ^ (prefixWord ++ tailWord_1414047).sum := by decide
  have hdescent : baseEnd_1414047 < baseStart_1414047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414077 : List Nat := [1, 4, 1, 2, 5, 1, 1, 1, 1, 5]
def baseStart_1414077 : Nat := 118140960795 + 1414077 * 2 ^ 59
def prefixEnd_1414077 : Nat := 4983230072969 + 3 ^ 40 * 1414077 * 2
def baseEnd_1414077 : Nat := 484067455645312767289523

theorem tailTrace_1414077 : CollatzResearch.WordTrace tailWord_1414077 prefixEnd_1414077 484067455645312767289523 := by
  unfold tailWord_1414077
  simp only [CollatzResearch.WordTrace]
  refine ⟨51575625298048008969504485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34383750198698672646336323 51575625298048008969504485)
  ·
    refine ⟨9670429743384001681782091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51575625298048008969504485 9670429743384001681782091)
    ·
      refine ⟨14505644615076002522673137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9670429743384001681782091 14505644615076002522673137)
      ·
        refine ⟨10879233461307001892004853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14505644615076002522673137 10879233461307001892004853)
        ·
          refine ⟨1019928136997531427375455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10879233461307001892004853 1019928136997531427375455)
          ·
            refine ⟨1529892205496297141063183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019928136997531427375455 1529892205496297141063183)
            ·
              refine ⟨2294838308244445711594775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529892205496297141063183 2294838308244445711594775)
              ·
                refine ⟨3442257462366668567392163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2294838308244445711594775 3442257462366668567392163)
                ·
                  refine ⟨5163386193550002851088245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3442257462366668567392163 5163386193550002851088245)
                  ·
                    refine ⟨484067455645312767289523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5163386193550002851088245 484067455645312767289523)
                    ·
                      rfl

theorem cell22_1414077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_1414077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414077 prefixEnd_1414077 := by exact prefixLift 1414077
  have htrace : WordTrace (prefixWord ++ tailWord_1414077) baseStart_1414077 baseEnd_1414077 := by
    simpa [prefixWord, tailWord_1414077, baseEnd_1414077] using wordTrace_append hprefix tailTrace_1414077
  have hstable : (prefixWord ++ tailWord_1414077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414077).length < 2 ^ (prefixWord ++ tailWord_1414077).sum := by decide
  have hdescent : baseEnd_1414077 < baseStart_1414077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414122 : List Nat := [3, 1, 3, 1, 2, 4, 1, 1, 3, 3]
def baseStart_1414122 : Nat := 118140960795 + 1414122 * 2 ^ 59
def prefixEnd_1414122 : Nat := 4983230072969 + 3 ^ 40 * 1414122 * 2
def baseEnd_1414122 : Nat := 484082860064947649914385

theorem tailTrace_1414122 : CollatzResearch.WordTrace tailWord_1414122 prefixEnd_1414122 484082860064947649914385 := by
  unfold tailWord_1414122
  simp only [CollatzResearch.WordTrace]
  refine ⟨12894316645721245413723155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34384844388589987769928413 12894316645721245413723155)
  ·
    refine ⟨19341474968581868120584733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12894316645721245413723155 19341474968581868120584733)
    ·
      refine ⟨7253053113218200545219275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19341474968581868120584733 7253053113218200545219275)
      ·
        refine ⟨10879579669827300817828913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7253053113218200545219275 10879579669827300817828913)
        ·
          refine ⟨8159684752370475613371685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10879579669827300817828913 8159684752370475613371685)
          ·
            refine ⟨1529940891069464177507191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8159684752370475613371685 1529940891069464177507191)
            ·
              refine ⟨2294911336604196266260787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529940891069464177507191 2294911336604196266260787)
              ·
                refine ⟨3442367004906294399391181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2294911336604196266260787 3442367004906294399391181)
                ·
                  refine ⟨1290887626839860399771693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3442367004906294399391181 1290887626839860399771693)
                  ·
                    refine ⟨484082860064947649914385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1290887626839860399771693 484082860064947649914385)
                    ·
                      rfl

theorem cell22_1414122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_1414122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414122 prefixEnd_1414122 := by exact prefixLift 1414122
  have htrace : WordTrace (prefixWord ++ tailWord_1414122) baseStart_1414122 baseEnd_1414122 := by
    simpa [prefixWord, tailWord_1414122, baseEnd_1414122] using wordTrace_append hprefix tailTrace_1414122
  have hstable : (prefixWord ++ tailWord_1414122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414122).length < 2 ^ (prefixWord ++ tailWord_1414122).sum := by decide
  have hdescent : baseEnd_1414122 < baseStart_1414122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414131 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 1, 10]
def baseStart_1414131 : Nat := 118140960795 + 1414131 * 2 ^ 59
def prefixEnd_1414131 : Nat := 4983230072969 + 3 ^ 40 * 1414131 * 2
def baseEnd_1414131 : Nat := 484085940948874626439357

theorem tailTrace_1414131 : CollatzResearch.WordTrace tailWord_1414131 prefixEnd_1414131 484085940948874626439357 := by
  unfold tailWord_1414131
  simp only [CollatzResearch.WordTrace]
  refine ⟨51577594839852376191970247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34385063226568250794646831 51577594839852376191970247)
  ·
    refine ⟨77366392259778564287955371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51577594839852376191970247 77366392259778564287955371)
    ·
      refine ⟨116049588389667846431933057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77366392259778564287955371 116049588389667846431933057)
      ·
        refine ⟨87037191292250884823949793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116049588389667846431933057 87037191292250884823949793)
        ·
          refine ⟨65277893469188163617962345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87037191292250884823949793 65277893469188163617962345)
          ·
            refine ⟨48958420101891122713471759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65277893469188163617962345 48958420101891122713471759)
            ·
              refine ⟨73437630152836684070207639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48958420101891122713471759 73437630152836684070207639)
              ·
                refine ⟨110156445229255026105311459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73437630152836684070207639 110156445229255026105311459)
                ·
                  refine ⟨165234667843882539157967189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110156445229255026105311459 165234667843882539157967189)
                  ·
                    refine ⟨484085940948874626439357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 165234667843882539157967189 484085940948874626439357)
                    ·
                      rfl

theorem cell22_1414131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 10].length) (baseStart_1414131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414131 prefixEnd_1414131 := by exact prefixLift 1414131
  have htrace : WordTrace (prefixWord ++ tailWord_1414131) baseStart_1414131 baseEnd_1414131 := by
    simpa [prefixWord, tailWord_1414131, baseEnd_1414131] using wordTrace_append hprefix tailTrace_1414131
  have hstable : (prefixWord ++ tailWord_1414131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414131).length < 2 ^ (prefixWord ++ tailWord_1414131).sum := by decide
  have hdescent : baseEnd_1414131 < baseStart_1414131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414173 : List Nat := [1, 4, 2, 2, 4, 1, 2, 2, 1, 3]
def baseStart_1414173 : Nat := 118140960795 + 1414173 * 2 ^ 59
def prefixEnd_1414173 : Nat := 4983230072969 + 3 ^ 40 * 1414173 * 2
def baseEnd_1414173 : Nat := 484100318407200516889229

theorem tailTrace_1414173 : CollatzResearch.WordTrace tailWord_1414173 prefixEnd_1414173 484100318407200516889229 := by
  unfold tailWord_1414173
  simp only [CollatzResearch.WordTrace]
  refine ⟨51579126705700217364999173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34386084470466811576666115 51579126705700217364999173)
  ·
    refine ⟨9671086257318790755937345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51579126705700217364999173 9671086257318790755937345)
    ·
      refine ⟨7253314692989093066953009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9671086257318790755937345 7253314692989093066953009)
      ·
        refine ⟨5439986019741819800214757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7253314692989093066953009 5439986019741819800214757)
        ·
          refine ⟨1019997378701591212540267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5439986019741819800214757 1019997378701591212540267)
          ·
            refine ⟨1529996068052386818810401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019997378701591212540267 1529996068052386818810401)
            ·
              refine ⟨1147497051039290114107801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1529996068052386818810401 1147497051039290114107801)
              ·
                refine ⟨860622788279467585580851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1147497051039290114107801 860622788279467585580851)
                ·
                  refine ⟨1290934182419201378371277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 860622788279467585580851 1290934182419201378371277)
                  ·
                    refine ⟨484100318407200516889229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1290934182419201378371277 484100318407200516889229)
                    ·
                      rfl

theorem cell22_1414173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_1414173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414173 prefixEnd_1414173 := by exact prefixLift 1414173
  have htrace : WordTrace (prefixWord ++ tailWord_1414173) baseStart_1414173 baseEnd_1414173 := by
    simpa [prefixWord, tailWord_1414173, baseEnd_1414173] using wordTrace_append hprefix tailTrace_1414173
  have hstable : (prefixWord ++ tailWord_1414173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414173).length < 2 ^ (prefixWord ++ tailWord_1414173).sum := by decide
  have hdescent : baseEnd_1414173 < baseStart_1414173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414193 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 1, 6]
def baseStart_1414193 : Nat := 118140960795 + 1414193 * 2 ^ 59
def prefixEnd_1414193 : Nat := 4983230072969 + 3 ^ 40 * 1414193 * 2
def baseEnd_1414193 : Nat := 484107164815927131389167

theorem tailTrace_1414193 : CollatzResearch.WordTrace tailWord_1414193 prefixEnd_1414193 484107164815927131389167 := by
  unfold tailWord_1414193
  simp only [CollatzResearch.WordTrace]
  refine ⟨51579856165627760780727233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34386570777085173853818155 51579856165627760780727233)
  ·
    refine ⟨38684892124220820585545425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51579856165627760780727233 38684892124220820585545425)
    ·
      refine ⟨29013669093165615439159069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38684892124220820585545425 29013669093165615439159069)
      ·
        refine ⟨10880125909937105789684651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29013669093165615439159069 10880125909937105789684651)
        ·
          refine ⟨16320188864905658684526977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10880125909937105789684651 16320188864905658684526977)
          ·
            refine ⟨12240141648679244013395233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16320188864905658684526977 12240141648679244013395233)
            ·
              refine ⟨9180106236509433010046425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12240141648679244013395233 9180106236509433010046425)
              ·
                refine ⟨6885079677382074757534819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9180106236509433010046425 6885079677382074757534819)
                ·
                  refine ⟨10327619516073112136302229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6885079677382074757534819 10327619516073112136302229)
                  ·
                    refine ⟨484107164815927131389167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10327619516073112136302229 484107164815927131389167)
                    ·
                      rfl

theorem cell22_1414193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_1414193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414193 prefixEnd_1414193 := by exact prefixLift 1414193
  have htrace : WordTrace (prefixWord ++ tailWord_1414193) baseStart_1414193 baseEnd_1414193 := by
    simpa [prefixWord, tailWord_1414193, baseEnd_1414193] using wordTrace_append hprefix tailTrace_1414193
  have hstable : (prefixWord ++ tailWord_1414193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414193).length < 2 ^ (prefixWord ++ tailWord_1414193).sum := by decide
  have hdescent : baseEnd_1414193 < baseStart_1414193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414214 : List Nat := [6, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_1414214 : Nat := 118140960795 + 1414214 * 2 ^ 59
def prefixEnd_1414214 : Nat := 4983230072969 + 3 ^ 40 * 1414214 * 2
def baseEnd_1414214 : Nat := 161371451181696692204701

theorem tailTrace_1414214 : CollatzResearch.WordTrace tailWord_1414214 prefixEnd_1414214 161371451181696692204701 := by
  unfold tailWord_1414214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1611894440579740042726303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34387081399034454244827797 1611894440579740042726303)
  ·
    refine ⟨2417841660869610064089455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1611894440579740042726303 2417841660869610064089455)
    ·
      refine ⟨3626762491304415096134183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2417841660869610064089455 3626762491304415096134183)
      ·
        refine ⟨5440143736956622644201275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3626762491304415096134183 5440143736956622644201275)
        ·
          refine ⟨8160215605434933966301913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5440143736956622644201275 8160215605434933966301913)
          ·
            refine ⟨6120161704076200474726435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8160215605434933966301913 6120161704076200474726435)
            ·
              refine ⟨9180242556114300712089653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6120161704076200474726435 9180242556114300712089653)
              ·
                refine ⟨860647739635715691758405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9180242556114300712089653 860647739635715691758405)
                ·
                  refine ⟨161371451181696692204701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 860647739635715691758405 161371451181696692204701)
                  ·
                    rfl

theorem cell22_1414214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_1414214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414214 prefixEnd_1414214 := by exact prefixLift 1414214
  have htrace : WordTrace (prefixWord ++ tailWord_1414214) baseStart_1414214 baseEnd_1414214 := by
    simpa [prefixWord, tailWord_1414214, baseEnd_1414214] using wordTrace_append hprefix tailTrace_1414214
  have hstable : (prefixWord ++ tailWord_1414214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414214).length < 2 ^ (prefixWord ++ tailWord_1414214).sum := by decide
  have hdescent : baseEnd_1414214 < baseStart_1414214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414405 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 7]
def baseStart_1414405 : Nat := 118140960795 + 1414405 * 2 ^ 59
def prefixEnd_1414405 : Nat := 4983230072969 + 3 ^ 40 * 1414405 * 2
def baseEnd_1414405 : Nat := 161393245582809748362839

theorem tailTrace_1414405 : CollatzResearch.WordTrace tailWord_1414405 prefixEnd_1414405 161393245582809748362839 := by
  unfold tailWord_1414405
  simp only [CollatzResearch.WordTrace]
  refine ⟨51587588440859720987444669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34391725627239813991629779 51587588440859720987444669)
  ·
    refine ⟨19345345665322395370291751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51587588440859720987444669 19345345665322395370291751)
    ·
      refine ⟨29018018497983593055437627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19345345665322395370291751 29018018497983593055437627)
      ·
        refine ⟨43527027746975389583156441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29018018497983593055437627 43527027746975389583156441)
        ·
          refine ⟨32645270810231542187367331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43527027746975389583156441 32645270810231542187367331)
          ·
            refine ⟨48967906215347313281050997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32645270810231542187367331 48967906215347313281050997)
            ·
              refine ⟨4590741207688810620098531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48967906215347313281050997 4590741207688810620098531)
              ·
                refine ⟨6886111811533215930147797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4590741207688810620098531 6886111811533215930147797)
                ·
                  refine ⟨161393245582809748362839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6886111811533215930147797 161393245582809748362839)
                  ·
                    rfl

theorem cell22_1414405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_1414405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414405 prefixEnd_1414405 := by exact prefixLift 1414405
  have htrace : WordTrace (prefixWord ++ tailWord_1414405) baseStart_1414405 baseEnd_1414405 := by
    simpa [prefixWord, tailWord_1414405, baseEnd_1414405] using wordTrace_append hprefix tailTrace_1414405
  have hstable : (prefixWord ++ tailWord_1414405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414405).length < 2 ^ (prefixWord ++ tailWord_1414405).sum := by decide
  have hdescent : baseEnd_1414405 < baseStart_1414405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414409 : List Nat := [1, 2, 1, 1, 3, 3, 1, 6, 1, 3]
def baseStart_1414409 : Nat := 118140960795 + 1414409 * 2 ^ 59
def prefixEnd_1414409 : Nat := 4983230072969 + 3 ^ 40 * 1414409 * 2
def baseEnd_1414409 : Nat := 484181106030174567988505

theorem tailTrace_1414409 : CollatzResearch.WordTrace tailWord_1414409 prefixEnd_1414409 484181106030174567988505 := by
  unfold tailWord_1414409
  simp only [CollatzResearch.WordTrace]
  refine ⟨51587734332845229670590281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34391822888563486447060187 51587734332845229670590281)
  ·
    refine ⟨38690800749633922252942711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51587734332845229670590281 38690800749633922252942711)
    ·
      refine ⟨58036201124450883379414067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38690800749633922252942711 58036201124450883379414067)
      ·
        refine ⟨87054301686676325069121101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58036201124450883379414067 87054301686676325069121101)
        ·
          refine ⟨32645363132503621900920413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87054301686676325069121101 32645363132503621900920413)
          ·
            refine ⟨12242011174688858212845155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32645363132503621900920413 12242011174688858212845155)
            ·
              refine ⟨18363016762033287319267733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12242011174688858212845155 18363016762033287319267733)
              ·
                refine ⟨860766410720310343090675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18363016762033287319267733 860766410720310343090675)
                ·
                  refine ⟨1291149616080465514636013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 860766410720310343090675 1291149616080465514636013)
                  ·
                    refine ⟨484181106030174567988505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1291149616080465514636013 484181106030174567988505)
                    ·
                      rfl

theorem cell22_1414409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 1, 3].length) (baseStart_1414409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414409 prefixEnd_1414409 := by exact prefixLift 1414409
  have htrace : WordTrace (prefixWord ++ tailWord_1414409) baseStart_1414409 baseEnd_1414409 := by
    simpa [prefixWord, tailWord_1414409, baseEnd_1414409] using wordTrace_append hprefix tailTrace_1414409
  have hstable : (prefixWord ++ tailWord_1414409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414409).length < 2 ^ (prefixWord ++ tailWord_1414409).sum := by decide
  have hdescent : baseEnd_1414409 < baseStart_1414409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414482 : List Nat := [3, 2, 2, 1, 1, 1, 1, 5, 1, 5]
def baseStart_1414482 : Nat := 118140960795 + 1414482 * 2 ^ 59
def prefixEnd_1414482 : Nat := 4983230072969 + 3 ^ 40 * 1414482 * 2
def baseEnd_1414482 : Nat := 484206095422026710913281

theorem tailTrace_1414482 : CollatzResearch.WordTrace tailWord_1414482 prefixEnd_1414482 484206095422026710913281 := by
  unfold tailWord_1414482
  simp only [CollatzResearch.WordTrace]
  refine ⟨12897599215395190784499425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34393597907720508758665133 12897599215395190784499425)
  ·
    refine ⟨9673199411546393088374569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12897599215395190784499425 9673199411546393088374569)
    ·
      refine ⟨7254899558659794816280927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9673199411546393088374569 7254899558659794816280927)
      ·
        refine ⟨10882349337989692224421391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7254899558659794816280927 10882349337989692224421391)
        ·
          refine ⟨16323524006984538336632087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10882349337989692224421391 16323524006984538336632087)
          ·
            refine ⟨24485286010476807504948131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16323524006984538336632087 24485286010476807504948131)
            ·
              refine ⟨36727929015715211257422197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24485286010476807504948131 36727929015715211257422197)
              ·
                refine ⟨3443243345223301055383331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36727929015715211257422197 3443243345223301055383331)
                ·
                  refine ⟨5164865017834951583074997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3443243345223301055383331 5164865017834951583074997)
                  ·
                    refine ⟨484206095422026710913281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5164865017834951583074997 484206095422026710913281)
                    ·
                      rfl

theorem cell22_1414482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_1414482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414482 prefixEnd_1414482 := by exact prefixLift 1414482
  have htrace : WordTrace (prefixWord ++ tailWord_1414482) baseStart_1414482 baseEnd_1414482 := by
    simpa [prefixWord, tailWord_1414482, baseEnd_1414482] using wordTrace_append hprefix tailTrace_1414482
  have hstable : (prefixWord ++ tailWord_1414482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414482).length < 2 ^ (prefixWord ++ tailWord_1414482).sum := by decide
  have hdescent : baseEnd_1414482 < baseStart_1414482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414572 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 2, 5]
def baseStart_1414572 : Nat := 118140960795 + 1414572 * 2 ^ 59
def prefixEnd_1414572 : Nat := 4983230072969 + 3 ^ 40 * 1414572 * 2
def baseEnd_1414572 : Nat := 484236904261296476163005

theorem tailTrace_1414572 : CollatzResearch.WordTrace tailWord_1414572 prefixEnd_1414572 484236904261296476163005 := by
  unfold tailWord_1414572
  simp only [CollatzResearch.WordTrace]
  refine ⟨25796839715627354254386985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34395786287503139005849313 25796839715627354254386985)
  ·
    refine ⟨19347629786720515690790239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25796839715627354254386985 19347629786720515690790239)
    ·
      refine ⟨29021444680080773536185359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19347629786720515690790239 29021444680080773536185359)
      ·
        refine ⟨43532167020121160304278039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29021444680080773536185359 43532167020121160304278039)
        ·
          refine ⟨65298250530181740456417059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43532167020121160304278039 65298250530181740456417059)
          ·
            refine ⟨97947375795272610684625589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65298250530181740456417059 97947375795272610684625589)
            ·
              refine ⟨9182566480806807251683649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97947375795272610684625589 9182566480806807251683649)
              ·
                refine ⟨6886924860605105438762737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9182566480806807251683649 6886924860605105438762737)
                ·
                  refine ⟨5165193645453829079072053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6886924860605105438762737 5165193645453829079072053)
                  ·
                    refine ⟨484236904261296476163005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5165193645453829079072053 484236904261296476163005)
                    ·
                      rfl

theorem cell22_1414572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_1414572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414572 prefixEnd_1414572 := by exact prefixLift 1414572
  have htrace : WordTrace (prefixWord ++ tailWord_1414572) baseStart_1414572 baseEnd_1414572 := by
    simpa [prefixWord, tailWord_1414572, baseEnd_1414572] using wordTrace_append hprefix tailTrace_1414572
  have hstable : (prefixWord ++ tailWord_1414572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414572).length < 2 ^ (prefixWord ++ tailWord_1414572).sum := by decide
  have hdescent : baseEnd_1414572 < baseStart_1414572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414612 : List Nat := [2, 4, 1, 2, 4, 1, 1, 3, 1, 3]
def baseStart_1414612 : Nat := 118140960795 + 1414612 * 2 ^ 59
def prefixEnd_1414612 : Nat := 4983230072969 + 3 ^ 40 * 1414612 * 2
def baseEnd_1414612 : Nat := 484250597078749705162883

theorem tailTrace_1414612 : CollatzResearch.WordTrace tailWord_1414612 prefixEnd_1414612 484250597078749705162883 := by
  unfold tailWord_1414612
  simp only [CollatzResearch.WordTrace]
  refine ⟨25797569175554897670115045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34396758900739863560153393 25797569175554897670115045)
  ·
    refine ⟨4837044220416543313146571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25797569175554897670115045 4837044220416543313146571)
    ·
      refine ⟨7255566330624814969719857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4837044220416543313146571 7255566330624814969719857)
      ·
        refine ⟨5441674747968611227289893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7255566330624814969719857 5441674747968611227289893)
        ·
          refine ⟨1020314015244114605116855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5441674747968611227289893 1020314015244114605116855)
          ·
            refine ⟨1530471022866171907675283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1020314015244114605116855 1530471022866171907675283)
            ·
              refine ⟨2295706534299257861512925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1530471022866171907675283 2295706534299257861512925)
              ·
                refine ⟨860889950362221698067347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2295706534299257861512925 860889950362221698067347)
                ·
                  refine ⟨1291334925543332547101021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 860889950362221698067347 1291334925543332547101021)
                  ·
                    refine ⟨484250597078749705162883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1291334925543332547101021 484250597078749705162883)
                    ·
                      rfl

theorem cell22_1414612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_1414612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414612 prefixEnd_1414612 := by exact prefixLift 1414612
  have htrace : WordTrace (prefixWord ++ tailWord_1414612) baseStart_1414612 baseEnd_1414612 := by
    simpa [prefixWord, tailWord_1414612, baseEnd_1414612] using wordTrace_append hprefix tailTrace_1414612
  have hstable : (prefixWord ++ tailWord_1414612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414612).length < 2 ^ (prefixWord ++ tailWord_1414612).sum := by decide
  have hdescent : baseEnd_1414612 < baseStart_1414612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414621 : List Nat := [1, 4, 3, 1, 1, 2, 2, 3, 1, 4]
def baseStart_1414621 : Nat := 118140960795 + 1414621 * 2 ^ 59
def prefixEnd_1414621 : Nat := 4983230072969 + 3 ^ 40 * 1414621 * 2
def baseEnd_1414621 : Nat := 484253677962676681687855

theorem tailTrace_1414621 : CollatzResearch.WordTrace tailWord_1414621 prefixEnd_1414621 484253677962676681687855 := by
  unfold tailWord_1414621
  simp only [CollatzResearch.WordTrace]
  refine ⟨51595466608077189877307717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34396977738718126584871811 51595466608077189877307717)
  ·
    refine ⟨9674149989014473101995197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51595466608077189877307717 9674149989014473101995197)
    ·
      refine ⟨3627806245880427413248199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9674149989014473101995197 3627806245880427413248199)
      ·
        refine ⟨5441709368820641119872299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3627806245880427413248199 5441709368820641119872299)
        ·
          refine ⟨8162564053230961679808449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5441709368820641119872299 8162564053230961679808449)
          ·
            refine ⟨6121923039923221259856337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8162564053230961679808449 6121923039923221259856337)
            ·
              refine ⟨4591442279942415944892253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6121923039923221259856337 4591442279942415944892253)
              ·
                refine ⟨1721790854978405979334595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4591442279942415944892253 1721790854978405979334595)
                ·
                  refine ⟨2582686282467608969001893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1721790854978405979334595 2582686282467608969001893)
                  ·
                    refine ⟨484253677962676681687855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2582686282467608969001893 484253677962676681687855)
                    ·
                      rfl

theorem cell22_1414621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_1414621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414621 prefixEnd_1414621 := by exact prefixLift 1414621
  have htrace : WordTrace (prefixWord ++ tailWord_1414621) baseStart_1414621 baseEnd_1414621 := by
    simpa [prefixWord, tailWord_1414621, baseEnd_1414621] using wordTrace_append hprefix tailTrace_1414621
  have hstable : (prefixWord ++ tailWord_1414621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414621).length < 2 ^ (prefixWord ++ tailWord_1414621).sum := by decide
  have hdescent : baseEnd_1414621 < baseStart_1414621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414666 : List Nat := [3, 1, 2, 2, 2, 3, 2, 1, 2, 4]
def baseStart_1414666 : Nat := 118140960795 + 1414666 * 2 ^ 59
def prefixEnd_1414666 : Nat := 4983230072969 + 3 ^ 40 * 1414666 * 2
def baseEnd_1414666 : Nat := 484269082382311564312717

theorem tailTrace_1414666 : CollatzResearch.WordTrace tailWord_1414666 prefixEnd_1414666 484269082382311564312717 := by
  unfold tailWord_1414666
  simp only [CollatzResearch.WordTrace]
  refine ⟨12899276973228540640673963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34398071928609441708463901 12899276973228540640673963)
  ·
    refine ⟨19348915459842810961010945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12899276973228540640673963 19348915459842810961010945)
    ·
      refine ⟨14511686594882108220758209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19348915459842810961010945 14511686594882108220758209)
      ·
        refine ⟨10883764946161581165568657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14511686594882108220758209 10883764946161581165568657)
        ·
          refine ⟨8162823709621185874176493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10883764946161581165568657 8162823709621185874176493)
          ·
            refine ⟨3061058891107944702816185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8162823709621185874176493 3061058891107944702816185)
            ·
              refine ⟨2295794168330958527112139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3061058891107944702816185 2295794168330958527112139)
              ·
                refine ⟨3443691252496437790668209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2295794168330958527112139 3443691252496437790668209)
                ·
                  refine ⟨2582768439372328343001157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3443691252496437790668209 2582768439372328343001157)
                  ·
                    refine ⟨484269082382311564312717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2582768439372328343001157 484269082382311564312717)
                    ·
                      rfl

theorem cell22_1414666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_1414666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414666 prefixEnd_1414666 := by exact prefixLift 1414666
  have htrace : WordTrace (prefixWord ++ tailWord_1414666) baseStart_1414666 baseEnd_1414666 := by
    simpa [prefixWord, tailWord_1414666, baseEnd_1414666] using wordTrace_append hprefix tailTrace_1414666
  have hstable : (prefixWord ++ tailWord_1414666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414666).length < 2 ^ (prefixWord ++ tailWord_1414666).sum := by decide
  have hdescent : baseEnd_1414666 < baseStart_1414666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414773 : List Nat := [1, 3, 4, 2, 1, 1, 1, 4, 1, 4]
def baseStart_1414773 : Nat := 118140960795 + 1414773 * 2 ^ 59
def prefixEnd_1414773 : Nat := 4983230072969 + 3 ^ 40 * 1414773 * 2
def baseEnd_1414773 : Nat := 484305710668998951887389

theorem tailTrace_1414773 : CollatzResearch.WordTrace tailWord_1414773 prefixEnd_1414773 484305710668998951887389 := by
  unfold tailWord_1414773
  simp only [CollatzResearch.WordTrace]
  refine ⟨51601010503526519836840973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34400673669017679891227315 51601010503526519836840973)
  ·
    refine ⟨19350378938822444938815365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51601010503526519836840973 19350378938822444938815365)
    ·
      refine ⟨3628196051029208426027881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19350378938822444938815365 3628196051029208426027881)
      ·
        refine ⟨2721147038271906319520911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3628196051029208426027881 2721147038271906319520911)
        ·
          refine ⟨4081720557407859479281367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2721147038271906319520911 4081720557407859479281367)
          ·
            refine ⟨6122580836111789218922051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4081720557407859479281367 6122580836111789218922051)
            ·
              refine ⟨9183871254167683828383077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6122580836111789218922051 9183871254167683828383077)
              ·
                refine ⟨1721975860156440717821827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9183871254167683828383077 1721975860156440717821827)
                ·
                  refine ⟨2582963790234661076732741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1721975860156440717821827 2582963790234661076732741)
                  ·
                    refine ⟨484305710668998951887389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2582963790234661076732741 484305710668998951887389)
                    ·
                      rfl

theorem cell22_1414773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_1414773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414773 prefixEnd_1414773 := by exact prefixLift 1414773
  have htrace : WordTrace (prefixWord ++ tailWord_1414773) baseStart_1414773 baseEnd_1414773 := by
    simpa [prefixWord, tailWord_1414773, baseEnd_1414773] using wordTrace_append hprefix tailTrace_1414773
  have hstable : (prefixWord ++ tailWord_1414773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414773).length < 2 ^ (prefixWord ++ tailWord_1414773).sum := by decide
  have hdescent : baseEnd_1414773 < baseStart_1414773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414784 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 1, 6]
def baseStart_1414784 : Nat := 118140960795 + 1414784 * 2 ^ 59
def prefixEnd_1414784 : Nat := 4983230072969 + 3 ^ 40 * 1414784 * 2
def baseEnd_1414784 : Nat := 484309476193798589862355

theorem tailTrace_1414784 : CollatzResearch.WordTrace tailWord_1414784 prefixEnd_1414784 484309476193798589862355 := by
  unfold tailWord_1414784
  simp only [CollatzResearch.WordTrace]
  refine ⟨25800705853243334357745703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34400941137657779143660937 25800705853243334357745703)
  ·
    refine ⟨38701058779865001536618555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25800705853243334357745703 38701058779865001536618555)
    ·
      refine ⟨58051588169797502304927833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38701058779865001536618555 58051588169797502304927833)
      ·
        refine ⟨43538691127348126728695875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58051588169797502304927833 43538691127348126728695875)
        ·
          refine ⟨65308036691022190093043813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43538691127348126728695875 65308036691022190093043813)
          ·
            refine ⟨12245256879566660642445715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65308036691022190093043813 12245256879566660642445715)
            ·
              refine ⟨18367885319349990963668573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12245256879566660642445715 18367885319349990963668573)
              ·
                refine ⟨6887956994756246611375715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18367885319349990963668573 6887956994756246611375715)
                ·
                  refine ⟨10331935492134369917063573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6887956994756246611375715 10331935492134369917063573)
                  ·
                    refine ⟨484309476193798589862355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10331935492134369917063573 484309476193798589862355)
                    ·
                      rfl

theorem cell22_1414784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_1414784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414784 prefixEnd_1414784 := by exact prefixLift 1414784
  have htrace : WordTrace (prefixWord ++ tailWord_1414784) baseStart_1414784 baseEnd_1414784 := by
    simpa [prefixWord, tailWord_1414784, baseEnd_1414784] using wordTrace_append hprefix tailTrace_1414784
  have hstable : (prefixWord ++ tailWord_1414784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414784).length < 2 ^ (prefixWord ++ tailWord_1414784).sum := by decide
  have hdescent : baseEnd_1414784 < baseStart_1414784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414816 : List Nat := [2, 1, 1, 4, 3, 2, 2, 7]
def baseStart_1414816 : Nat := 118140960795 + 1414816 * 2 ^ 59
def prefixEnd_1414816 : Nat := 4983230072969 + 3 ^ 40 * 1414816 * 2
def baseEnd_1414816 : Nat := 53813381160862352562473

theorem tailTrace_1414816 : CollatzResearch.WordTrace tailWord_1414816 prefixEnd_1414816 53813381160862352562473 := by
  unfold tailWord_1414816
  simp only [CollatzResearch.WordTrace]
  refine ⟨25801289421185369090328151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34401719228247158787104201 25801289421185369090328151)
  ·
    refine ⟨38701934131778053635492227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25801289421185369090328151 38701934131778053635492227)
    ·
      refine ⟨58052901197667080453238341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38701934131778053635492227 58052901197667080453238341)
      ·
        refine ⟨10884918974562577584982189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58052901197667080453238341 10884918974562577584982189)
        ·
          refine ⟨4081844615460966594368321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10884918974562577584982189 4081844615460966594368321)
          ·
            refine ⟨3061383461595724945776241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4081844615460966594368321 3061383461595724945776241)
            ·
              refine ⟨2296037596196793709332181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3061383461595724945776241 2296037596196793709332181)
              ·
                refine ⟨53813381160862352562473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2296037596196793709332181 53813381160862352562473)
                ·
                  rfl

theorem cell22_1414816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 7].length) (baseStart_1414816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414816 prefixEnd_1414816 := by exact prefixLift 1414816
  have htrace : WordTrace (prefixWord ++ tailWord_1414816) baseStart_1414816 baseEnd_1414816 := by
    simpa [prefixWord, tailWord_1414816, baseEnd_1414816] using wordTrace_append hprefix tailTrace_1414816
  have hstable : (prefixWord ++ tailWord_1414816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414816).length < 2 ^ (prefixWord ++ tailWord_1414816).sum := by decide
  have hdescent : baseEnd_1414816 < baseStart_1414816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414820 : List Nat := [2, 3, 1, 2, 2, 2, 4, 1, 2, 3]
def baseStart_1414820 : Nat := 118140960795 + 1414820 * 2 ^ 59
def prefixEnd_1414820 : Nat := 4983230072969 + 3 ^ 40 * 1414820 * 2
def baseEnd_1414820 : Nat := 484321799729506495962245

theorem tailTrace_1414820 : CollatzResearch.WordTrace tailWord_1414820 prefixEnd_1414820 484321799729506495962245 := by
  unfold tailWord_1414820
  simp only [CollatzResearch.WordTrace]
  refine ⟨25801362367178123431900957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34401816489570831242534609 25801362367178123431900957)
  ·
    refine ⟨9675510887691796286962859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25801362367178123431900957 9675510887691796286962859)
    ·
      refine ⟨14513266331537694430444289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9675510887691796286962859 14513266331537694430444289)
      ·
        refine ⟨10884949748653270822833217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14513266331537694430444289 10884949748653270822833217)
        ·
          refine ⟨8163712311489953117124913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10884949748653270822833217 8163712311489953117124913)
          ·
            refine ⟨6122784233617464837843685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8163712311489953117124913 6122784233617464837843685)
            ·
              refine ⟨1148022043803274657095691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6122784233617464837843685 1148022043803274657095691)
              ·
                refine ⟨1722033065704911985643537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1148022043803274657095691 1722033065704911985643537)
                ·
                  refine ⟨1291524799278683989232653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1722033065704911985643537 1291524799278683989232653)
                  ·
                    refine ⟨484321799729506495962245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1291524799278683989232653 484321799729506495962245)
                    ·
                      rfl

theorem cell22_1414820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_1414820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414820 prefixEnd_1414820 := by exact prefixLift 1414820
  have htrace : WordTrace (prefixWord ++ tailWord_1414820) baseStart_1414820 baseEnd_1414820 := by
    simpa [prefixWord, tailWord_1414820, baseEnd_1414820] using wordTrace_append hprefix tailTrace_1414820
  have hstable : (prefixWord ++ tailWord_1414820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414820).length < 2 ^ (prefixWord ++ tailWord_1414820).sum := by decide
  have hdescent : baseEnd_1414820 < baseStart_1414820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414824 : List Nat := [2, 1, 7, 1, 1, 2, 1, 2, 1, 4]
def baseStart_1414824 : Nat := 118140960795 + 1414824 * 2 ^ 59
def prefixEnd_1414824 : Nat := 4983230072969 + 3 ^ 40 * 1414824 * 2
def baseEnd_1414824 : Nat := 484323169011251818862233

theorem tailTrace_1414824 : CollatzResearch.WordTrace tailWord_1414824 prefixEnd_1414824 484323169011251818862233 := by
  unfold tailWord_1414824
  simp only [CollatzResearch.WordTrace]
  refine ⟨25801435313170877773473763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34401913750894503697965017 25801435313170877773473763)
  ·
    refine ⟨38702152969756316660210645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25801435313170877773473763 38702152969756316660210645)
    ·
      refine ⟨907081710228663671723687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 38702152969756316660210645 907081710228663671723687)
      ·
        refine ⟨1360622565342995507585531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 907081710228663671723687 1360622565342995507585531)
        ·
          refine ⟨2040933848014493261378297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1360622565342995507585531 2040933848014493261378297)
          ·
            refine ⟨1530700386010869946033723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2040933848014493261378297 1530700386010869946033723)
            ·
              refine ⟨2296050579016304919050585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1530700386010869946033723 2296050579016304919050585)
              ·
                refine ⟨1722037934262228689287939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2296050579016304919050585 1722037934262228689287939)
                ·
                  refine ⟨2583056901393343033931909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1722037934262228689287939 2583056901393343033931909)
                  ·
                    refine ⟨484323169011251818862233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2583056901393343033931909 484323169011251818862233)
                    ·
                      rfl

theorem cell22_1414824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_1414824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414824 prefixEnd_1414824 := by exact prefixLift 1414824
  have htrace : WordTrace (prefixWord ++ tailWord_1414824) baseStart_1414824 baseEnd_1414824 := by
    simpa [prefixWord, tailWord_1414824, baseEnd_1414824] using wordTrace_append hprefix tailTrace_1414824
  have hstable : (prefixWord ++ tailWord_1414824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414824).length < 2 ^ (prefixWord ++ tailWord_1414824).sum := by decide
  have hdescent : baseEnd_1414824 < baseStart_1414824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414831 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 5, 3]
def baseStart_1414831 : Nat := 118140960795 + 1414831 * 2 ^ 59
def prefixEnd_1414831 : Nat := 4983230072969 + 3 ^ 40 * 1414831 * 2
def baseEnd_1414831 : Nat := 484325565254306133937211

theorem tailTrace_1414831 : CollatzResearch.WordTrace tailWord_1414831 prefixEnd_1414831 484325565254306133937211 := by
  unfold tailWord_1414831
  simp only [CollatzResearch.WordTrace]
  refine ⟨51603125937316395742452347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34402083958210930494968231 51603125937316395742452347)
  ·
    refine ⟨77404688905974593613678521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51603125937316395742452347 77404688905974593613678521)
    ·
      refine ⟨58053516679480945210258891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77404688905974593613678521 58053516679480945210258891)
      ·
        refine ⟨87080275019221417815388337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58053516679480945210258891 87080275019221417815388337)
        ·
          refine ⟨65310206264416063361541253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87080275019221417815388337 65310206264416063361541253)
          ·
            refine ⟨12245663674578011880288985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65310206264416063361541253 12245663674578011880288985)
            ·
              refine ⟨9184247755933508910216739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12245663674578011880288985 9184247755933508910216739)
              ·
                refine ⟨13776371633900263365325109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9184247755933508910216739 13776371633900263365325109)
                ·
                  refine ⟨1291534840678149690499229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13776371633900263365325109 1291534840678149690499229)
                  ·
                    refine ⟨484325565254306133937211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1291534840678149690499229 484325565254306133937211)
                    ·
                      rfl

theorem cell22_1414831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 3].length) (baseStart_1414831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414831 prefixEnd_1414831 := by exact prefixLift 1414831
  have htrace : WordTrace (prefixWord ++ tailWord_1414831) baseStart_1414831 baseEnd_1414831 := by
    simpa [prefixWord, tailWord_1414831, baseEnd_1414831] using wordTrace_append hprefix tailTrace_1414831
  have hstable : (prefixWord ++ tailWord_1414831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414831).length < 2 ^ (prefixWord ++ tailWord_1414831).sum := by decide
  have hdescent : baseEnd_1414831 < baseStart_1414831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414850 : List Nat := [3, 5, 1, 2, 1, 10]
def baseStart_1414850 : Nat := 118140960795 + 1414850 * 2 ^ 59
def prefixEnd_1414850 : Nat := 4983230072969 + 3 ^ 40 * 1414850 * 2
def baseEnd_1414850 : Nat := 5979408263488844663113

theorem tailTrace_1414850 : CollatzResearch.WordTrace tailWord_1414850 prefixEnd_1414850 5979408263488844663113 := by
  unfold tailWord_1414850
  simp only [CollatzResearch.WordTrace]
  refine ⟨12900954731061890496848501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34402545949498374658262669 12900954731061890496848501)
  ·
    refine ⟨1209464506037052234079547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12900954731061890496848501 1209464506037052234079547)
    ·
      refine ⟨1814196759055578351119321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1209464506037052234079547 1814196759055578351119321)
      ·
        refine ⟨1360647569291683763339491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1814196759055578351119321 1360647569291683763339491)
        ·
          refine ⟨2040971353937525645009237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1360647569291683763339491 2040971353937525645009237)
          ·
            refine ⟨5979408263488844663113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2040971353937525645009237 5979408263488844663113)
            ·
              rfl

theorem cell22_1414850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 10].length) (baseStart_1414850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414850 prefixEnd_1414850 := by exact prefixLift 1414850
  have htrace : WordTrace (prefixWord ++ tailWord_1414850) baseStart_1414850 baseEnd_1414850 := by
    simpa [prefixWord, tailWord_1414850, baseEnd_1414850] using wordTrace_append hprefix tailTrace_1414850
  have hstable : (prefixWord ++ tailWord_1414850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414850).length < 2 ^ (prefixWord ++ tailWord_1414850).sum := by decide
  have hdescent : baseEnd_1414850 < baseStart_1414850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414854 : List Nat := [6, 1, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_1414854 : Nat := 118140960795 + 1414854 * 2 ^ 59
def prefixEnd_1414854 : Nat := 4983230072969 + 3 ^ 40 * 1414854 * 2
def baseEnd_1414854 : Nat := 484333438624341740612141

theorem tailTrace_1414854 : CollatzResearch.WordTrace tailWord_1414854 prefixEnd_1414854 484333438624341740612141 := by
  unfold tailWord_1414854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1612623900507283458454363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34402643210822047113693077 1612623900507283458454363)
  ·
    refine ⟨2418935850760925187681545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1612623900507283458454363 2418935850760925187681545)
    ·
      refine ⟨1814201888070693890761159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2418935850760925187681545 1814201888070693890761159)
      ·
        refine ⟨2721302832106040836141739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1814201888070693890761159 2721302832106040836141739)
        ·
          refine ⟨4081954248159061254212609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2721302832106040836141739 4081954248159061254212609)
          ·
            refine ⟨3061465686119295940659457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4081954248159061254212609 3061465686119295940659457)
            ·
              refine ⟨2296099264589471955494593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3061465686119295940659457 2296099264589471955494593)
              ·
                refine ⟨1722074448442103966620945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2296099264589471955494593 1722074448442103966620945)
                ·
                  refine ⟨1291555836331577974965709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1722074448442103966620945 1291555836331577974965709)
                  ·
                    refine ⟨484333438624341740612141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1291555836331577974965709 484333438624341740612141)
                    ·
                      rfl

theorem cell22_1414854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_1414854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414854 prefixEnd_1414854 := by exact prefixLift 1414854
  have htrace : WordTrace (prefixWord ++ tailWord_1414854) baseStart_1414854 baseEnd_1414854 := by
    simpa [prefixWord, tailWord_1414854, baseEnd_1414854] using wordTrace_append hprefix tailTrace_1414854
  have hstable : (prefixWord ++ tailWord_1414854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414854).length < 2 ^ (prefixWord ++ tailWord_1414854).sum := by decide
  have hdescent : baseEnd_1414854 < baseStart_1414854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414859 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 3, 7]
def baseStart_1414859 : Nat := 118140960795 + 1414859 * 2 ^ 59
def prefixEnd_1414859 : Nat := 4983230072969 + 3 ^ 40 * 1414859 * 2
def baseEnd_1414859 : Nat := 484335150226523394237125

theorem tailTrace_1414859 : CollatzResearch.WordTrace tailWord_1414859 prefixEnd_1414859 484335150226523394237125 := by
  unfold tailWord_1414859
  simp only [CollatzResearch.WordTrace]
  refine ⟨51604147181214956524471631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34402764787476637682981087 51604147181214956524471631)
  ·
    refine ⟨77406220771822434786707447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51604147181214956524471631 77406220771822434786707447)
    ·
      refine ⟨116109331157733652180061171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77406220771822434786707447 116109331157733652180061171)
      ·
        refine ⟨174163996736600478270091757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116109331157733652180061171 174163996736600478270091757)
        ·
          refine ⟨65311498776225179351284409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174163996736600478270091757 65311498776225179351284409)
          ·
            refine ⟨48983624082168884513463307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65311498776225179351284409 48983624082168884513463307)
            ·
              refine ⟨73475436123253326770194961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48983624082168884513463307 73475436123253326770194961)
              ·
                refine ⟨55106577092439995077646221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73475436123253326770194961 55106577092439995077646221)
                ·
                  refine ⟨20664966409664998154117333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55106577092439995077646221 20664966409664998154117333)
                  ·
                    refine ⟨484335150226523394237125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20664966409664998154117333 484335150226523394237125)
                    ·
                      rfl

theorem cell22_1414859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 7].length) (baseStart_1414859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414859 prefixEnd_1414859 := by exact prefixLift 1414859
  have htrace : WordTrace (prefixWord ++ tailWord_1414859) baseStart_1414859 baseEnd_1414859 := by
    simpa [prefixWord, tailWord_1414859, baseEnd_1414859] using wordTrace_append hprefix tailTrace_1414859
  have hstable : (prefixWord ++ tailWord_1414859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414859).length < 2 ^ (prefixWord ++ tailWord_1414859).sum := by decide
  have hdescent : baseEnd_1414859 < baseStart_1414859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414865 : List Nat := [1, 2, 2, 1, 2, 5, 1, 4, 1, 3]
def baseStart_1414865 : Nat := 118140960795 + 1414865 * 2 ^ 59
def prefixEnd_1414865 : Nat := 4983230072969 + 3 ^ 40 * 1414865 * 2
def baseEnd_1414865 : Nat := 484337204149141378587107

theorem tailTrace_1414865 : CollatzResearch.WordTrace tailWord_1414865 prefixEnd_1414865 484337204149141378587107 := by
  unfold tailWord_1414865
  simp only [CollatzResearch.WordTrace]
  refine ⟨51604366019193219549190049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34402910679462146366126699 51604366019193219549190049)
  ·
    refine ⟨38703274514394914661892537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51604366019193219549190049 38703274514394914661892537)
    ·
      refine ⟨29027455885796185996419403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38703274514394914661892537 29027455885796185996419403)
      ·
        refine ⟨43541183828694278994629105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29027455885796185996419403 43541183828694278994629105)
        ·
          refine ⟨32655887871520709245971829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43541183828694278994629105 32655887871520709245971829)
          ·
            refine ⟨3061489487955066491809859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32655887871520709245971829 3061489487955066491809859)
            ·
              refine ⟨4592234231932599737714789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3061489487955066491809859 4592234231932599737714789)
              ·
                refine ⟨861043918487362450821523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4592234231932599737714789 861043918487362450821523)
                ·
                  refine ⟨1291565877731043676232285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 861043918487362450821523 1291565877731043676232285)
                  ·
                    refine ⟨484337204149141378587107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1291565877731043676232285 484337204149141378587107)
                    ·
                      rfl

theorem cell22_1414865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 1, 3].length) (baseStart_1414865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414865 prefixEnd_1414865 := by exact prefixLift 1414865
  have htrace : WordTrace (prefixWord ++ tailWord_1414865) baseStart_1414865 baseEnd_1414865 := by
    simpa [prefixWord, tailWord_1414865, baseEnd_1414865] using wordTrace_append hprefix tailTrace_1414865
  have hstable : (prefixWord ++ tailWord_1414865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414865).length < 2 ^ (prefixWord ++ tailWord_1414865).sum := by decide
  have hdescent : baseEnd_1414865 < baseStart_1414865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414891 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 3, 4]
def baseStart_1414891 : Nat := 118140960795 + 1414891 * 2 ^ 59
def prefixEnd_1414891 : Nat := 4983230072969 + 3 ^ 40 * 1414891 * 2
def baseEnd_1414891 : Nat := 484346104480485977437027

theorem tailTrace_1414891 : CollatzResearch.WordTrace tailWord_1414891 prefixEnd_1414891 484346104480485977437027 := by
  unfold tailWord_1414891
  simp only [CollatzResearch.WordTrace]
  refine ⟨51605314317099025989636527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34403542878066017326424351 51605314317099025989636527)
  ·
    refine ⟨77407971475648538984454791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51605314317099025989636527 77407971475648538984454791)
    ·
      refine ⟨116111957213472808476682187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77407971475648538984454791 116111957213472808476682187)
      ·
        refine ⟨174167935820209212715023281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116111957213472808476682187 174167935820209212715023281)
        ·
          refine ⟨130625951865156909536267461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174167935820209212715023281 130625951865156909536267461)
          ·
            refine ⟨24492365974716920538050149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130625951865156909536267461 24492365974716920538050149)
            ·
              refine ⟨4592318620259422600884403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24492365974716920538050149 4592318620259422600884403)
              ·
                refine ⟨6888477930389133901326605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4592318620259422600884403 6888477930389133901326605)
                ·
                  refine ⟨2583179223895925212997477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6888477930389133901326605 2583179223895925212997477)
                  ·
                    refine ⟨484346104480485977437027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2583179223895925212997477 484346104480485977437027)
                    ·
                      rfl

theorem cell22_1414891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 4].length) (baseStart_1414891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414891 prefixEnd_1414891 := by exact prefixLift 1414891
  have htrace : WordTrace (prefixWord ++ tailWord_1414891) baseStart_1414891 baseEnd_1414891 := by
    simpa [prefixWord, tailWord_1414891, baseEnd_1414891] using wordTrace_append hprefix tailTrace_1414891
  have hstable : (prefixWord ++ tailWord_1414891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414891).length < 2 ^ (prefixWord ++ tailWord_1414891).sum := by decide
  have hdescent : baseEnd_1414891 < baseStart_1414891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414908 : List Nat := [2, 2, 2, 1, 3, 1, 3, 3, 1, 4]
def baseStart_1414908 : Nat := 118140960795 + 1414908 * 2 ^ 59
def prefixEnd_1414908 : Nat := 4983230072969 + 3 ^ 40 * 1414908 * 2
def baseEnd_1414908 : Nat := 484351923927903599761975

theorem tailTrace_1414908 : CollatzResearch.WordTrace tailWord_1414908 prefixEnd_1414908 484351923927903599761975 := by
  unfold tailWord_1414908
  simp only [CollatzResearch.WordTrace]
  refine ⟨25802967179018718946502689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34403956238691625262003585 25802967179018718946502689)
  ·
    refine ⟨19352225384264039209877017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25802967179018718946502689 19352225384264039209877017)
    ·
      refine ⟨14514169038198029407407763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19352225384264039209877017 14514169038198029407407763)
      ·
        refine ⟨21771253557297044111111645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14514169038198029407407763 21771253557297044111111645)
        ·
          refine ⟨8164220083986391541666867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21771253557297044111111645 8164220083986391541666867)
          ·
            refine ⟨12246330125979587312500301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8164220083986391541666867 12246330125979587312500301)
            ·
              refine ⟨4592373797242345242187613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12246330125979587312500301 4592373797242345242187613)
              ·
                refine ⟨1722140173965879465820355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4592373797242345242187613 1722140173965879465820355)
                ·
                  refine ⟨2583210260948819198730533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1722140173965879465820355 2583210260948819198730533)
                  ·
                    refine ⟨484351923927903599761975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2583210260948819198730533 484351923927903599761975)
                    ·
                      rfl

theorem cell22_1414908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_1414908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414908 prefixEnd_1414908 := by exact prefixLift 1414908
  have htrace : WordTrace (prefixWord ++ tailWord_1414908) baseStart_1414908 baseEnd_1414908 := by
    simpa [prefixWord, tailWord_1414908, baseEnd_1414908] using wordTrace_append hprefix tailTrace_1414908
  have hstable : (prefixWord ++ tailWord_1414908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414908).length < 2 ^ (prefixWord ++ tailWord_1414908).sum := by decide
  have hdescent : baseEnd_1414908 < baseStart_1414908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414923 : List Nat := [1, 1, 1, 1, 5, 1, 4, 4, 4]
def baseStart_1414923 : Nat := 118140960795 + 1414923 * 2 ^ 59
def prefixEnd_1414923 : Nat := 4983230072969 + 3 ^ 40 * 1414923 * 2
def baseEnd_1414923 : Nat := 161452352911482853545643

theorem tailTrace_1414923 : CollatzResearch.WordTrace tailWord_1414923 prefixEnd_1414923 161452352911482853545643 := by
  unfold tailWord_1414923
  simp only [CollatzResearch.WordTrace]
  refine ⟨51606481452983095454801423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34404320968655396969867615 51606481452983095454801423)
  ·
    refine ⟨77409722179474643182202135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51606481452983095454801423 77409722179474643182202135)
    ·
      refine ⟨116114583269211964773303203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77409722179474643182202135 116114583269211964773303203)
      ·
        refine ⟨174171874903817947159954805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116114583269211964773303203 174171874903817947159954805)
        ·
          refine ⟨16328613272232932546245763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174171874903817947159954805 16328613272232932546245763)
          ·
            refine ⟨24492919908349398819368645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16328613272232932546245763 24492919908349398819368645)
            ·
              refine ⟨4592422482815512278631621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24492919908349398819368645 4592422482815512278631621)
              ·
                refine ⟨861079215527908552243429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4592422482815512278631621 861079215527908552243429)
                ·
                  refine ⟨161452352911482853545643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 861079215527908552243429 161452352911482853545643)
                  ·
                    rfl

theorem cell22_1414923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 4].length) (baseStart_1414923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414923 prefixEnd_1414923 := by exact prefixLift 1414923
  have htrace : WordTrace (prefixWord ++ tailWord_1414923) baseStart_1414923 baseEnd_1414923 := by
    simpa [prefixWord, tailWord_1414923, baseEnd_1414923] using wordTrace_append hprefix tailTrace_1414923
  have hstable : (prefixWord ++ tailWord_1414923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414923).length < 2 ^ (prefixWord ++ tailWord_1414923).sum := by decide
  have hdescent : baseEnd_1414923 < baseStart_1414923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414936 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 1, 6]
def baseStart_1414936 : Nat := 118140960795 + 1414936 * 2 ^ 59
def prefixEnd_1414936 : Nat := 4983230072969 + 3 ^ 40 * 1414936 * 2
def baseEnd_1414936 : Nat := 484361508900120860061889

theorem tailTrace_1414936 : CollatzResearch.WordTrace tailWord_1414936 prefixEnd_1414936 484361508900120860061889 := by
  unfold tailWord_1414936
  simp only [CollatzResearch.WordTrace]
  refine ⟨25803477800967999337512331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34404637067957332450016441 25803477800967999337512331)
  ·
    refine ⟨38705216701451999006268497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25803477800967999337512331 38705216701451999006268497)
    ·
      refine ⟨29028912526088999254701373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38705216701451999006268497 29028912526088999254701373)
      ·
        refine ⟨10885842197283374720513015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29028912526088999254701373 10885842197283374720513015)
        ·
          refine ⟨16328763295925062080769523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10885842197283374720513015 16328763295925062080769523)
          ·
            refine ⟨24493144943887593121154285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16328763295925062080769523 24493144943887593121154285)
            ·
              refine ⟨9184929353957847420432857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24493144943887593121154285 9184929353957847420432857)
              ·
                refine ⟨6888697015468385565324643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9184929353957847420432857 6888697015468385565324643)
                ·
                  refine ⟨10333045523202578347986965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6888697015468385565324643 10333045523202578347986965)
                  ·
                    refine ⟨484361508900120860061889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10333045523202578347986965 484361508900120860061889)
                    ·
                      rfl

theorem cell22_1414936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_1414936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414936 prefixEnd_1414936 := by exact prefixLift 1414936
  have htrace : WordTrace (prefixWord ++ tailWord_1414936) baseStart_1414936 baseEnd_1414936 := by
    simpa [prefixWord, tailWord_1414936, baseEnd_1414936] using wordTrace_append hprefix tailTrace_1414936
  have hstable : (prefixWord ++ tailWord_1414936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414936).length < 2 ^ (prefixWord ++ tailWord_1414936).sum := by decide
  have hdescent : baseEnd_1414936 < baseStart_1414936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414938 : List Nat := [3, 1, 1, 3, 2, 2, 3, 1, 1, 5]
def baseStart_1414938 : Nat := 118140960795 + 1414938 * 2 ^ 59
def prefixEnd_1414938 : Nat := 4983230072969 + 3 ^ 40 * 1414938 * 2
def baseEnd_1414938 : Nat := 484362193540993521511883

theorem tailTrace_1414938 : CollatzResearch.WordTrace tailWord_1414938 prefixEnd_1414938 484362193540993521511883 := by
  unfold tailWord_1414938
  simp only [CollatzResearch.WordTrace]
  refine ⟨12901757136982188254149367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34404685698619168677731645 12901757136982188254149367)
  ·
    refine ⟨19352635705473282381224051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12901757136982188254149367 19352635705473282381224051)
    ·
      refine ⟨29028953558209923571836077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19352635705473282381224051 29028953558209923571836077)
      ·
        refine ⟨10885857584328721339438529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29028953558209923571836077 10885857584328721339438529)
        ·
          refine ⟨8164393188246541004578897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10885857584328721339438529 8164393188246541004578897)
          ·
            refine ⟨6123294891184905753434173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8164393188246541004578897 6123294891184905753434173)
            ·
              refine ⟨2296235584194339657537815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6123294891184905753434173 2296235584194339657537815)
              ·
                refine ⟨3444353376291509486306723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2296235584194339657537815 3444353376291509486306723)
                ·
                  refine ⟨5166530064437264229460085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3444353376291509486306723 5166530064437264229460085)
                  ·
                    refine ⟨484362193540993521511883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5166530064437264229460085 484362193540993521511883)
                    ·
                      rfl

theorem cell22_1414938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_1414938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414938 prefixEnd_1414938 := by exact prefixLift 1414938
  have htrace : WordTrace (prefixWord ++ tailWord_1414938) baseStart_1414938 baseEnd_1414938 := by
    simpa [prefixWord, tailWord_1414938, baseEnd_1414938] using wordTrace_append hprefix tailTrace_1414938
  have hstable : (prefixWord ++ tailWord_1414938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414938).length < 2 ^ (prefixWord ++ tailWord_1414938).sum := by decide
  have hdescent : baseEnd_1414938 < baseStart_1414938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414981 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 2, 6]
def baseStart_1414981 : Nat := 118140960795 + 1414981 * 2 ^ 59
def prefixEnd_1414981 : Nat := 4983230072969 + 3 ^ 40 * 1414981 * 2
def baseEnd_1414981 : Nat := 484376913319755742686751

theorem tailTrace_1414981 : CollatzResearch.WordTrace tailWord_1414981 prefixEnd_1414981 484376913319755742686751 := by
  unfold tailWord_1414981
  simp only [CollatzResearch.WordTrace]
  refine ⟨51608596886772971360412797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34405731257848647573608531 51608596886772971360412797)
  ·
    refine ⟨19353223832539864260154799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51608596886772971360412797 19353223832539864260154799)
    ·
      refine ⟨29029835748809796390232199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19353223832539864260154799 29029835748809796390232199)
      ·
        refine ⟨43544753623214694585348299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29029835748809796390232199 43544753623214694585348299)
        ·
          refine ⟨65317130434822041878022449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43544753623214694585348299 65317130434822041878022449)
          ·
            refine ⟨48987847826116531408516837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65317130434822041878022449 48987847826116531408516837)
            ·
              refine ⟨9185221467396849639096907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48987847826116531408516837 9185221467396849639096907)
              ·
                refine ⟨13777832201095274458645361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9185221467396849639096907 13777832201095274458645361)
                ·
                  refine ⟨10333374150821455843984021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13777832201095274458645361 10333374150821455843984021)
                  ·
                    refine ⟨484376913319755742686751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10333374150821455843984021 484376913319755742686751)
                    ·
                      rfl

theorem cell22_1414981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_1414981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414981 prefixEnd_1414981 := by exact prefixLift 1414981
  have htrace : WordTrace (prefixWord ++ tailWord_1414981) baseStart_1414981 baseEnd_1414981 := by
    simpa [prefixWord, tailWord_1414981, baseEnd_1414981] using wordTrace_append hprefix tailTrace_1414981
  have hstable : (prefixWord ++ tailWord_1414981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414981).length < 2 ^ (prefixWord ++ tailWord_1414981).sum := by decide
  have hdescent : baseEnd_1414981 < baseStart_1414981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414989 : List Nat := [1, 6, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_1414989 : Nat := 118140960795 + 1414989 * 2 ^ 59
def prefixEnd_1414989 : Nat := 4983230072969 + 3 ^ 40 * 1414989 * 2
def baseEnd_1414989 : Nat := 484379651883246388486727

theorem tailTrace_1414989 : CollatzResearch.WordTrace tailWord_1414989 prefixEnd_1414989 484379651883246388486727 := by
  unfold tailWord_1414989
  simp only [CollatzResearch.WordTrace]
  refine ⟨51608888670743988726704021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34405925780495992484469347 51608888670743988726704021)
  ·
    refine ⟨2419166656441124471564251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51608888670743988726704021 2419166656441124471564251)
    ·
      refine ⟨3628749984661686707346377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2419166656441124471564251 3628749984661686707346377)
      ·
        refine ⟨2721562488496265030509783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3628749984661686707346377 2721562488496265030509783)
        ·
          refine ⟨4082343732744397545764675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2721562488496265030509783 4082343732744397545764675)
          ·
            refine ⟨6123515599116596318647013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4082343732744397545764675 6123515599116596318647013)
            ·
              refine ⟨1148159174834361809746315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6123515599116596318647013 1148159174834361809746315)
              ·
                refine ⟨1722238762251542714619473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1148159174834361809746315 1722238762251542714619473)
                ·
                  refine ⟨1291679071688657035964605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1722238762251542714619473 1291679071688657035964605)
                  ·
                    refine ⟨484379651883246388486727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1291679071688657035964605 484379651883246388486727)
                    ·
                      rfl

theorem cell22_1414989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_1414989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1414989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1414989 prefixEnd_1414989 := by exact prefixLift 1414989
  have htrace : WordTrace (prefixWord ++ tailWord_1414989) baseStart_1414989 baseEnd_1414989 := by
    simpa [prefixWord, tailWord_1414989, baseEnd_1414989] using wordTrace_append hprefix tailTrace_1414989
  have hstable : (prefixWord ++ tailWord_1414989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414989).length < 2 ^ (prefixWord ++ tailWord_1414989).sum := by decide
  have hdescent : baseEnd_1414989 < baseStart_1414989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415043 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 3, 4]
def baseStart_1415043 : Nat := 118140960795 + 1415043 * 2 ^ 59
def prefixEnd_1415043 : Nat := 4983230072969 + 3 ^ 40 * 1415043 * 2
def baseEnd_1415043 : Nat := 484398137186808247636561

theorem tailTrace_1415043 : CollatzResearch.WordTrace tailWord_1415043 prefixEnd_1415043 484398137186808247636561 := by
  unfold tailWord_1415043
  simp only [CollatzResearch.WordTrace]
  refine ⟨51610858212548355949169783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34407238808365570632779855 51610858212548355949169783)
  ·
    refine ⟨77416287318822533923754675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51610858212548355949169783 77416287318822533923754675)
    ·
      refine ⟨116124430978233800885632013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77416287318822533923754675 116124430978233800885632013)
      ·
        refine ⟨43546661616837675332112005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116124430978233800885632013 43546661616837675332112005)
        ·
          refine ⟨8164999053157064124771001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43546661616837675332112005 8164999053157064124771001)
          ·
            refine ⟨6123749289867798093578251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8164999053157064124771001 6123749289867798093578251)
            ·
              refine ⟨9185623934801697140367377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6123749289867798093578251 9185623934801697140367377)
              ·
                refine ⟨6889217951101272855275533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9185623934801697140367377 6889217951101272855275533)
                ·
                  refine ⟨2583456731662977320728325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6889217951101272855275533 2583456731662977320728325)
                  ·
                    refine ⟨484398137186808247636561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2583456731662977320728325 484398137186808247636561)
                    ·
                      rfl

theorem cell22_1415043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 4].length) (baseStart_1415043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415043 prefixEnd_1415043 := by exact prefixLift 1415043
  have htrace : WordTrace (prefixWord ++ tailWord_1415043) baseStart_1415043 baseEnd_1415043 := by
    simpa [prefixWord, tailWord_1415043, baseEnd_1415043] using wordTrace_append hprefix tailTrace_1415043
  have hstable : (prefixWord ++ tailWord_1415043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415043).length < 2 ^ (prefixWord ++ tailWord_1415043).sum := by decide
  have hdescent : baseEnd_1415043 < baseStart_1415043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415060 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_1415060 : Nat := 118140960795 + 1415060 * 2 ^ 59
def prefixEnd_1415060 : Nat := 4983230072969 + 3 ^ 40 * 1415060 * 2
def baseEnd_1415060 : Nat := 484403956634225869961509

theorem tailTrace_1415060 : CollatzResearch.WordTrace tailWord_1415060 prefixEnd_1415060 484403956634225869961509 := by
  unfold tailWord_1415060
  simp only [CollatzResearch.WordTrace]
  refine ⟨25805739126743383926269317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34407652168991178568359089 25805739126743383926269317)
  ·
    refine ⟨4838576086264384486175497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25805739126743383926269317 4838576086264384486175497)
    ·
      refine ⟨3628932064698288364631623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4838576086264384486175497 3628932064698288364631623)
      ·
        refine ⟨5443398097047432546947435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3628932064698288364631623 5443398097047432546947435)
        ·
          refine ⟨8165097145571148820421153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5443398097047432546947435 8165097145571148820421153)
          ·
            refine ⟨6123822859178361615315865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8165097145571148820421153 6123822859178361615315865)
            ·
              refine ⟨4592867144383771211486899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6123822859178361615315865 4592867144383771211486899)
              ·
                refine ⟨6889300716575656817230349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4592867144383771211486899 6889300716575656817230349)
                ·
                  refine ⟨2583487768715871306461381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6889300716575656817230349 2583487768715871306461381)
                  ·
                    refine ⟨484403956634225869961509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2583487768715871306461381 484403956634225869961509)
                    ·
                      rfl

theorem cell22_1415060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_1415060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415060 prefixEnd_1415060 := by exact prefixLift 1415060
  have htrace : WordTrace (prefixWord ++ tailWord_1415060) baseStart_1415060 baseEnd_1415060 := by
    simpa [prefixWord, tailWord_1415060, baseEnd_1415060] using wordTrace_append hprefix tailTrace_1415060
  have hstable : (prefixWord ++ tailWord_1415060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415060).length < 2 ^ (prefixWord ++ tailWord_1415060).sum := by decide
  have hdescent : baseEnd_1415060 < baseStart_1415060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415118 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_1415118 : Nat := 118140960795 + 1415118 * 2 ^ 59
def prefixEnd_1415118 : Nat := 4983230072969 + 3 ^ 40 * 1415118 * 2
def baseEnd_1415118 : Nat := 484423811219533052011331

theorem tailTrace_1415118 : CollatzResearch.WordTrace tailWord_1415118 prefixEnd_1415118 484423811219533052011331 := by
  unfold tailWord_1415118
  simp only [CollatzResearch.WordTrace]
  refine ⟨6451699210909580469768751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34409062458184429172100005 6451699210909580469768751)
  ·
    refine ⟨9677548816364370704653127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6451699210909580469768751 9677548816364370704653127)
    ·
      refine ⟨14516323224546556056979691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9677548816364370704653127 14516323224546556056979691)
      ·
        refine ⟨21774484836819834085469537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14516323224546556056979691 21774484836819834085469537)
        ·
          refine ⟨16330863627614875564102153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21774484836819834085469537 16330863627614875564102153)
          ·
            refine ⟨12248147720711156673076615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16330863627614875564102153 12248147720711156673076615)
            ·
              refine ⟨18372221581066735009614923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12248147720711156673076615 18372221581066735009614923)
              ·
                refine ⟨27558332371600102514422385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18372221581066735009614923 27558332371600102514422385)
                ·
                  refine ⟨20668749278700076885816789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27558332371600102514422385 20668749278700076885816789)
                  ·
                    refine ⟨484423811219533052011331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20668749278700076885816789 484423811219533052011331)
                    ·
                      rfl

theorem cell22_1415118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_1415118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415118 prefixEnd_1415118 := by exact prefixLift 1415118
  have htrace : WordTrace (prefixWord ++ tailWord_1415118) baseStart_1415118 baseEnd_1415118 := by
    simpa [prefixWord, tailWord_1415118, baseEnd_1415118] using wordTrace_append hprefix tailTrace_1415118
  have hstable : (prefixWord ++ tailWord_1415118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415118).length < 2 ^ (prefixWord ++ tailWord_1415118).sum := by decide
  have hdescent : baseEnd_1415118 < baseStart_1415118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415126 : List Nat := [5, 2, 1, 1, 3, 2, 1, 3, 4]
def baseStart_1415126 : Nat := 118140960795 + 1415126 * 2 ^ 59
def prefixEnd_1415126 : Nat := 4983230072969 + 3 ^ 40 * 1415126 * 2
def baseEnd_1415126 : Nat := 161475516594341232603769

theorem tailTrace_1415126 : CollatzResearch.WordTrace tailWord_1415126 prefixEnd_1415126 161475516594341232603769 := by
  unfold tailWord_1415126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3225867841952978820277577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34409256980831774082960821 3225867841952978820277577)
  ·
    refine ⟨2419400881464734115208183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3225867841952978820277577 2419400881464734115208183)
    ·
      refine ⟨3629101322197101172812275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2419400881464734115208183 3629101322197101172812275)
      ·
        refine ⟨5443651983295651759218413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3629101322197101172812275 5443651983295651759218413)
        ·
          refine ⟨2041369493735869409706905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5443651983295651759218413 2041369493735869409706905)
          ·
            refine ⟨1531027120301902057280179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2041369493735869409706905 1531027120301902057280179)
            ·
              refine ⟨2296540680452853085920269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1531027120301902057280179 2296540680452853085920269)
              ·
                refine ⟨861202755169819907220101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2296540680452853085920269 861202755169819907220101)
                ·
                  refine ⟨161475516594341232603769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 861202755169819907220101 161475516594341232603769)
                  ·
                    rfl

theorem cell22_1415126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_1415126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415126 prefixEnd_1415126 := by exact prefixLift 1415126
  have htrace : WordTrace (prefixWord ++ tailWord_1415126) baseStart_1415126 baseEnd_1415126 := by
    simpa [prefixWord, tailWord_1415126, baseEnd_1415126] using wordTrace_append hprefix tailTrace_1415126
  have hstable : (prefixWord ++ tailWord_1415126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415126).length < 2 ^ (prefixWord ++ tailWord_1415126).sum := by decide
  have hdescent : baseEnd_1415126 < baseStart_1415126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415152 : List Nat := [2, 1, 1, 1, 3, 2, 2, 6, 1, 3]
def baseStart_1415152 : Nat := 118140960795 + 1415152 * 2 ^ 59
def prefixEnd_1415152 : Nat := 4983230072969 + 3 ^ 40 * 1415152 * 2
def baseEnd_1415152 : Nat := 484435450114368296661227

theorem tailTrace_1415152 : CollatzResearch.WordTrace tailWord_1415152 prefixEnd_1415152 484435450114368296661227 := by
  unfold tailWord_1415152
  simp only [CollatzResearch.WordTrace]
  refine ⟨25807416884576733782443855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34409889179435645043258473 25807416884576733782443855)
  ·
    refine ⟨38711125326865100673665783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25807416884576733782443855 38711125326865100673665783)
    ·
      refine ⟨58066687990297651010498675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38711125326865100673665783 58066687990297651010498675)
      ·
        refine ⟨87100031985446476515748013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58066687990297651010498675 87100031985446476515748013)
        ·
          refine ⟨32662511994542428693405505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87100031985446476515748013 32662511994542428693405505)
          ·
            refine ⟨24496883995906821520054129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32662511994542428693405505 24496883995906821520054129)
            ·
              refine ⟨18372662996930116140040597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24496883995906821520054129 18372662996930116140040597)
              ·
                refine ⟨861218577981099194064403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18372662996930116140040597 861218577981099194064403)
                ·
                  refine ⟨1291827866971648791096605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 861218577981099194064403 1291827866971648791096605)
                  ·
                    refine ⟨484435450114368296661227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1291827866971648791096605 484435450114368296661227)
                    ·
                      rfl

theorem cell22_1415152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6, 1, 3].length) (baseStart_1415152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415152 prefixEnd_1415152 := by exact prefixLift 1415152
  have htrace : WordTrace (prefixWord ++ tailWord_1415152) baseStart_1415152 baseEnd_1415152 := by
    simpa [prefixWord, tailWord_1415152, baseEnd_1415152] using wordTrace_append hprefix tailTrace_1415152
  have hstable : (prefixWord ++ tailWord_1415152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415152).length < 2 ^ (prefixWord ++ tailWord_1415152).sum := by decide
  have hdescent : baseEnd_1415152 < baseStart_1415152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415158 : List Nat := [5, 1, 1, 1, 5, 1, 2, 1, 2, 3]
def baseStart_1415158 : Nat := 118140960795 + 1415158 * 2 ^ 59
def prefixEnd_1415158 : Nat := 4983230072969 + 3 ^ 40 * 1415158 * 2
def baseEnd_1415158 : Nat := 484437504036986281011209

theorem tailTrace_1415158 : CollatzResearch.WordTrace tailWord_1415158 prefixEnd_1415158 484437504036986281011209 := by
  unfold tailWord_1415158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3225940787945733161850383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34410035071421153726404085 3225940787945733161850383)
  ·
    refine ⟨4838911181918599742775575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3225940787945733161850383 4838911181918599742775575)
    ·
      refine ⟨7258366772877899614163363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4838911181918599742775575 7258366772877899614163363)
      ·
        refine ⟨10887550159316849421245045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7258366772877899614163363 10887550159316849421245045)
        ·
          refine ⟨1020707827435954633241723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10887550159316849421245045 1020707827435954633241723)
          ·
            refine ⟨1531061741153931949862585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1020707827435954633241723 1531061741153931949862585)
            ·
              refine ⟨1148296305865448962396939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1531061741153931949862585 1148296305865448962396939)
              ·
                refine ⟨1722444458798173443595409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1148296305865448962396939 1722444458798173443595409)
                ·
                  refine ⟨1291833344098630082696557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1722444458798173443595409 1291833344098630082696557)
                  ·
                    refine ⟨484437504036986281011209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1291833344098630082696557 484437504036986281011209)
                    ·
                      rfl

theorem cell22_1415158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_1415158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415158 prefixEnd_1415158 := by exact prefixLift 1415158
  have htrace : WordTrace (prefixWord ++ tailWord_1415158) baseStart_1415158 baseEnd_1415158 := by
    simpa [prefixWord, tailWord_1415158, baseEnd_1415158] using wordTrace_append hprefix tailTrace_1415158
  have hstable : (prefixWord ++ tailWord_1415158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415158).length < 2 ^ (prefixWord ++ tailWord_1415158).sum := by decide
  have hdescent : baseEnd_1415158 < baseStart_1415158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415163 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 2, 5]
def baseStart_1415163 : Nat := 118140960795 + 1415163 * 2 ^ 59
def prefixEnd_1415163 : Nat := 4983230072969 + 3 ^ 40 * 1415163 * 2
def baseEnd_1415163 : Nat := 484439215639167934636193

theorem tailTrace_1415163 : CollatzResearch.WordTrace tailWord_1415163 prefixEnd_1415163 484439215639167934636193 := by
  unfold tailWord_1415163
  simp only [CollatzResearch.WordTrace]
  refine ⟨51615234972113616443538143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34410156648075744295692095 51615234972113616443538143)
  ·
    refine ⟨77422852458170424665307215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51615234972113616443538143 77422852458170424665307215)
    ·
      refine ⟨116134278687255636997960823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77422852458170424665307215 116134278687255636997960823)
      ·
        refine ⟨174201418030883455496941235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116134278687255636997960823 174201418030883455496941235)
        ·
          refine ⟨261302127046325183245411853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174201418030883455496941235 261302127046325183245411853)
          ·
            refine ⟨97988297642371943717029445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261302127046325183245411853 97988297642371943717029445)
            ·
              refine ⟨18372805807944739446943021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97988297642371943717029445 18372805807944739446943021)
              ·
                refine ⟨6889802177979277292603633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18372805807944739446943021 6889802177979277292603633)
                ·
                  refine ⟨5167351633484457969452725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6889802177979277292603633 5167351633484457969452725)
                  ·
                    refine ⟨484439215639167934636193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5167351633484457969452725 484439215639167934636193)
                    ·
                      rfl

theorem cell22_1415163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 5].length) (baseStart_1415163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415163 prefixEnd_1415163 := by exact prefixLift 1415163
  have htrace : WordTrace (prefixWord ++ tailWord_1415163) baseStart_1415163 baseEnd_1415163 := by
    simpa [prefixWord, tailWord_1415163, baseEnd_1415163] using wordTrace_append hprefix tailTrace_1415163
  have hstable : (prefixWord ++ tailWord_1415163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415163).length < 2 ^ (prefixWord ++ tailWord_1415163).sum := by decide
  have hdescent : baseEnd_1415163 < baseStart_1415163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415240 : List Nat := [2, 1, 3, 1, 1, 1, 2, 5, 2, 4]
def baseStart_1415240 : Nat := 118140960795 + 1415240 * 2 ^ 59
def prefixEnd_1415240 : Nat := 4983230072969 + 3 ^ 40 * 1415240 * 2
def baseEnd_1415240 : Nat := 484465574312765400460957

theorem tailTrace_1415240 : CollatzResearch.WordTrace tailWord_1415240 prefixEnd_1415240 484465574312765400460957 := by
  unfold tailWord_1415240
  simp only [CollatzResearch.WordTrace]
  refine ⟨25809021696417329297045587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34412028928556439062727449 25809021696417329297045587)
  ·
    refine ⟨38713532544625993945568381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25809021696417329297045587 38713532544625993945568381)
    ·
      refine ⟨14517574704234747729588143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38713532544625993945568381 14517574704234747729588143)
      ·
        refine ⟨21776362056352121594382215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14517574704234747729588143 21776362056352121594382215)
        ·
          refine ⟨32664543084528182391573323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21776362056352121594382215 32664543084528182391573323)
          ·
            refine ⟨48996814626792273587359985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32664543084528182391573323 48996814626792273587359985)
            ·
              refine ⟨36747610970094205190519989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48996814626792273587359985 36747610970094205190519989)
              ·
                refine ⟨3445088528446331736611249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36747610970094205190519989 3445088528446331736611249)
                ·
                  refine ⟨2583816396334748802458437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3445088528446331736611249 2583816396334748802458437)
                  ·
                    refine ⟨484465574312765400460957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2583816396334748802458437 484465574312765400460957)
                    ·
                      rfl

theorem cell22_1415240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_1415240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415240 prefixEnd_1415240 := by exact prefixLift 1415240
  have htrace : WordTrace (prefixWord ++ tailWord_1415240) baseStart_1415240 baseEnd_1415240 := by
    simpa [prefixWord, tailWord_1415240, baseEnd_1415240] using wordTrace_append hprefix tailTrace_1415240
  have hstable : (prefixWord ++ tailWord_1415240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415240).length < 2 ^ (prefixWord ++ tailWord_1415240).sum := by decide
  have hdescent : baseEnd_1415240 < baseStart_1415240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415287 : List Nat := [1, 1, 3, 1, 1, 5, 2, 2, 3, 3]
def baseStart_1415287 : Nat := 118140960795 + 1415287 * 2 ^ 59
def prefixEnd_1415287 : Nat := 4983230072969 + 3 ^ 40 * 1415287 * 2
def baseEnd_1415287 : Nat := 484481663373272944535813

theorem tailTrace_1415287 : CollatzResearch.WordTrace tailWord_1415287 prefixEnd_1415287 484481663373272944535813 := by
  unfold tailWord_1415287
  simp only [CollatzResearch.WordTrace]
  refine ⟨51619757623664385621052115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34413171749109590414034743 51619757623664385621052115)
  ·
    refine ⟨77429636435496578431578173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51619757623664385621052115 77429636435496578431578173)
    ·
      refine ⟨29036113663311216911841815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77429636435496578431578173 29036113663311216911841815)
      ·
        refine ⟨43554170494966825367762723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29036113663311216911841815 43554170494966825367762723)
        ·
          refine ⟨65331255742450238051644085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43554170494966825367762723 65331255742450238051644085)
          ·
            refine ⟨6124805225854709817341633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65331255742450238051644085 6124805225854709817341633)
            ·
              refine ⟨4593603919391032363006225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6124805225854709817341633 4593603919391032363006225)
              ·
                refine ⟨3445202939543274272254669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4593603919391032363006225 3445202939543274272254669)
                ·
                  refine ⟨1291951102328727852095501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3445202939543274272254669 1291951102328727852095501)
                  ·
                    refine ⟨484481663373272944535813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1291951102328727852095501 484481663373272944535813)
                    ·
                      rfl

theorem cell22_1415287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 3].length) (baseStart_1415287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415287 prefixEnd_1415287 := by exact prefixLift 1415287
  have htrace : WordTrace (prefixWord ++ tailWord_1415287) baseStart_1415287 baseEnd_1415287 := by
    simpa [prefixWord, tailWord_1415287, baseEnd_1415287] using wordTrace_append hprefix tailTrace_1415287
  have hstable : (prefixWord ++ tailWord_1415287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415287).length < 2 ^ (prefixWord ++ tailWord_1415287).sum := by decide
  have hdescent : baseEnd_1415287 < baseStart_1415287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415300 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 9]
def baseStart_1415300 : Nat := 118140960795 + 1415300 * 2 ^ 59
def prefixEnd_1415300 : Nat := 4983230072969 + 3 ^ 40 * 1415300 * 2
def baseEnd_1415300 : Nat := 161495371179648414653591

theorem tailTrace_1415300 : CollatzResearch.WordTrace tailWord_1415300 prefixEnd_1415300 161495371179648414653591 := by
  unfold tailWord_1415300
  simp only [CollatzResearch.WordTrace]
  refine ⟨25810115886308644420637677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34413487848411525894183569 25810115886308644420637677)
  ·
    refine ⟨9678793457365741657739129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25810115886308644420637677 9678793457365741657739129)
    ·
      refine ⟨7259095093024306243304347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9678793457365741657739129 7259095093024306243304347)
      ·
        refine ⟨10888642639536459364956521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7259095093024306243304347 10888642639536459364956521)
        ·
          refine ⟨8166481979652344523717391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10888642639536459364956521 8166481979652344523717391)
          ·
            refine ⟨12249722969478516785576087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8166481979652344523717391 12249722969478516785576087)
            ·
              refine ⟨18374584454217775178364131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12249722969478516785576087 18374584454217775178364131)
              ·
                refine ⟨27561876681326662767546197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18374584454217775178364131 27561876681326662767546197)
                ·
                  refine ⟨161495371179648414653591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27561876681326662767546197 161495371179648414653591)
                  ·
                    rfl

theorem cell22_1415300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_1415300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415300 prefixEnd_1415300 := by exact prefixLift 1415300
  have htrace : WordTrace (prefixWord ++ tailWord_1415300) baseStart_1415300 baseEnd_1415300 := by
    simpa [prefixWord, tailWord_1415300, baseEnd_1415300] using wordTrace_append hprefix tailTrace_1415300
  have hstable : (prefixWord ++ tailWord_1415300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415300).length < 2 ^ (prefixWord ++ tailWord_1415300).sum := by decide
  have hdescent : baseEnd_1415300 < baseStart_1415300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415372 : List Nat := [2, 2, 1, 6, 2, 1, 2, 2, 1, 3]
def baseStart_1415372 : Nat := 118140960795 + 1415372 * 2 ^ 59
def prefixEnd_1415372 : Nat := 4983230072969 + 3 ^ 40 * 1415372 * 2
def baseEnd_1415372 : Nat := 484510760610361056160553

theorem tailTrace_1415372 : CollatzResearch.WordTrace tailWord_1415372 prefixEnd_1415372 484510760610361056160553 := by
  unfold tailWord_1415372
  simp only [CollatzResearch.WordTrace]
  refine ⟨25811428914178222568948185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34415238552237630091930913 25811428914178222568948185)
  ·
    refine ⟨19358571685633666926711139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25811428914178222568948185 19358571685633666926711139)
    ·
      refine ⟨29037857528450500390066709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19358571685633666926711139 29037857528450500390066709)
      ·
        refine ⟨1361149571646117205784377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29037857528450500390066709 1361149571646117205784377)
        ·
          refine ⟨1020862178734587904338283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1361149571646117205784377 1020862178734587904338283)
          ·
            refine ⟨1531293268101881856507425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1020862178734587904338283 1531293268101881856507425)
            ·
              refine ⟨1148469951076411392380569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1531293268101881856507425 1148469951076411392380569)
              ·
                refine ⟨861352463307308544285427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1148469951076411392380569 861352463307308544285427)
                ·
                  refine ⟨1292028694960962816428141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 861352463307308544285427 1292028694960962816428141)
                  ·
                    refine ⟨484510760610361056160553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1292028694960962816428141 484510760610361056160553)
                    ·
                      rfl

theorem cell22_1415372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 1, 3].length) (baseStart_1415372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415372 prefixEnd_1415372 := by exact prefixLift 1415372
  have htrace : WordTrace (prefixWord ++ tailWord_1415372) baseStart_1415372 baseEnd_1415372 := by
    simpa [prefixWord, tailWord_1415372, baseEnd_1415372] using wordTrace_append hprefix tailTrace_1415372
  have hstable : (prefixWord ++ tailWord_1415372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415372).length < 2 ^ (prefixWord ++ tailWord_1415372).sum := by decide
  have hdescent : baseEnd_1415372 < baseStart_1415372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415377 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 4, 3]
def baseStart_1415377 : Nat := 118140960795 + 1415377 * 2 ^ 59
def prefixEnd_1415377 : Nat := 4983230072969 + 3 ^ 40 * 1415377 * 2
def baseEnd_1415377 : Nat := 484512472212542709785537

theorem tailTrace_1415377 : CollatzResearch.WordTrace tailWord_1415377 prefixEnd_1415377 484512472212542709785537 := by
  unfold tailWord_1415377
  simp only [CollatzResearch.WordTrace]
  refine ⟨51623040193338330991828385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34415360128892220661218923 51623040193338330991828385)
  ·
    refine ⟨38717280145003748243871289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51623040193338330991828385 38717280145003748243871289)
    ·
      refine ⟨29037960108752811182903467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38717280145003748243871289 29037960108752811182903467)
      ·
        refine ⟨43556940163129216774355201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29037960108752811182903467 43556940163129216774355201)
        ·
          refine ⟨32667705122346912580766401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43556940163129216774355201 32667705122346912580766401)
          ·
            refine ⟨24500778841760184435574801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32667705122346912580766401 24500778841760184435574801)
            ·
              refine ⟨18375584131320138326681101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24500778841760184435574801 18375584131320138326681101)
              ·
                refine ⟨6890844049245051872505413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18375584131320138326681101 6890844049245051872505413)
                ·
                  refine ⟨1292033259233447226094765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6890844049245051872505413 1292033259233447226094765)
                  ·
                    refine ⟨484512472212542709785537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1292033259233447226094765 484512472212542709785537)
                    ·
                      rfl

theorem cell22_1415377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 3].length) (baseStart_1415377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415377 prefixEnd_1415377 := by exact prefixLift 1415377
  have htrace : WordTrace (prefixWord ++ tailWord_1415377) baseStart_1415377 baseEnd_1415377 := by
    simpa [prefixWord, tailWord_1415377, baseEnd_1415377] using wordTrace_append hprefix tailTrace_1415377
  have hstable : (prefixWord ++ tailWord_1415377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415377).length < 2 ^ (prefixWord ++ tailWord_1415377).sum := by decide
  have hdescent : baseEnd_1415377 < baseStart_1415377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415428 : List Nat := [2, 3, 2, 2, 3, 2, 1, 2, 2, 3]
def baseStart_1415428 : Nat := 118140960795 + 1415428 * 2 ^ 59
def prefixEnd_1415428 : Nat := 4983230072969 + 3 ^ 40 * 1415428 * 2
def baseEnd_1415428 : Nat := 484529930554795576760381

theorem tailTrace_1415428 : CollatzResearch.WordTrace tailWord_1415428 prefixEnd_1415428 484529930554795576760381 := by
  unfold tailWord_1415428
  simp only [CollatzResearch.WordTrace]
  refine ⟨25812450158076783350967469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34416600210769044467956625 25812450158076783350967469)
  ·
    refine ⟨9679668809278793756612801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25812450158076783350967469 9679668809278793756612801)
    ·
      refine ⟨7259751606959095317459601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9679668809278793756612801 7259751606959095317459601)
      ·
        refine ⟨5444813705219321488094701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7259751606959095317459601 5444813705219321488094701)
        ·
          refine ⟨2041805139457245558035513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5444813705219321488094701 2041805139457245558035513)
          ·
            refine ⟨1531353854592934168526635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2041805139457245558035513 1531353854592934168526635)
            ·
              refine ⟨2297030781889401252789953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1531353854592934168526635 2297030781889401252789953)
              ·
                refine ⟨1722773086417050939592465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2297030781889401252789953 1722773086417050939592465)
                ·
                  refine ⟨1292079814812788204694349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1722773086417050939592465 1292079814812788204694349)
                  ·
                    refine ⟨484529930554795576760381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1292079814812788204694349 484529930554795576760381)
                    ·
                      rfl

theorem cell22_1415428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_1415428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415428 prefixEnd_1415428 := by exact prefixLift 1415428
  have htrace : WordTrace (prefixWord ++ tailWord_1415428) baseStart_1415428 baseEnd_1415428 := by
    simpa [prefixWord, tailWord_1415428, baseEnd_1415428] using wordTrace_append hprefix tailTrace_1415428
  have hstable : (prefixWord ++ tailWord_1415428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415428).length < 2 ^ (prefixWord ++ tailWord_1415428).sum := by decide
  have hdescent : baseEnd_1415428 < baseStart_1415428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415557 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 2, 7]
def baseStart_1415557 : Nat := 118140960795 + 1415557 * 2 ^ 59
def prefixEnd_1415557 : Nat := 4983230072969 + 3 ^ 40 * 1415557 * 2
def baseEnd_1415557 : Nat := 484574089891082240284985

theorem tailTrace_1415557 : CollatzResearch.WordTrace tailWord_1415557 prefixEnd_1415557 484574089891082240284985 := by
  unfold tailWord_1415557
  simp only [CollatzResearch.WordTrace]
  refine ⟨51629605332686221733380925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34419736888457481155587283 51629605332686221733380925)
  ·
    refine ⟨19361101999757333150017847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51629605332686221733380925 19361101999757333150017847)
    ·
      refine ⟨29041652999635999725026771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19361101999757333150017847 29041652999635999725026771)
      ·
        refine ⟨43562479499453999587540157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29041652999635999725026771 43562479499453999587540157)
        ·
          refine ⟨16335929812295249845327559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43562479499453999587540157 16335929812295249845327559)
          ·
            refine ⟨24503894718442874767991339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16335929812295249845327559 24503894718442874767991339)
            ·
              refine ⟨36755842077664312151987009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24503894718442874767991339 36755842077664312151987009)
              ·
                refine ⟨27566881558248234113990257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36755842077664312151987009 27566881558248234113990257)
                ·
                  refine ⟨20675161168686175585492693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27566881558248234113990257 20675161168686175585492693)
                  ·
                    refine ⟨484574089891082240284985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20675161168686175585492693 484574089891082240284985)
                    ·
                      rfl

theorem cell22_1415557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_1415557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415557 prefixEnd_1415557 := by exact prefixLift 1415557
  have htrace : WordTrace (prefixWord ++ tailWord_1415557) baseStart_1415557 baseEnd_1415557 := by
    simpa [prefixWord, tailWord_1415557, baseEnd_1415557] using wordTrace_append hprefix tailTrace_1415557
  have hstable : (prefixWord ++ tailWord_1415557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415557).length < 2 ^ (prefixWord ++ tailWord_1415557).sum := by decide
  have hdescent : baseEnd_1415557 < baseStart_1415557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415576 : List Nat := [2, 1, 2, 5, 1, 2, 3, 6]
def baseStart_1415576 : Nat := 118140960795 + 1415576 * 2 ^ 59
def prefixEnd_1415576 : Nat := 4983230072969 + 3 ^ 40 * 1415576 * 2
def baseEnd_1415576 : Nat := 53842288219930280451103

theorem tailTrace_1415576 : CollatzResearch.WordTrace tailWord_1415576 prefixEnd_1415576 53842288219930280451103 := by
  unfold tailWord_1415576
  simp only [CollatzResearch.WordTrace]
  refine ⟨25815149159808693989161291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34420198879744925318881721 25815149159808693989161291)
  ·
    refine ⟨38722723739713040983741937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25815149159808693989161291 38722723739713040983741937)
    ·
      refine ⟨29042042804784780737806453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38722723739713040983741937 29042042804784780737806453)
      ·
        refine ⟨2722691512948573194169355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29042042804784780737806453 2722691512948573194169355)
        ·
          refine ⟨4084037269422859791254033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2722691512948573194169355 4084037269422859791254033)
          ·
            refine ⟨3063027952067144843440525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4084037269422859791254033 3063027952067144843440525)
            ·
              refine ⟨1148635482025179316290197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3063027952067144843440525 1148635482025179316290197)
              ·
                refine ⟨53842288219930280451103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1148635482025179316290197 53842288219930280451103)
                ·
                  rfl

theorem cell22_1415576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 6].length) (baseStart_1415576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415576 prefixEnd_1415576 := by exact prefixLift 1415576
  have htrace : WordTrace (prefixWord ++ tailWord_1415576) baseStart_1415576 baseEnd_1415576 := by
    simpa [prefixWord, tailWord_1415576, baseEnd_1415576] using wordTrace_append hprefix tailTrace_1415576
  have hstable : (prefixWord ++ tailWord_1415576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415576).length < 2 ^ (prefixWord ++ tailWord_1415576).sum := by decide
  have hdescent : baseEnd_1415576 < baseStart_1415576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415597 : List Nat := [1, 5, 2, 2, 3, 1, 1, 2, 2, 3]
def baseStart_1415597 : Nat := 118140960795 + 1415597 * 2 ^ 59
def prefixEnd_1415597 : Nat := 4983230072969 + 3 ^ 40 * 1415597 * 2
def baseEnd_1415597 : Nat := 484587782708535469284863

theorem tailTrace_1415597 : CollatzResearch.WordTrace tailWord_1415597 prefixEnd_1415597 484587782708535469284863 := by
  unfold tailWord_1415597
  simp only [CollatzResearch.WordTrace]
  refine ⟨51631064252541308564837045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34420709501694205709891363 51631064252541308564837045)
  ·
    refine ⟨4840412273675747677953473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51631064252541308564837045 4840412273675747677953473)
    ·
      refine ⟨3630309205256810758465105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4840412273675747677953473 3630309205256810758465105)
      ·
        refine ⟨2722731903942608068848829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3630309205256810758465105 2722731903942608068848829)
        ·
          refine ⟨1021024463978478025818311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2722731903942608068848829 1021024463978478025818311)
          ·
            refine ⟨1531536695967717038727467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021024463978478025818311 1531536695967717038727467)
            ·
              refine ⟨2297305043951575558091201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1531536695967717038727467 2297305043951575558091201)
              ·
                refine ⟨1722978782963681668568401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2297305043951575558091201 1722978782963681668568401)
                ·
                  refine ⟨1292234087222761251426301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1722978782963681668568401 1292234087222761251426301)
                  ·
                    refine ⟨484587782708535469284863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1292234087222761251426301 484587782708535469284863)
                    ·
                      rfl

theorem cell22_1415597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_1415597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415597 prefixEnd_1415597 := by exact prefixLift 1415597
  have htrace : WordTrace (prefixWord ++ tailWord_1415597) baseStart_1415597 baseEnd_1415597 := by
    simpa [prefixWord, tailWord_1415597, baseEnd_1415597] using wordTrace_append hprefix tailTrace_1415597
  have hstable : (prefixWord ++ tailWord_1415597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415597).length < 2 ^ (prefixWord ++ tailWord_1415597).sum := by decide
  have hdescent : baseEnd_1415597 < baseStart_1415597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415679 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 4, 4]
def baseStart_1415679 : Nat := 118140960795 + 1415679 * 2 ^ 59
def prefixEnd_1415679 : Nat := 4983230072969 + 3 ^ 40 * 1415679 * 2
def baseEnd_1415679 : Nat := 484615852984314588734611

theorem tailTrace_1415679 : CollatzResearch.WordTrace tailWord_1415679 prefixEnd_1415679 484615852984314588734611 := by
  unfold tailWord_1415679
  simp only [CollatzResearch.WordTrace]
  refine ⟨51634055038244236569322091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34422703358829491046214727 51634055038244236569322091)
  ·
    refine ⟨77451082557366354853983137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51634055038244236569322091 77451082557366354853983137)
    ·
      refine ⟨58088311918024766140487353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77451082557366354853983137 58088311918024766140487353)
      ·
        refine ⟨43566233938518574605365515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58088311918024766140487353 43566233938518574605365515)
        ·
          refine ⟨65349350907777861908048273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43566233938518574605365515 65349350907777861908048273)
          ·
            refine ⟨49012013180833396431036205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65349350907777861908048273 49012013180833396431036205)
            ·
              refine ⟨18379504942812523661638577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49012013180833396431036205 18379504942812523661638577)
              ·
                refine ⟨13784628707109392746228933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18379504942812523661638577 13784628707109392746228933)
                ·
                  refine ⟨2584617882583011139917925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13784628707109392746228933 2584617882583011139917925)
                  ·
                    refine ⟨484615852984314588734611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2584617882583011139917925 484615852984314588734611)
                    ·
                      rfl

theorem cell22_1415679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 4].length) (baseStart_1415679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415679 prefixEnd_1415679 := by exact prefixLift 1415679
  have htrace : WordTrace (prefixWord ++ tailWord_1415679) baseStart_1415679 baseEnd_1415679 := by
    simpa [prefixWord, tailWord_1415679, baseEnd_1415679] using wordTrace_append hprefix tailTrace_1415679
  have hstable : (prefixWord ++ tailWord_1415679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415679).length < 2 ^ (prefixWord ++ tailWord_1415679).sum := by decide
  have hdescent : baseEnd_1415679 < baseStart_1415679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415790 : List Nat := [4, 1, 2, 2, 2, 2, 3, 1, 5]
def baseStart_1415790 : Nat := 118140960795 + 1415790 * 2 ^ 59
def prefixEnd_1415790 : Nat := 4983230072969 + 3 ^ 40 * 1415790 * 2
def baseEnd_1415790 : Nat := 161551283517582433069757

theorem tailTrace_1415790 : CollatzResearch.WordTrace tailWord_1415790 prefixEnd_1415790 161551283517582433069757 := by
  unfold tailWord_1415790
  simp only [CollatzResearch.WordTrace]
  refine ⟨6454762942605262815826603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34425402360561401684408549 6454762942605262815826603)
  ·
    refine ⟨9682144413907894223739905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6454762942605262815826603 9682144413907894223739905)
    ·
      refine ⟨7261608310430920667804929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9682144413907894223739905 7261608310430920667804929)
      ·
        refine ⟨5446206232823190500853697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7261608310430920667804929 5446206232823190500853697)
        ·
          refine ⟨4084654674617392875640273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5446206232823190500853697 4084654674617392875640273)
          ·
            refine ⟨3063491005963044656730205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4084654674617392875640273 3063491005963044656730205)
            ·
              refine ⟨1148809127236141746273827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3063491005963044656730205 1148809127236141746273827)
              ·
                refine ⟨1723213690854212619410741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1148809127236141746273827 1723213690854212619410741)
                ·
                  refine ⟨161551283517582433069757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1723213690854212619410741 161551283517582433069757)
                  ·
                    rfl

theorem cell22_1415790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_1415790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415790 prefixEnd_1415790 := by exact prefixLift 1415790
  have htrace : WordTrace (prefixWord ++ tailWord_1415790) baseStart_1415790 baseEnd_1415790 := by
    simpa [prefixWord, tailWord_1415790, baseEnd_1415790] using wordTrace_append hprefix tailTrace_1415790
  have hstable : (prefixWord ++ tailWord_1415790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415790).length < 2 ^ (prefixWord ++ tailWord_1415790).sum := by decide
  have hdescent : baseEnd_1415790 < baseStart_1415790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415801 : List Nat := [1, 2, 1, 3, 3, 2, 2, 2, 6]
def baseStart_1415801 : Nat := 118140960795 + 1415801 * 2 ^ 59
def prefixEnd_1415801 : Nat := 4983230072969 + 3 ^ 40 * 1415801 * 2
def baseEnd_1415801 : Nat := 161552538692515645728079

theorem tailTrace_1415801 : CollatzResearch.WordTrace tailWord_1415801 prefixEnd_1415801 161552538692515645728079 := by
  unfold tailWord_1415801
  simp only [CollatzResearch.WordTrace]
  refine ⟨51638504743802251405263257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34425669829201500936842171 51638504743802251405263257)
  ·
    refine ⟨38728878557851688553947443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51638504743802251405263257 38728878557851688553947443)
    ·
      refine ⟨58093317836777532830921165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38728878557851688553947443 58093317836777532830921165)
      ·
        refine ⟨21784994188791574811595437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58093317836777532830921165 21784994188791574811595437)
        ·
          refine ⟨8169372820796840554348289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21784994188791574811595437 8169372820796840554348289)
          ·
            refine ⟨6127029615597630415761217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8169372820796840554348289 6127029615597630415761217)
            ·
              refine ⟨4595272211698222811820913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6127029615597630415761217 4595272211698222811820913)
              ·
                refine ⟨3446454158773667108865685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4595272211698222811820913 3446454158773667108865685)
                ·
                  refine ⟨161552538692515645728079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3446454158773667108865685 161552538692515645728079)
                  ·
                    rfl

theorem cell22_1415801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 6].length) (baseStart_1415801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415801 prefixEnd_1415801 := by exact prefixLift 1415801
  have htrace : WordTrace (prefixWord ++ tailWord_1415801) baseStart_1415801 baseEnd_1415801 := by
    simpa [prefixWord, tailWord_1415801, baseEnd_1415801] using wordTrace_append hprefix tailTrace_1415801
  have hstable : (prefixWord ++ tailWord_1415801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415801).length < 2 ^ (prefixWord ++ tailWord_1415801).sum := by decide
  have hdescent : baseEnd_1415801 < baseStart_1415801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415833 : List Nat := [1, 2, 1, 2, 1, 2, 4, 4, 2, 3]
def baseStart_1415833 : Nat := 118140960795 + 1415833 * 2 ^ 59
def prefixEnd_1415833 : Nat := 4983230072969 + 3 ^ 40 * 1415833 * 2
def baseEnd_1415833 : Nat := 484668570331509520384139

theorem tailTrace_1415833 : CollatzResearch.WordTrace tailWord_1415833 prefixEnd_1415833 484668570331509520384139 := by
  unfold tailWord_1415833
  simp only [CollatzResearch.WordTrace]
  refine ⟨51639671879686320870428153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34426447919790880580285435 51639671879686320870428153)
  ·
    refine ⟨38729753909764740652821115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51639671879686320870428153 38729753909764740652821115)
    ·
      refine ⟨58094630864647110979231673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38729753909764740652821115 58094630864647110979231673)
      ·
        refine ⟨43570973148485333234423755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58094630864647110979231673 43570973148485333234423755)
        ·
          refine ⟨65356459722727999851635633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43570973148485333234423755 65356459722727999851635633)
          ·
            refine ⟨49017344792045999888726725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65356459722727999851635633 49017344792045999888726725)
            ·
              refine ⟨9190752148508624979136261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49017344792045999888726725 9190752148508624979136261)
              ·
                refine ⟨1723266027845367183588049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9190752148508624979136261 1723266027845367183588049)
                ·
                  refine ⟨1292449520884025387691037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1723266027845367183588049 1292449520884025387691037)
                  ·
                    refine ⟨484668570331509520384139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1292449520884025387691037 484668570331509520384139)
                    ·
                      rfl

theorem cell22_1415833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 3].length) (baseStart_1415833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415833 prefixEnd_1415833 := by exact prefixLift 1415833
  have htrace : WordTrace (prefixWord ++ tailWord_1415833) baseStart_1415833 baseEnd_1415833 := by
    simpa [prefixWord, tailWord_1415833, baseEnd_1415833] using wordTrace_append hprefix tailTrace_1415833
  have hstable : (prefixWord ++ tailWord_1415833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415833).length < 2 ^ (prefixWord ++ tailWord_1415833).sum := by decide
  have hdescent : baseEnd_1415833 < baseStart_1415833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415908 : List Nat := [2, 3, 1, 1, 1, 4, 2, 3, 5]
def baseStart_1415908 : Nat := 118140960795 + 1415908 * 2 ^ 59
def prefixEnd_1415908 : Nat := 4983230072969 + 3 ^ 40 * 1415908 * 2
def baseEnd_1415908 : Nat := 161564748121411441586303

theorem tailTrace_1415908 : CollatzResearch.WordTrace tailWord_1415908 prefixEnd_1415908 161564748121411441586303 := by
  unfold tailWord_1415908
  simp only [CollatzResearch.WordTrace]
  refine ⟨25821203677207304339704189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34428271569609739119605585 25821203677207304339704189)
  ·
    refine ⟨9682951378952739127389071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25821203677207304339704189 9682951378952739127389071)
    ·
      refine ⟨14524427068429108691083607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9682951378952739127389071 14524427068429108691083607)
      ·
        refine ⟨21786640602643663036625411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14524427068429108691083607 21786640602643663036625411)
        ·
          refine ⟨32679960903965494554938117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21786640602643663036625411 32679960903965494554938117)
          ·
            refine ⟨6127492669493530229050897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32679960903965494554938117 6127492669493530229050897)
            ·
              refine ⟨4595619502120147671788173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6127492669493530229050897 4595619502120147671788173)
              ·
                refine ⟨1723357313295055376920565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4595619502120147671788173 1723357313295055376920565)
                ·
                  refine ⟨161564748121411441586303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1723357313295055376920565 161564748121411441586303)
                  ·
                    rfl

theorem cell22_1415908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_1415908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415908 prefixEnd_1415908 := by exact prefixLift 1415908
  have htrace : WordTrace (prefixWord ++ tailWord_1415908) baseStart_1415908 baseEnd_1415908 := by
    simpa [prefixWord, tailWord_1415908, baseEnd_1415908] using wordTrace_append hprefix tailTrace_1415908
  have hstable : (prefixWord ++ tailWord_1415908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415908).length < 2 ^ (prefixWord ++ tailWord_1415908).sum := by decide
  have hdescent : baseEnd_1415908 < baseStart_1415908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415972 : List Nat := [2, 3, 1, 3, 3, 1, 2, 2, 1, 4]
def baseStart_1415972 : Nat := 118140960795 + 1415972 * 2 ^ 59
def prefixEnd_1415972 : Nat := 4983230072969 + 3 ^ 40 * 1415972 * 2
def baseEnd_1415972 : Nat := 484716152872159491158713

theorem tailTrace_1415972 : CollatzResearch.WordTrace tailWord_1415972 prefixEnd_1415972 484716152872159491158713 := by
  unfold tailWord_1415972
  simp only [CollatzResearch.WordTrace]
  refine ⟨25822370813091373804869085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34429827750788498406492113 25822370813091373804869085)
  ·
    refine ⟨9683389054909265176825907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25822370813091373804869085 9683389054909265176825907)
    ·
      refine ⟨14525083582363897765238861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9683389054909265176825907 14525083582363897765238861)
      ·
        refine ⟨5446906343386461661964573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14525083582363897765238861 5446906343386461661964573)
        ·
          refine ⟨2042589878769923123236715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5446906343386461661964573 2042589878769923123236715)
          ·
            refine ⟨3063884818154884684855073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2042589878769923123236715 3063884818154884684855073)
            ·
              refine ⟨2297913613616163513641305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3063884818154884684855073 2297913613616163513641305)
              ·
                refine ⟨1723435210212122635230979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2297913613616163513641305 1723435210212122635230979)
                ·
                  refine ⟨2585152815318183952846469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1723435210212122635230979 2585152815318183952846469)
                  ·
                    refine ⟨484716152872159491158713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2585152815318183952846469 484716152872159491158713)
                    ·
                      rfl

theorem cell22_1415972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_1415972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415972 prefixEnd_1415972 := by exact prefixLift 1415972
  have htrace : WordTrace (prefixWord ++ tailWord_1415972) baseStart_1415972 baseEnd_1415972 := by
    simpa [prefixWord, tailWord_1415972, baseEnd_1415972] using wordTrace_append hprefix tailTrace_1415972
  have hstable : (prefixWord ++ tailWord_1415972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415972).length < 2 ^ (prefixWord ++ tailWord_1415972).sum := by decide
  have hdescent : baseEnd_1415972 < baseStart_1415972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415987 : List Nat := [1, 1, 1, 2, 6, 3, 1, 3, 4]
def baseStart_1415987 : Nat := 118140960795 + 1415987 * 2 ^ 59
def prefixEnd_1415987 : Nat := 4983230072969 + 3 ^ 40 * 1415987 * 2
def baseEnd_1415987 : Nat := 161573762559568150677889

theorem tailTrace_1415987 : CollatzResearch.WordTrace tailWord_1415987 prefixEnd_1415987 161573762559568150677889 := by
  unfold tailWord_1415987
  simp only [CollatzResearch.WordTrace]
  refine ⟨51645288721128405171534215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34430192480752270114356143 51645288721128405171534215)
  ·
    refine ⟨77467933081692607757301323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51645288721128405171534215 77467933081692607757301323)
    ·
      refine ⟨116201899622538911635951985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77467933081692607757301323 116201899622538911635951985)
      ·
        refine ⟨87151424716904183726963989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116201899622538911635951985 87151424716904183726963989)
        ·
          refine ⟨4085223033604883612201437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 87151424716904183726963989 4085223033604883612201437)
          ·
            refine ⟨1531958637601831354575539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4085223033604883612201437 1531958637601831354575539)
            ·
              refine ⟨2297937956402747031863309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1531958637601831354575539 2297937956402747031863309)
              ·
                refine ⟨861726733651030136948741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2297937956402747031863309 861726733651030136948741)
                ·
                  refine ⟨161573762559568150677889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 861726733651030136948741 161573762559568150677889)
                  ·
                    rfl

theorem cell22_1415987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 4].length) (baseStart_1415987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1415987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1415987 prefixEnd_1415987 := by exact prefixLift 1415987
  have htrace : WordTrace (prefixWord ++ tailWord_1415987) baseStart_1415987 baseEnd_1415987 := by
    simpa [prefixWord, tailWord_1415987, baseEnd_1415987] using wordTrace_append hprefix tailTrace_1415987
  have hstable : (prefixWord ++ tailWord_1415987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415987).length < 2 ^ (prefixWord ++ tailWord_1415987).sum := by decide
  have hdescent : baseEnd_1415987 < baseStart_1415987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416004 : List Nat := [2, 3, 4, 2, 1, 2, 1, 1, 6]
def baseStart_1416004 : Nat := 118140960795 + 1416004 * 2 ^ 59
def prefixEnd_1416004 : Nat := 4983230072969 + 3 ^ 40 * 1416004 * 2
def baseEnd_1416004 : Nat := 161575702375374024786205

theorem tailTrace_1416004 : CollatzResearch.WordTrace tailWord_1416004 prefixEnd_1416004 161575702375374024786205 := by
  unfold tailWord_1416004
  simp only [CollatzResearch.WordTrace]
  refine ⟨25822954381033408537451533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34430605841377878049935377 25822954381033408537451533)
  ·
    refine ⟨9683607892887528201544325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25822954381033408537451533 9683607892887528201544325)
    ·
      refine ⟨1815676479916411537789561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9683607892887528201544325 1815676479916411537789561)
      ·
        refine ⟨1361757359937308653342171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1815676479916411537789561 1361757359937308653342171)
        ·
          refine ⟨2042636039905962980013257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1361757359937308653342171 2042636039905962980013257)
          ·
            refine ⟨1531977029929472235009943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2042636039905962980013257 1531977029929472235009943)
            ·
              refine ⟨2297965544894208352514915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1531977029929472235009943 2297965544894208352514915)
              ·
                refine ⟨3446948317341312528772373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2297965544894208352514915 3446948317341312528772373)
                ·
                  refine ⟨161575702375374024786205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3446948317341312528772373 161575702375374024786205)
                  ·
                    rfl

theorem cell22_1416004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_1416004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416004 prefixEnd_1416004 := by exact prefixLift 1416004
  have htrace : WordTrace (prefixWord ++ tailWord_1416004) baseStart_1416004 baseEnd_1416004 := by
    simpa [prefixWord, tailWord_1416004, baseEnd_1416004] using wordTrace_append hprefix tailTrace_1416004
  have hstable : (prefixWord ++ tailWord_1416004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416004).length < 2 ^ (prefixWord ++ tailWord_1416004).sum := by decide
  have hdescent : baseEnd_1416004 < baseStart_1416004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416058 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 2, 5]
def baseStart_1416058 : Nat := 118140960795 + 1416058 * 2 ^ 59
def prefixEnd_1416058 : Nat := 4983230072969 + 3 ^ 40 * 1416058 * 2
def baseEnd_1416058 : Nat := 484745592429683933508449

theorem tailTrace_1416058 : CollatzResearch.WordTrace tailWord_1416058 prefixEnd_1416058 484745592429683933508449 := by
  unfold tailWord_1416058
  simp only [CollatzResearch.WordTrace]
  refine ⟨12911969575967796074342207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34431918869247456198245885 12911969575967796074342207)
  ·
    refine ⟨19367954363951694111513311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12911969575967796074342207 19367954363951694111513311)
    ·
      refine ⟨29051931545927541167269967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19367954363951694111513311 29051931545927541167269967)
      ·
        refine ⟨43577897318891311750904951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29051931545927541167269967 43577897318891311750904951)
        ·
          refine ⟨65366845978336967626357427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43577897318891311750904951 65366845978336967626357427)
          ·
            refine ⟨98050268967505451439536141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65366845978336967626357427 98050268967505451439536141)
            ·
              refine ⟨36768850862814544289826053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98050268967505451439536141 36768850862814544289826053)
              ·
                refine ⟨6894159536777727054342385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36768850862814544289826053 6894159536777727054342385)
                ·
                  refine ⟨5170619652583295290756789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6894159536777727054342385 5170619652583295290756789)
                  ·
                    refine ⟨484745592429683933508449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5170619652583295290756789 484745592429683933508449)
                    ·
                      rfl

theorem cell22_1416058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_1416058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416058 prefixEnd_1416058 := by exact prefixLift 1416058
  have htrace : WordTrace (prefixWord ++ tailWord_1416058) baseStart_1416058 baseEnd_1416058 := by
    simpa [prefixWord, tailWord_1416058, baseEnd_1416058] using wordTrace_append hprefix tailTrace_1416058
  have hstable : (prefixWord ++ tailWord_1416058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416058).length < 2 ^ (prefixWord ++ tailWord_1416058).sum := by decide
  have hdescent : baseEnd_1416058 < baseStart_1416058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416066 : List Nat := [3, 4, 2, 2, 2, 1, 1, 7]
def baseStart_1416066 : Nat := 118140960795 + 1416066 * 2 ^ 59
def prefixEnd_1416066 : Nat := 4983230072969 + 3 ^ 40 * 1416066 * 2
def baseEnd_1416066 : Nat := 53860925665908286589825

theorem tailTrace_1416066 : CollatzResearch.WordTrace tailWord_1416066 prefixEnd_1416066 53860925665908286589825 := by
  unfold tailWord_1416066
  simp only [CollatzResearch.WordTrace]
  refine ⟨12912042521960550415915013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34432113391894801109106701 12912042521960550415915013)
  ·
    refine ⟨2421007972867603202984065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12912042521960550415915013 2421007972867603202984065)
    ·
      refine ⟨1815755979650702402238049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2421007972867603202984065 1815755979650702402238049)
      ·
        refine ⟨1361816984738026801678537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1815755979650702402238049 1361816984738026801678537)
        ·
          refine ⟨1021362738553520101258903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1361816984738026801678537 1021362738553520101258903)
          ·
            refine ⟨1532044107830280151888355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021362738553520101258903 1532044107830280151888355)
            ·
              refine ⟨2298066161745420227832533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1532044107830280151888355 2298066161745420227832533)
              ·
                refine ⟨53860925665908286589825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2298066161745420227832533 53860925665908286589825)
                ·
                  rfl

theorem cell22_1416066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 7].length) (baseStart_1416066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416066 prefixEnd_1416066 := by exact prefixLift 1416066
  have htrace : WordTrace (prefixWord ++ tailWord_1416066) baseStart_1416066 baseEnd_1416066 := by
    simpa [prefixWord, tailWord_1416066, baseEnd_1416066] using wordTrace_append hprefix tailTrace_1416066
  have hstable : (prefixWord ++ tailWord_1416066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416066).length < 2 ^ (prefixWord ++ tailWord_1416066).sum := by decide
  have hdescent : baseEnd_1416066 < baseStart_1416066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416240 : List Nat := [2, 1, 1, 1, 2, 4, 2, 3, 6]
def baseStart_1416240 : Nat := 118140960795 + 1416240 * 2 ^ 59
def prefixEnd_1416240 : Nat := 4983230072969 + 3 ^ 40 * 1416240 * 2
def baseEnd_1416240 : Nat := 161602631583032041819297

theorem tailTrace_1416240 : CollatzResearch.WordTrace tailWord_1416240 prefixEnd_1416240 161602631583032041819297 := by
  unfold tailWord_1416240
  simp only [CollatzResearch.WordTrace]
  refine ⟨25827258194605914690247087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34436344259474552920329449 25827258194605914690247087)
  ·
    refine ⟨38740887291908872035370631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25827258194605914690247087 38740887291908872035370631)
    ·
      refine ⟨58111330937863308053055947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38740887291908872035370631 58111330937863308053055947)
      ·
        refine ⟨87166996406794962079583921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58111330937863308053055947 87166996406794962079583921)
        ·
          refine ⟨65375247305096221559687941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87166996406794962079583921 65375247305096221559687941)
          ·
            refine ⟨12257858869705541542441489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65375247305096221559687941 12257858869705541542441489)
            ·
              refine ⟨9193394152279156156831117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12257858869705541542441489 9193394152279156156831117)
              ·
                refine ⟨3447522807104683558811669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9193394152279156156831117 3447522807104683558811669)
                ·
                  refine ⟨161602631583032041819297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3447522807104683558811669 161602631583032041819297)
                  ·
                    rfl

theorem cell22_1416240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 6].length) (baseStart_1416240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416240 prefixEnd_1416240 := by exact prefixLift 1416240
  have htrace : WordTrace (prefixWord ++ tailWord_1416240) baseStart_1416240 baseEnd_1416240 := by
    simpa [prefixWord, tailWord_1416240, baseEnd_1416240] using wordTrace_append hprefix tailTrace_1416240
  have hstable : (prefixWord ++ tailWord_1416240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416240).length < 2 ^ (prefixWord ++ tailWord_1416240).sum := by decide
  have hdescent : baseEnd_1416240 < baseStart_1416240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416244 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_1416244 : Nat := 118140960795 + 1416244 * 2 ^ 59
def prefixEnd_1416244 : Nat := 4983230072969 + 3 ^ 40 * 1416244 * 2
def baseEnd_1416244 : Nat := 484809264030841448357879

theorem tailTrace_1416244 : CollatzResearch.WordTrace tailWord_1416244 prefixEnd_1416244 484809264030841448357879 := by
  unfold tailWord_1416244
  simp only [CollatzResearch.WordTrace]
  refine ⟨25827331140598669031819893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34436441520798225375759857 25827331140598669031819893)
  ·
    refine ⟨2421312294431125221733115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25827331140598669031819893 2421312294431125221733115)
    ·
      refine ⟨3631968441646687832599673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2421312294431125221733115 3631968441646687832599673)
      ·
        refine ⟨2723976331235015874449755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3631968441646687832599673 2723976331235015874449755)
        ·
          refine ⟨4085964496852523811674633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2723976331235015874449755 4085964496852523811674633)
          ·
            refine ⟨3064473372639392858755975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4085964496852523811674633 3064473372639392858755975)
            ·
              refine ⟨4596710058959089288133963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3064473372639392858755975 4596710058959089288133963)
              ·
                refine ⟨6895065088438633932200945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4596710058959089288133963 6895065088438633932200945)
                ·
                  refine ⟨5171298816328975449150709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6895065088438633932200945 5171298816328975449150709)
                  ·
                    refine ⟨484809264030841448357879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5171298816328975449150709 484809264030841448357879)
                    ·
                      rfl

theorem cell22_1416244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_1416244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416244 prefixEnd_1416244 := by exact prefixLift 1416244
  have htrace : WordTrace (prefixWord ++ tailWord_1416244) baseStart_1416244 baseEnd_1416244 := by
    simpa [prefixWord, tailWord_1416244, baseEnd_1416244] using wordTrace_append hprefix tailTrace_1416244
  have hstable : (prefixWord ++ tailWord_1416244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416244).length < 2 ^ (prefixWord ++ tailWord_1416244).sum := by decide
  have hdescent : baseEnd_1416244 < baseStart_1416244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416274 : List Nat := [3, 2, 2, 1, 3, 1, 1, 5, 4]
def baseStart_1416274 : Nat := 118140960795 + 1416274 * 2 ^ 59
def prefixEnd_1416274 : Nat := 4983230072969 + 3 ^ 40 * 1416274 * 2
def baseEnd_1416274 : Nat := 161606511214643790035929

theorem tailTrace_1416274 : CollatzResearch.WordTrace tailWord_1416274 prefixEnd_1416274 161606511214643790035929 := by
  unfold tailWord_1416274
  simp only [CollatzResearch.WordTrace]
  refine ⟨12913939117772163296807969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34437170980725768791487917 12913939117772163296807969)
  ·
    refine ⟨9685454338329122472605977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12913939117772163296807969 9685454338329122472605977)
    ·
      refine ⟨7264090753746841854454483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9685454338329122472605977 7264090753746841854454483)
      ·
        refine ⟨10896136130620262781681725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7264090753746841854454483 10896136130620262781681725)
        ·
          refine ⟨4086051048982598543130647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10896136130620262781681725 4086051048982598543130647)
          ·
            refine ⟨6129076573473897814695971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4086051048982598543130647 6129076573473897814695971)
            ·
              refine ⟨9193614860210846722043957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6129076573473897814695971 9193614860210846722043957)
              ·
                refine ⟨861901393144766880191621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9193614860210846722043957 861901393144766880191621)
                ·
                  refine ⟨161606511214643790035929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 861901393144766880191621 161606511214643790035929)
                  ·
                    rfl

theorem cell22_1416274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_1416274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416274 prefixEnd_1416274 := by exact prefixLift 1416274
  have htrace : WordTrace (prefixWord ++ tailWord_1416274) baseStart_1416274 baseEnd_1416274 := by
    simpa [prefixWord, tailWord_1416274, baseEnd_1416274] using wordTrace_append hprefix tailTrace_1416274
  have hstable : (prefixWord ++ tailWord_1416274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416274).length < 2 ^ (prefixWord ++ tailWord_1416274).sum := by decide
  have hdescent : baseEnd_1416274 < baseStart_1416274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416289 : List Nat := [1, 2, 3, 1, 1, 2, 5, 2, 2, 3]
def baseStart_1416289 : Nat := 118140960795 + 1416289 * 2 ^ 59
def prefixEnd_1416289 : Nat := 4983230072969 + 3 ^ 40 * 1416289 * 2
def baseEnd_1416289 : Nat := 484824668450476330982741

theorem tailTrace_1416289 : CollatzResearch.WordTrace tailWord_1416289 prefixEnd_1416289 484824668450476330982741 := by
  unfold tailWord_1416289
  simp only [CollatzResearch.WordTrace]
  refine ⟨51656303566034310749027921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34437535710689540499351947 51656303566034310749027921)
  ·
    refine ⟨38742227674525733061770941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51656303566034310749027921 38742227674525733061770941)
    ·
      refine ⟨14528335377947149898164103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38742227674525733061770941 14528335377947149898164103)
      ·
        refine ⟨21792503066920724847246155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14528335377947149898164103 21792503066920724847246155)
        ·
          refine ⟨32688754600381087270869233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21792503066920724847246155 32688754600381087270869233)
          ·
            refine ⟨24516565950285815453151925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32688754600381087270869233 24516565950285815453151925)
            ·
              refine ⟨2298428057839295198732993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24516565950285815453151925 2298428057839295198732993)
              ·
                refine ⟨1723821043379471399049745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2298428057839295198732993 1723821043379471399049745)
                ·
                  refine ⟨1292865782534603549287309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1723821043379471399049745 1292865782534603549287309)
                  ·
                    refine ⟨484824668450476330982741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1292865782534603549287309 484824668450476330982741)
                    ·
                      rfl

theorem cell22_1416289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_1416289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416289 prefixEnd_1416289 := by exact prefixLift 1416289
  have htrace : WordTrace (prefixWord ++ tailWord_1416289) baseStart_1416289 baseEnd_1416289 := by
    simpa [prefixWord, tailWord_1416289, baseEnd_1416289] using wordTrace_append hprefix tailTrace_1416289
  have hstable : (prefixWord ++ tailWord_1416289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416289).length < 2 ^ (prefixWord ++ tailWord_1416289).sum := by decide
  have hdescent : baseEnd_1416289 < baseStart_1416289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416306 : List Nat := [3, 2, 1, 2, 2, 1, 5, 1, 2, 3]
def baseStart_1416306 : Nat := 118140960795 + 1416306 * 2 ^ 59
def prefixEnd_1416306 : Nat := 4983230072969 + 3 ^ 40 * 1416306 * 2
def baseEnd_1416306 : Nat := 484830487897893953307689

theorem tailTrace_1416306 : CollatzResearch.WordTrace tailWord_1416306 prefixEnd_1416306 484830487897893953307689 := by
  unfold tailWord_1416306
  simp only [CollatzResearch.WordTrace]
  refine ⟨12914230901743180663099193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34437949071315148434931181 12914230901743180663099193)
  ·
    refine ⟨9685673176307385497324395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12914230901743180663099193 9685673176307385497324395)
    ·
      refine ⟨14528509764461078245986593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9685673176307385497324395 14528509764461078245986593)
      ·
        refine ⟨10896382323345808684489945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14528509764461078245986593 10896382323345808684489945)
        ·
          refine ⟨8172286742509356513367459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10896382323345808684489945 8172286742509356513367459)
          ·
            refine ⟨12258430113764034770051189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8172286742509356513367459 12258430113764034770051189)
            ·
              refine ⟨1149227823165378259692299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12258430113764034770051189 1149227823165378259692299)
              ·
                refine ⟨1723841734748067389538449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1149227823165378259692299 1723841734748067389538449)
                ·
                  refine ⟨1292881301061050542153837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1723841734748067389538449 1292881301061050542153837)
                  ·
                    refine ⟨484830487897893953307689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1292881301061050542153837 484830487897893953307689)
                    ·
                      rfl

theorem cell22_1416306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_1416306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416306 prefixEnd_1416306 := by exact prefixLift 1416306
  have htrace : WordTrace (prefixWord ++ tailWord_1416306) baseStart_1416306 baseEnd_1416306 := by
    simpa [prefixWord, tailWord_1416306, baseEnd_1416306] using wordTrace_append hprefix tailTrace_1416306
  have hstable : (prefixWord ++ tailWord_1416306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416306).length < 2 ^ (prefixWord ++ tailWord_1416306).sum := by decide
  have hdescent : baseEnd_1416306 < baseStart_1416306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416315 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 2, 6]
def baseStart_1416315 : Nat := 118140960795 + 1416315 * 2 ^ 59
def prefixEnd_1416315 : Nat := 4983230072969 + 3 ^ 40 * 1416315 * 2
def baseEnd_1416315 : Nat := 484833568781820929832661

theorem tailTrace_1416315 : CollatzResearch.WordTrace tailWord_1416315 prefixEnd_1416315 484833568781820929832661 := by
  unfold tailWord_1416315
  simp only [CollatzResearch.WordTrace]
  refine ⟨51657251863940117189474399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34438167909293411459649599 51657251863940117189474399)
  ·
    refine ⟨77485877795910175784211599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51657251863940117189474399 77485877795910175784211599)
    ·
      refine ⟨116228816693865263676317399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77485877795910175784211599 116228816693865263676317399)
      ·
        refine ⟨174343225040797895514476099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116228816693865263676317399 174343225040797895514476099)
        ·
          refine ⟨261514837561196843271714149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174343225040797895514476099 261514837561196843271714149)
          ·
            refine ⟨49034032042724408113446403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 261514837561196843271714149 49034032042724408113446403)
            ·
              refine ⟨73551048064086612170169605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49034032042724408113446403 73551048064086612170169605)
              ·
                refine ⟨13790821512016239781906801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73551048064086612170169605 13790821512016239781906801)
                ·
                  refine ⟨10343116134012179836430101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13790821512016239781906801 10343116134012179836430101)
                  ·
                    refine ⟨484833568781820929832661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10343116134012179836430101 484833568781820929832661)
                    ·
                      rfl

theorem cell22_1416315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 6].length) (baseStart_1416315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416315 prefixEnd_1416315 := by exact prefixLift 1416315
  have htrace : WordTrace (prefixWord ++ tailWord_1416315) baseStart_1416315 baseEnd_1416315 := by
    simpa [prefixWord, tailWord_1416315, baseEnd_1416315] using wordTrace_append hprefix tailTrace_1416315
  have hstable : (prefixWord ++ tailWord_1416315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416315).length < 2 ^ (prefixWord ++ tailWord_1416315).sum := by decide
  have hdescent : baseEnd_1416315 < baseStart_1416315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416424 : List Nat := [2, 1, 4, 1, 2, 1, 4, 1, 1, 5]
def baseStart_1416424 : Nat := 118140960795 + 1416424 * 2 ^ 59
def prefixEnd_1416424 : Nat := 4983230072969 + 3 ^ 40 * 1416424 * 2
def baseEnd_1416424 : Nat := 484870881709380978857327

theorem tailTrace_1416424 : CollatzResearch.WordTrace tailWord_1416424 prefixEnd_1416424 484870881709380978857327 := by
  unfold tailWord_1416424
  simp only [CollatzResearch.WordTrace]
  refine ⟨25830613710272614402596163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34440818280363485870128217 25830613710272614402596163)
  ·
    refine ⟨38745920565408921603894245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25830613710272614402596163 38745920565408921603894245)
    ·
      refine ⟨7264860106014172800730171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38745920565408921603894245 7264860106014172800730171)
      ·
        refine ⟨10897290159021259201095257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7264860106014172800730171 10897290159021259201095257)
        ·
          refine ⟨8172967619265944400821443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10897290159021259201095257 8172967619265944400821443)
          ·
            refine ⟨12259451428898916601232165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8172967619265944400821443 12259451428898916601232165)
            ·
              refine ⟨2298647142918546862731031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12259451428898916601232165 2298647142918546862731031)
              ·
                refine ⟨3447970714377820294096547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2298647142918546862731031 3447970714377820294096547)
                ·
                  refine ⟨5171956071566730441144821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3447970714377820294096547 5171956071566730441144821)
                  ·
                    refine ⟨484870881709380978857327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5171956071566730441144821 484870881709380978857327)
                    ·
                      rfl

theorem cell22_1416424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_1416424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416424 prefixEnd_1416424 := by exact prefixLift 1416424
  have htrace : WordTrace (prefixWord ++ tailWord_1416424) baseStart_1416424 baseEnd_1416424 := by
    simpa [prefixWord, tailWord_1416424, baseEnd_1416424] using wordTrace_append hprefix tailTrace_1416424
  have hstable : (prefixWord ++ tailWord_1416424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416424).length < 2 ^ (prefixWord ++ tailWord_1416424).sum := by decide
  have hdescent : baseEnd_1416424 < baseStart_1416424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416516 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 7]
def baseStart_1416516 : Nat := 118140960795 + 1416516 * 2 ^ 59
def prefixEnd_1416516 : Nat := 4983230072969 + 3 ^ 40 * 1416516 * 2
def baseEnd_1416516 : Nat := 161634125063174468519015

theorem tailTrace_1416516 : CollatzResearch.WordTrace tailWord_1416516 prefixEnd_1416516 161634125063174468519015 := by
  unfold tailWord_1416516
  simp only [CollatzResearch.WordTrace]
  refine ⟨25832291468105964258770701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34443055290807952345027601 25832291468105964258770701)
  ·
    refine ⟨9687109300539736597039013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25832291468105964258770701 9687109300539736597039013)
    ·
      refine ⟨1816332993851200611944815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9687109300539736597039013 1816332993851200611944815)
      ·
        refine ⟨2724499490776800917917223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1816332993851200611944815 2724499490776800917917223)
        ·
          refine ⟨4086749236165201376875835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2724499490776800917917223 4086749236165201376875835)
          ·
            refine ⟨6130123854247802065313753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4086749236165201376875835 6130123854247802065313753)
            ·
              refine ⟨4597592890685851548985315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6130123854247802065313753 4597592890685851548985315)
              ·
                refine ⟨6896389336028777323477973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4597592890685851548985315 6896389336028777323477973)
                ·
                  refine ⟨161634125063174468519015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6896389336028777323477973 161634125063174468519015)
                  ·
                    rfl

theorem cell22_1416516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_1416516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416516 prefixEnd_1416516 := by exact prefixLift 1416516
  have htrace : WordTrace (prefixWord ++ tailWord_1416516) baseStart_1416516 baseEnd_1416516 := by
    simpa [prefixWord, tailWord_1416516, baseEnd_1416516] using wordTrace_append hprefix tailTrace_1416516
  have hstable : (prefixWord ++ tailWord_1416516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416516).length < 2 ^ (prefixWord ++ tailWord_1416516).sum := by decide
  have hdescent : baseEnd_1416516 < baseStart_1416516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416529 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 3, 4]
def baseStart_1416529 : Nat := 118140960795 + 1416529 * 2 ^ 59
def prefixEnd_1416529 : Nat := 4983230072969 + 3 ^ 40 * 1416529 * 2
def baseEnd_1416529 : Nat := 484906825355195704982005

theorem tailTrace_1416529 : CollatzResearch.WordTrace tailWord_1416529 prefixEnd_1416529 484906825355195704982005 := by
  unfold tailWord_1416529
  simp only [CollatzResearch.WordTrace]
  refine ⟨51665057085164831737764641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34443371390109887825176427 51665057085164831737764641)
  ·
    refine ⟨38748792813873623803323481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51665057085164831737764641 38748792813873623803323481)
    ·
      refine ⟨29061594610405217852492611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38748792813873623803323481 29061594610405217852492611)
      ·
        refine ⟨43592391915607826778738917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29061594610405217852492611 43592391915607826778738917)
        ·
          refine ⟨8173573484176467521013547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43592391915607826778738917 8173573484176467521013547)
          ·
            refine ⟨12260360226264701281520321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8173573484176467521013547 12260360226264701281520321)
            ·
              refine ⟨9195270169698525961140241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12260360226264701281520321 9195270169698525961140241)
              ·
                refine ⟨6896452627273894470855181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9195270169698525961140241 6896452627273894470855181)
                ·
                  refine ⟨2586169735227710426570693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6896452627273894470855181 2586169735227710426570693)
                  ·
                    refine ⟨484906825355195704982005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2586169735227710426570693 484906825355195704982005)
                    ·
                      rfl

theorem cell22_1416529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_1416529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416529 prefixEnd_1416529 := by exact prefixLift 1416529
  have htrace : WordTrace (prefixWord ++ tailWord_1416529) baseStart_1416529 baseEnd_1416529 := by
    simpa [prefixWord, tailWord_1416529, baseEnd_1416529] using wordTrace_append hprefix tailTrace_1416529
  have hstable : (prefixWord ++ tailWord_1416529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416529).length < 2 ^ (prefixWord ++ tailWord_1416529).sum := by decide
  have hdescent : baseEnd_1416529 < baseStart_1416529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416533 : List Nat := [1, 3, 2, 2, 3, 3, 2, 1, 5]
def baseStart_1416533 : Nat := 118140960795 + 1416533 * 2 ^ 59
def prefixEnd_1416533 : Nat := 4983230072969 + 3 ^ 40 * 1416533 * 2
def baseEnd_1416533 : Nat := 161636064878980342627331

theorem tailTrace_1416533 : CollatzResearch.WordTrace tailWord_1416533 prefixEnd_1416533 161636064878980342627331 := by
  unfold tailWord_1416533
  simp only [CollatzResearch.WordTrace]
  refine ⟨51665202977150340420910253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34443468651433560280606835 51665202977150340420910253)
  ·
    refine ⟨19374451116431377657841345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51665202977150340420910253 19374451116431377657841345)
    ·
      refine ⟨14530838337323533243381009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19374451116431377657841345 14530838337323533243381009)
      ·
        refine ⟨10898128752992649932535757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14530838337323533243381009 10898128752992649932535757)
        ·
          refine ⟨4086798282372243724700909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10898128752992649932535757 4086798282372243724700909)
          ·
            refine ⟨1532549355889591396762841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4086798282372243724700909 1532549355889591396762841)
            ·
              refine ⟨1149412016917193547572131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1532549355889591396762841 1149412016917193547572131)
              ·
                refine ⟨1724118025375790321358197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1149412016917193547572131 1724118025375790321358197)
                ·
                  refine ⟨161636064878980342627331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1724118025375790321358197 161636064878980342627331)
                  ·
                    rfl

theorem cell22_1416533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 5].length) (baseStart_1416533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416533 prefixEnd_1416533 := by exact prefixLift 1416533
  have htrace : WordTrace (prefixWord ++ tailWord_1416533) baseStart_1416533 baseEnd_1416533 := by
    simpa [prefixWord, tailWord_1416533, baseEnd_1416533] using wordTrace_append hprefix tailTrace_1416533
  have hstable : (prefixWord ++ tailWord_1416533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416533).length < 2 ^ (prefixWord ++ tailWord_1416533).sum := by decide
  have hdescent : baseEnd_1416533 < baseStart_1416533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416546 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1416546 : Nat := 118140960795 + 1416546 * 2 ^ 59
def prefixEnd_1416546 : Nat := 4983230072969 + 3 ^ 40 * 1416546 * 2
def baseEnd_1416546 : Nat := 484912644802613327306953

theorem tailTrace_1416546 : CollatzResearch.WordTrace tailWord_1416546 prefixEnd_1416546 484912644802613327306953 := by
  unfold tailWord_1416546
  simp only [CollatzResearch.WordTrace]
  refine ⟨12916419281525810910283373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34443784750735495760755661 12916419281525810910283373)
  ·
    refine ⟨4843657230572179091356265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12916419281525810910283373 4843657230572179091356265)
    ·
      refine ⟨3632742922929134318517199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4843657230572179091356265 3632742922929134318517199)
      ·
        refine ⟨5449114384393701477775799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3632742922929134318517199 5449114384393701477775799)
        ·
          refine ⟨8173671576590552216663699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5449114384393701477775799 8173671576590552216663699)
          ·
            refine ⟨12260507364885828324995549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8173671576590552216663699 12260507364885828324995549)
            ·
              refine ⟨4597690261832185621873331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12260507364885828324995549 4597690261832185621873331)
              ·
                refine ⟨6896535392748278432809997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4597690261832185621873331 6896535392748278432809997)
                ·
                  refine ⟨2586200772280604412303749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6896535392748278432809997 2586200772280604412303749)
                  ·
                    refine ⟨484912644802613327306953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2586200772280604412303749 484912644802613327306953)
                    ·
                      rfl

theorem cell22_1416546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1416546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416546 prefixEnd_1416546 := by exact prefixLift 1416546
  have htrace : WordTrace (prefixWord ++ tailWord_1416546) baseStart_1416546 baseEnd_1416546 := by
    simpa [prefixWord, tailWord_1416546, baseEnd_1416546] using wordTrace_append hprefix tailTrace_1416546
  have hstable : (prefixWord ++ tailWord_1416546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416546).length < 2 ^ (prefixWord ++ tailWord_1416546).sum := by decide
  have hdescent : baseEnd_1416546 < baseStart_1416546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416559 : List Nat := [1, 1, 2, 1, 3, 1, 5, 2, 1, 5]
def baseStart_1416559 : Nat := 118140960795 + 1416559 * 2 ^ 59
def prefixEnd_1416559 : Nat := 4983230072969 + 3 ^ 40 * 1416559 * 2
def baseEnd_1416559 : Nat := 484917094968285626731913

theorem tailTrace_1416559 : CollatzResearch.WordTrace tailWord_1416559 prefixEnd_1416559 484917094968285626731913 := by
  unfold tailWord_1416559
  simp only [CollatzResearch.WordTrace]
  refine ⟨51666151275056146861356731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34444100850037431240904487 51666151275056146861356731)
  ·
    refine ⟨77499226912584220292035097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51666151275056146861356731 77499226912584220292035097)
    ·
      refine ⟨58124420184438165219026323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77499226912584220292035097 58124420184438165219026323)
      ·
        refine ⟨87186630276657247828539485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58124420184438165219026323 87186630276657247828539485)
        ·
          refine ⟨32694986353746467935702307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87186630276657247828539485 32694986353746467935702307)
          ·
            refine ⟨49042479530619701903553461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32694986353746467935702307 49042479530619701903553461)
            ·
              refine ⟨4597732455995597053458137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49042479530619701903553461 4597732455995597053458137)
              ·
                refine ⟨3448299341996697790093603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4597732455995597053458137 3448299341996697790093603)
                ·
                  refine ⟨5172449012995046685140405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3448299341996697790093603 5172449012995046685140405)
                  ·
                    refine ⟨484917094968285626731913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5172449012995046685140405 484917094968285626731913)
                    ·
                      rfl

theorem cell22_1416559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 5].length) (baseStart_1416559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416559 prefixEnd_1416559 := by exact prefixLift 1416559
  have htrace : WordTrace (prefixWord ++ tailWord_1416559) baseStart_1416559 baseEnd_1416559 := by
    simpa [prefixWord, tailWord_1416559, baseEnd_1416559] using wordTrace_append hprefix tailTrace_1416559
  have hstable : (prefixWord ++ tailWord_1416559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416559).length < 2 ^ (prefixWord ++ tailWord_1416559).sum := by decide
  have hdescent : baseEnd_1416559 < baseStart_1416559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416696 : List Nat := [2, 1, 2, 1, 1, 5, 3, 1, 6]
def baseStart_1416696 : Nat := 118140960795 + 1416696 * 2 ^ 59
def prefixEnd_1416696 : Nat := 4983230072969 + 3 ^ 40 * 1416696 * 2
def baseEnd_1416696 : Nat := 161654664289354312018831

theorem tailTrace_1416696 : CollatzResearch.WordTrace tailWord_1416696 prefixEnd_1416696 161654664289354312018831 := by
  unfold tailWord_1416696
  simp only [CollatzResearch.WordTrace]
  refine ⟨25835574037779909629546971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34447432050373212839395961 25835574037779909629546971)
  ·
    refine ⟨38753361056669864444320457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25835574037779909629546971 38753361056669864444320457)
    ·
      refine ⟨29065020792502398333240343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38753361056669864444320457 29065020792502398333240343)
      ·
        refine ⟨43597531188753597499860515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29065020792502398333240343 43597531188753597499860515)
        ·
          refine ⟨65396296783130396249790773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43597531188753597499860515 65396296783130396249790773)
          ·
            refine ⟨6130902823418474648417885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65396296783130396249790773 6130902823418474648417885)
            ·
              refine ⟨2299088558781927993156707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6130902823418474648417885 2299088558781927993156707)
              ·
                refine ⟨3448632838172891989735061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2299088558781927993156707 3448632838172891989735061)
                ·
                  refine ⟨161654664289354312018831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3448632838172891989735061 161654664289354312018831)
                  ·
                    rfl

theorem cell22_1416696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 6].length) (baseStart_1416696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416696 prefixEnd_1416696 := by exact prefixLift 1416696
  have htrace : WordTrace (prefixWord ++ tailWord_1416696) baseStart_1416696 baseEnd_1416696 := by
    simpa [prefixWord, tailWord_1416696, baseEnd_1416696] using wordTrace_append hprefix tailTrace_1416696
  have hstable : (prefixWord ++ tailWord_1416696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416696).length < 2 ^ (prefixWord ++ tailWord_1416696).sum := by decide
  have hdescent : baseEnd_1416696 < baseStart_1416696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416715 : List Nat := [1, 1, 1, 1, 8, 2, 1, 2, 1, 4]
def baseStart_1416715 : Nat := 118140960795 + 1416715 * 2 ^ 59
def prefixEnd_1416715 : Nat := 4983230072969 + 3 ^ 40 * 1416715 * 2
def baseEnd_1416715 : Nat := 484970496956353219831435

theorem tailTrace_1416715 : CollatzResearch.WordTrace tailWord_1416715 prefixEnd_1416715 484970496956353219831435 := by
  unfold tailWord_1416715
  simp only [CollatzResearch.WordTrace]
  refine ⟨51671841062490985504035599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34447894041660657002690399 51671841062490985504035599)
  ·
    refine ⟨77507761593736478256053399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51671841062490985504035599 77507761593736478256053399)
    ·
      refine ⟨116261642390604717384080099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77507761593736478256053399 116261642390604717384080099)
      ·
        refine ⟨174392463585907076076120149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116261642390604717384080099 174392463585907076076120149)
        ·
          refine ⟨2043661682647348547767033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 174392463585907076076120149 2043661682647348547767033)
          ·
            refine ⟨1532746261985511410825275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2043661682647348547767033 1532746261985511410825275)
            ·
              refine ⟨2299119392978267116237913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1532746261985511410825275 2299119392978267116237913)
              ·
                refine ⟨1724339544733700337178435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2299119392978267116237913 1724339544733700337178435)
                ·
                  refine ⟨2586509317100550505767653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1724339544733700337178435 2586509317100550505767653)
                  ·
                    refine ⟨484970496956353219831435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2586509317100550505767653 484970496956353219831435)
                    ·
                      rfl

theorem cell22_1416715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 4].length) (baseStart_1416715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416715 prefixEnd_1416715 := by exact prefixLift 1416715
  have htrace : WordTrace (prefixWord ++ tailWord_1416715) baseStart_1416715 baseEnd_1416715 := by
    simpa [prefixWord, tailWord_1416715, baseEnd_1416715] using wordTrace_append hprefix tailTrace_1416715
  have hstable : (prefixWord ++ tailWord_1416715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416715).length < 2 ^ (prefixWord ++ tailWord_1416715).sum := by decide
  have hdescent : baseEnd_1416715 < baseStart_1416715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416728 : List Nat := [2, 1, 2, 3, 4, 1, 1, 2, 1, 5]
def baseStart_1416728 : Nat := 118140960795 + 1416728 * 2 ^ 59
def prefixEnd_1416728 : Nat := 4983230072969 + 3 ^ 40 * 1416728 * 2
def baseEnd_1416728 : Nat := 484974947122025519256395

theorem tailTrace_1416728 : CollatzResearch.WordTrace tailWord_1416728 prefixEnd_1416728 484974947122025519256395 := by
  unfold tailWord_1416728
  simp only [CollatzResearch.WordTrace]
  refine ⟨25836157605721944362129419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34448210140962592482839225 25836157605721944362129419)
  ·
    refine ⟨38754236408582916543194129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25836157605721944362129419 38754236408582916543194129)
    ·
      refine ⟨29065677306437187407395597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38754236408582916543194129 29065677306437187407395597)
      ·
        refine ⟨10899628989913945277773349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29065677306437187407395597 10899628989913945277773349)
        ·
          refine ⟨2043680435608864739582503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10899628989913945277773349 2043680435608864739582503)
          ·
            refine ⟨3065520653413297109373755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2043680435608864739582503 3065520653413297109373755)
            ·
              refine ⟨4598280980119945664060633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3065520653413297109373755 4598280980119945664060633)
              ·
                refine ⟨3448710735089959248045475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4598280980119945664060633 3448710735089959248045475)
                ·
                  refine ⟨5173066102634938872068213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3448710735089959248045475 5173066102634938872068213)
                  ·
                    refine ⟨484974947122025519256395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5173066102634938872068213 484974947122025519256395)
                    ·
                      rfl

theorem cell22_1416728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_1416728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416728 prefixEnd_1416728 := by exact prefixLift 1416728
  have htrace : WordTrace (prefixWord ++ tailWord_1416728) baseStart_1416728 baseEnd_1416728 := by
    simpa [prefixWord, tailWord_1416728, baseEnd_1416728] using wordTrace_append hprefix tailTrace_1416728
  have hstable : (prefixWord ++ tailWord_1416728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416728).length < 2 ^ (prefixWord ++ tailWord_1416728).sum := by decide
  have hdescent : baseEnd_1416728 < baseStart_1416728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416773 : List Nat := [1, 3, 1, 1, 1, 4, 3, 2, 3, 3]
def baseStart_1416773 : Nat := 118140960795 + 1416773 * 2 ^ 59
def prefixEnd_1416773 : Nat := 4983230072969 + 3 ^ 40 * 1416773 * 2
def baseEnd_1416773 : Nat := 484990351541660401881257

theorem tailTrace_1416773 : CollatzResearch.WordTrace tailWord_1416773 prefixEnd_1416773 484990351541660401881257 := by
  unfold tailWord_1416773
  simp only [CollatzResearch.WordTrace]
  refine ⟨51673956496280861409646973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34449304330853907606431315 51673956496280861409646973)
  ·
    refine ⟨19377733686105323028617615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51673956496280861409646973 19377733686105323028617615)
    ·
      refine ⟨29066600529157984542926423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19377733686105323028617615 29066600529157984542926423)
      ·
        refine ⟨43599900793736976814389635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29066600529157984542926423 43599900793736976814389635)
        ·
          refine ⟨65399851190605465221584453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43599900793736976814389635 65399851190605465221584453)
          ·
            refine ⟨12262472098238524729047085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65399851190605465221584453 12262472098238524729047085)
            ·
              refine ⟨4598427036839446773392657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12262472098238524729047085 4598427036839446773392657)
              ·
                refine ⟨3448820277629585080044493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4598427036839446773392657 3448820277629585080044493)
                ·
                  refine ⟨1293307604111094405016685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3448820277629585080044493 1293307604111094405016685)
                  ·
                    refine ⟨484990351541660401881257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1293307604111094405016685 484990351541660401881257)
                    ·
                      rfl

theorem cell22_1416773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 3].length) (baseStart_1416773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416773 prefixEnd_1416773 := by exact prefixLift 1416773
  have htrace : WordTrace (prefixWord ++ tailWord_1416773) baseStart_1416773 baseEnd_1416773 := by
    simpa [prefixWord, tailWord_1416773, baseEnd_1416773] using wordTrace_append hprefix tailTrace_1416773
  have hstable : (prefixWord ++ tailWord_1416773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416773).length < 2 ^ (prefixWord ++ tailWord_1416773).sum := by decide
  have hdescent : baseEnd_1416773 < baseStart_1416773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416801 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 4, 5]
def baseStart_1416801 : Nat := 118140960795 + 1416801 * 2 ^ 59
def prefixEnd_1416801 : Nat := 4983230072969 + 3 ^ 40 * 1416801 * 2
def baseEnd_1416801 : Nat := 484999936513877662181171

theorem tailTrace_1416801 : CollatzResearch.WordTrace tailWord_1416801 prefixEnd_1416801 484999936513877662181171 := by
  unfold tailWord_1416801
  simp only [CollatzResearch.WordTrace]
  refine ⟨51674977740179422191666257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34449985160119614794444171 51674977740179422191666257)
  ·
    refine ⟨38756233305134566643749693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51674977740179422191666257 38756233305134566643749693)
    ·
      refine ⟨14533587489425462491406135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38756233305134566643749693 14533587489425462491406135)
      ·
        refine ⟨21800381234138193737109203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14533587489425462491406135 21800381234138193737109203)
        ·
          refine ⟨32700571851207290605663805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21800381234138193737109203 32700571851207290605663805)
          ·
            refine ⟨12262714444202733977123927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32700571851207290605663805 12262714444202733977123927)
            ·
              refine ⟨18394071666304100965685891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12262714444202733977123927 18394071666304100965685891)
              ·
                refine ⟨27591107499456151448528837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18394071666304100965685891 27591107499456151448528837)
                ·
                  refine ⟨5173332656148028396599157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27591107499456151448528837 5173332656148028396599157)
                  ·
                    refine ⟨484999936513877662181171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5173332656148028396599157 484999936513877662181171)
                    ·
                      rfl

theorem cell22_1416801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_1416801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416801 prefixEnd_1416801 := by exact prefixLift 1416801
  have htrace : WordTrace (prefixWord ++ tailWord_1416801) baseStart_1416801 baseEnd_1416801 := by
    simpa [prefixWord, tailWord_1416801, baseEnd_1416801] using wordTrace_append hprefix tailTrace_1416801
  have hstable : (prefixWord ++ tailWord_1416801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416801).length < 2 ^ (prefixWord ++ tailWord_1416801).sum := by decide
  have hdescent : baseEnd_1416801 < baseStart_1416801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416803 : List Nat := [1, 1, 1, 5, 1, 3, 3, 2, 5]
def baseStart_1416803 : Nat := 118140960795 + 1416803 * 2 ^ 59
def prefixEnd_1416803 : Nat := 4983230072969 + 3 ^ 40 * 1416803 * 2
def baseEnd_1416803 : Nat := 161666873718250107877055

theorem tailTrace_1416803 : CollatzResearch.WordTrace tailWord_1416803 prefixEnd_1416803 161666873718250107877055 := by
  unfold tailWord_1416803
  simp only [CollatzResearch.WordTrace]
  refine ⟨51675050686172176533239063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34450033790781451022159375 51675050686172176533239063)
  ·
    refine ⟨77512576029258264799858595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51675050686172176533239063 77512576029258264799858595)
    ·
      refine ⟨116268864043887397199787893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77512576029258264799858595 116268864043887397199787893)
      ·
        refine ⟨10900206004114443487480115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116268864043887397199787893 10900206004114443487480115)
        ·
          refine ⟨16350309006171665231220173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10900206004114443487480115 16350309006171665231220173)
          ·
            refine ⟨6131365877314374461707565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16350309006171665231220173 6131365877314374461707565)
            ·
              refine ⟨2299262203992890423140337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6131365877314374461707565 2299262203992890423140337)
              ·
                refine ⟨1724446652994667817355253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2299262203992890423140337 1724446652994667817355253)
                ·
                  refine ⟨161666873718250107877055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1724446652994667817355253 161666873718250107877055)
                  ·
                    rfl

theorem cell22_1416803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 5].length) (baseStart_1416803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416803 prefixEnd_1416803 := by exact prefixLift 1416803
  have htrace : WordTrace (prefixWord ++ tailWord_1416803) baseStart_1416803 baseEnd_1416803 := by
    simpa [prefixWord, tailWord_1416803, baseEnd_1416803] using wordTrace_append hprefix tailTrace_1416803
  have hstable : (prefixWord ++ tailWord_1416803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416803).length < 2 ^ (prefixWord ++ tailWord_1416803).sum := by decide
  have hdescent : baseEnd_1416803 < baseStart_1416803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416818 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 2, 5]
def baseStart_1416818 : Nat := 118140960795 + 1416818 * 2 ^ 59
def prefixEnd_1416818 : Nat := 4983230072969 + 3 ^ 40 * 1416818 * 2
def baseEnd_1416818 : Nat := 485005755961295284506119

theorem tailTrace_1416818 : CollatzResearch.WordTrace tailWord_1416818 prefixEnd_1416818 485005755961295284506119 := by
  unfold tailWord_1416818
  simp only [CollatzResearch.WordTrace]
  refine ⟨12918899445279458523758777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34450398520745222730023405 12918899445279458523758777)
  ·
    refine ⟨9689174583959593892819083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12918899445279458523758777 9689174583959593892819083)
    ·
      refine ⟨14533761875939390839228625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9689174583959593892819083 14533761875939390839228625)
      ·
        refine ⟨10900321406954543129421469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14533761875939390839228625 10900321406954543129421469)
        ·
          refine ⟨4087620527607953673533051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10900321406954543129421469 4087620527607953673533051)
          ·
            refine ⟨6131430791411930510299577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4087620527607953673533051 6131430791411930510299577)
            ·
              refine ⟨4598573093558947882724683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6131430791411930510299577 4598573093558947882724683)
              ·
                refine ⟨6897859640338421824087025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4598573093558947882724683 6897859640338421824087025)
                ·
                  refine ⟨5173394730253816368065269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6897859640338421824087025 5173394730253816368065269)
                  ·
                    refine ⟨485005755961295284506119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5173394730253816368065269 485005755961295284506119)
                    ·
                      rfl

theorem cell22_1416818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_1416818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416818 prefixEnd_1416818 := by exact prefixLift 1416818
  have htrace : WordTrace (prefixWord ++ tailWord_1416818) baseStart_1416818 baseEnd_1416818 := by
    simpa [prefixWord, tailWord_1416818, baseEnd_1416818] using wordTrace_append hprefix tailTrace_1416818
  have hstable : (prefixWord ++ tailWord_1416818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416818).length < 2 ^ (prefixWord ++ tailWord_1416818).sum := by decide
  have hdescent : baseEnd_1416818 < baseStart_1416818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416865 : List Nat := [1, 2, 3, 3, 2, 3, 1, 1, 6]
def baseStart_1416865 : Nat := 118140960795 + 1416865 * 2 ^ 59
def prefixEnd_1416865 : Nat := 4983230072969 + 3 ^ 40 * 1416865 * 2
def baseEnd_1416865 : Nat := 161673948340600942860325

theorem tailTrace_1416865 : CollatzResearch.WordTrace tailWord_1416865 prefixEnd_1416865 161673948340600942860325 := by
  unfold tailWord_1416865
  simp only [CollatzResearch.WordTrace]
  refine ⟨51677312011947561121996049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34451541341298374081330699 51677312011947561121996049)
  ·
    refine ⟨38757984008960670841497037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51677312011947561121996049 38757984008960670841497037)
    ·
      refine ⟨14534244003360251565561389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38757984008960670841497037 14534244003360251565561389)
      ·
        refine ⟨5450341501260094337085521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14534244003360251565561389 5450341501260094337085521)
        ·
          refine ⟨4087756125945070752814141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5450341501260094337085521 4087756125945070752814141)
          ·
            refine ⟨1532908547229401532305303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4087756125945070752814141 1532908547229401532305303)
            ·
              refine ⟨2299362820844102298457955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1532908547229401532305303 2299362820844102298457955)
              ·
                refine ⟨3449044231266153447686933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2299362820844102298457955 3449044231266153447686933)
                ·
                  refine ⟨161673948340600942860325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3449044231266153447686933 161673948340600942860325)
                  ·
                    rfl

theorem cell22_1416865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 6].length) (baseStart_1416865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416865 prefixEnd_1416865 := by exact prefixLift 1416865
  have htrace : WordTrace (prefixWord ++ tailWord_1416865) baseStart_1416865 baseEnd_1416865 := by
    simpa [prefixWord, tailWord_1416865, baseEnd_1416865] using wordTrace_append hprefix tailTrace_1416865
  have hstable : (prefixWord ++ tailWord_1416865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416865).length < 2 ^ (prefixWord ++ tailWord_1416865).sum := by decide
  have hdescent : baseEnd_1416865 < baseStart_1416865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416891 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 2, 7]
def baseStart_1416891 : Nat := 118140960795 + 1416891 * 2 ^ 59
def prefixEnd_1416891 : Nat := 4983230072969 + 3 ^ 40 * 1416891 * 2
def baseEnd_1416891 : Nat := 485030745353147427430895

theorem tailTrace_1416891 : CollatzResearch.WordTrace tailWord_1416891 prefixEnd_1416891 485030745353147427430895 := by
  unfold tailWord_1416891
  simp only [CollatzResearch.WordTrace]
  refine ⟨51678260309853367562442527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34452173539902245041628351 51678260309853367562442527)
  ·
    refine ⟨77517390464780051343663791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51678260309853367562442527 77517390464780051343663791)
    ·
      refine ⟨116276085697170077015495687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77517390464780051343663791 116276085697170077015495687)
      ·
        refine ⟨174414128545755115523243531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116276085697170077015495687 174414128545755115523243531)
        ·
          refine ⟨261621192818632673284865297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174414128545755115523243531 261621192818632673284865297)
          ·
            refine ⟨196215894613974504963648973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261621192818632673284865297 196215894613974504963648973)
            ·
              refine ⟨73580960480240439361368365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196215894613974504963648973 73580960480240439361368365)
              ·
                refine ⟨27592860180090164760513137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73580960480240439361368365 27592860180090164760513137)
                ·
                  refine ⟨20694645135067623570384853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27592860180090164760513137 20694645135067623570384853)
                  ·
                    refine ⟨485030745353147427430895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20694645135067623570384853 485030745353147427430895)
                    ·
                      rfl

theorem cell22_1416891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 7].length) (baseStart_1416891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1416891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1416891 prefixEnd_1416891 := by exact prefixLift 1416891
  have htrace : WordTrace (prefixWord ++ tailWord_1416891) baseStart_1416891 baseEnd_1416891 := by
    simpa [prefixWord, tailWord_1416891, baseEnd_1416891] using wordTrace_append hprefix tailTrace_1416891
  have hstable : (prefixWord ++ tailWord_1416891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416891).length < 2 ^ (prefixWord ++ tailWord_1416891).sum := by decide
  have hdescent : baseEnd_1416891 < baseStart_1416891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417000 : List Nat := [2, 1, 5, 1, 1, 2, 2, 2, 6]
def baseStart_1417000 : Nat := 118140960795 + 1417000 * 2 ^ 59
def prefixEnd_1417000 : Nat := 4983230072969 + 3 ^ 40 * 1417000 * 2
def baseEnd_1417000 : Nat := 161689352760235825485187

theorem tailTrace_1417000 : CollatzResearch.WordTrace tailWord_1417000 prefixEnd_1417000 161689352760235825485187 := by
  unfold tailWord_1417000
  simp only [CollatzResearch.WordTrace]
  refine ⟨25841117933229239589080227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34454823910972319452106969 25841117933229239589080227)
  ·
    refine ⟨38761676899843859383620341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25841117933229239589080227 38761676899843859383620341)
    ·
      refine ⟨3633907209360361817214407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38761676899843859383620341 3633907209360361817214407)
      ·
        refine ⟨5450860814040542725821611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3633907209360361817214407 5450860814040542725821611)
        ·
          refine ⟨8176291221060814088732417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5450860814040542725821611 8176291221060814088732417)
          ·
            refine ⟨6132218415795610566549313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8176291221060814088732417 6132218415795610566549313)
            ·
              refine ⟨4599163811846707924911985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6132218415795610566549313 4599163811846707924911985)
              ·
                refine ⟨3449372858885030943683989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4599163811846707924911985 3449372858885030943683989)
                ·
                  refine ⟨161689352760235825485187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3449372858885030943683989 161689352760235825485187)
                  ·
                    rfl

theorem cell22_1417000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 6].length) (baseStart_1417000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417000 prefixEnd_1417000 := by exact prefixLift 1417000
  have htrace : WordTrace (prefixWord ++ tailWord_1417000) baseStart_1417000 baseEnd_1417000 := by
    simpa [prefixWord, tailWord_1417000, baseEnd_1417000] using wordTrace_append hprefix tailTrace_1417000
  have hstable : (prefixWord ++ tailWord_1417000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417000).length < 2 ^ (prefixWord ++ tailWord_1417000).sum := by decide
  have hdescent : baseEnd_1417000 < baseStart_1417000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417045 : List Nat := [1, 3, 2, 2, 2, 3, 2, 7]
def baseStart_1417045 : Nat := 118140960795 + 1417045 * 2 ^ 59
def prefixEnd_1417045 : Nat := 4983230072969 + 3 ^ 40 * 1417045 * 2
def baseEnd_1417045 : Nat := 53898162522260262120047

theorem tailTrace_1417045 : CollatzResearch.WordTrace tailWord_1417045 prefixEnd_1417045 53898162522260262120047 := by
  unfold tailWord_1417045
  simp only [CollatzResearch.WordTrace]
  refine ⟨51683877151295451863548589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34455918100863634575699059 51683877151295451863548589)
  ·
    refine ⟨19381453931735794448830721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51683877151295451863548589 19381453931735794448830721)
    ·
      refine ⟨14536090448801845836623041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19381453931735794448830721 14536090448801845836623041)
      ·
        refine ⟨10902067836601384377467281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14536090448801845836623041 10902067836601384377467281)
        ·
          refine ⟨8176550877451038283100461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10902067836601384377467281 8176550877451038283100461)
          ·
            refine ⟨3066206579044139356162673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8176550877451038283100461 3066206579044139356162673)
            ·
              refine ⟨2299654934283104517122005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3066206579044139356162673 2299654934283104517122005)
              ·
                refine ⟨53898162522260262120047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2299654934283104517122005 53898162522260262120047)
                ·
                  rfl

theorem cell22_1417045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 7].length) (baseStart_1417045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417045 prefixEnd_1417045 := by exact prefixLift 1417045
  have htrace : WordTrace (prefixWord ++ tailWord_1417045) baseStart_1417045 baseEnd_1417045 := by
    simpa [prefixWord, tailWord_1417045, baseEnd_1417045] using wordTrace_append hprefix tailTrace_1417045
  have hstable : (prefixWord ++ tailWord_1417045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417045).length < 2 ^ (prefixWord ++ tailWord_1417045).sum := by decide
  have hdescent : baseEnd_1417045 < baseStart_1417045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417152 : List Nat := [2, 1, 1, 2, 3, 2, 1, 6, 4]
def baseStart_1417152 : Nat := 118140960795 + 1417152 * 2 ^ 59
def prefixEnd_1417152 : Nat := 4983230072969 + 3 ^ 40 * 1417152 * 2
def baseEnd_1417152 : Nat := 161706696995676582218365

theorem tailTrace_1417152 : CollatzResearch.WordTrace tailWord_1417152 prefixEnd_1417152 161706696995676582218365 := by
  unfold tailWord_1417152
  simp only [CollatzResearch.WordTrace]
  refine ⟨25843889880953904568846855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34458519841271872758462473 25843889880953904568846855)
  ·
    refine ⟨38765834821430856853270283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25843889880953904568846855 38765834821430856853270283)
    ·
      refine ⟨58148752232146285279905425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38765834821430856853270283 58148752232146285279905425)
      ·
        refine ⟨43611564174109713959929069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58148752232146285279905425 43611564174109713959929069)
        ·
          refine ⟨16354336565291142734973401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43611564174109713959929069 16354336565291142734973401)
          ·
            refine ⟨12265752423968357051230051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16354336565291142734973401 12265752423968357051230051)
            ·
              refine ⟨18398628635952535576845077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12265752423968357051230051 18398628635952535576845077)
              ·
                refine ⟨862435717310275105164613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18398628635952535576845077 862435717310275105164613)
                ·
                  refine ⟨161706696995676582218365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 862435717310275105164613 161706696995676582218365)
                  ·
                    rfl

theorem cell22_1417152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 6, 4].length) (baseStart_1417152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417152 prefixEnd_1417152 := by exact prefixLift 1417152
  have htrace : WordTrace (prefixWord ++ tailWord_1417152) baseStart_1417152 baseEnd_1417152 := by
    simpa [prefixWord, tailWord_1417152, baseEnd_1417152] using wordTrace_append hprefix tailTrace_1417152
  have hstable : (prefixWord ++ tailWord_1417152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417152).length < 2 ^ (prefixWord ++ tailWord_1417152).sum := by decide
  have hdescent : baseEnd_1417152 < baseStart_1417152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417214 : List Nat := [4, 2, 2, 2, 1, 2, 2, 7]
def baseStart_1417214 : Nat := 118140960795 + 1417214 * 2 ^ 59
def prefixEnd_1417214 : Nat := 4983230072969 + 3 ^ 40 * 1417214 * 2
def baseEnd_1417214 : Nat := 53904590539342472400545

theorem tailTrace_1417214 : CollatzResearch.WordTrace tailWord_1417214 prefixEnd_1417214 53904590539342472400545 := by
  unfold tailWord_1417214
  simp only [CollatzResearch.WordTrace]
  refine ⟨6461255135960399215806337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34460027391788795817633797 6461255135960399215806337)
  ·
    refine ⟨4845941351970299411854753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6461255135960399215806337 4845941351970299411854753)
    ·
      refine ⟨3634456013977724558891065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4845941351970299411854753 3634456013977724558891065)
      ·
        refine ⟨2725842010483293419168299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3634456013977724558891065 2725842010483293419168299)
        ·
          refine ⟨4088763015724940128752449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2725842010483293419168299 4088763015724940128752449)
          ·
            refine ⟨3066572261793705096564337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4088763015724940128752449 3066572261793705096564337)
            ·
              refine ⟨2299929196345278822423253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3066572261793705096564337 2299929196345278822423253)
              ·
                refine ⟨53904590539342472400545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2299929196345278822423253 53904590539342472400545)
                ·
                  rfl

theorem cell22_1417214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_1417214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417214 prefixEnd_1417214 := by exact prefixLift 1417214
  have htrace : WordTrace (prefixWord ++ tailWord_1417214) baseStart_1417214 baseEnd_1417214 := by
    simpa [prefixWord, tailWord_1417214, baseEnd_1417214] using wordTrace_append hprefix tailTrace_1417214
  have hstable : (prefixWord ++ tailWord_1417214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417214).length < 2 ^ (prefixWord ++ tailWord_1417214).sum := by decide
  have hdescent : baseEnd_1417214 < baseStart_1417214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417222 : List Nat := [6, 2, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_1417222 : Nat := 118140960795 + 1417222 * 2 ^ 59
def prefixEnd_1417222 : Nat := 4983230072969 + 3 ^ 40 * 1417222 * 2
def baseEnd_1417222 : Nat := 485144053417572897404881

theorem tailTrace_1417222 : CollatzResearch.WordTrace tailWord_1417222 prefixEnd_1417222 485144053417572897404881 := by
  unfold tailWord_1417222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1615322902239194096648185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34460221914436140728494613 1615322902239194096648185)
  ·
    refine ⟨1211492176679395572486139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1615322902239194096648185 1211492176679395572486139)
    ·
      refine ⟨1817238265019093358729209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1211492176679395572486139 1817238265019093358729209)
      ·
        refine ⟨1362928698764320019046907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1817238265019093358729209 1362928698764320019046907)
        ·
          refine ⟨2044393048146480028570361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1362928698764320019046907 2044393048146480028570361)
          ·
            refine ⟨1533294786109860021427771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2044393048146480028570361 1533294786109860021427771)
            ·
              refine ⟨2299942179164790032141657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1533294786109860021427771 2299942179164790032141657)
              ·
                refine ⟨1724956634373592524106243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2299942179164790032141657 1724956634373592524106243)
                ·
                  refine ⟨2587434951560388786159365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1724956634373592524106243 2587434951560388786159365)
                  ·
                    refine ⟨485144053417572897404881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2587434951560388786159365 485144053417572897404881)
                    ·
                      rfl

theorem cell22_1417222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_1417222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417222 prefixEnd_1417222 := by exact prefixLift 1417222
  have htrace : WordTrace (prefixWord ++ tailWord_1417222) baseStart_1417222 baseEnd_1417222 := by
    simpa [prefixWord, tailWord_1417222, baseEnd_1417222] using wordTrace_append hprefix tailTrace_1417222
  have hstable : (prefixWord ++ tailWord_1417222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417222).length < 2 ^ (prefixWord ++ tailWord_1417222).sum := by decide
  have hdescent : baseEnd_1417222 < baseStart_1417222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417287 : List Nat := [1, 1, 4, 1, 3, 1, 3, 2, 6]
def baseStart_1417287 : Nat := 118140960795 + 1417287 * 2 ^ 59
def prefixEnd_1417287 : Nat := 4983230072969 + 3 ^ 40 * 1417287 * 2
def baseEnd_1417287 : Nat := 161722101415311464843227

theorem tailTrace_1417287 : CollatzResearch.WordTrace tailWord_1417287 prefixEnd_1417287 161722101415311464843227 := by
  unfold tailWord_1417287
  simp only [CollatzResearch.WordTrace]
  refine ⟨51692703616418727193858115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34461802410945818129238743 51692703616418727193858115)
  ·
    refine ⟨77539055424628090790787173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51692703616418727193858115 77539055424628090790787173)
    ·
      refine ⟨14538572892117767023272595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77539055424628090790787173 14538572892117767023272595)
      ·
        refine ⟨21807859338176650534908893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14538572892117767023272595 21807859338176650534908893)
        ·
          refine ⟨8177947251816243950590835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21807859338176650534908893 8177947251816243950590835)
          ·
            refine ⟨12266920877724365925886253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8177947251816243950590835 12266920877724365925886253)
            ·
              refine ⟨4600095329146637222207345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12266920877724365925886253 4600095329146637222207345)
              ·
                refine ⟨3450071496859977916655509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4600095329146637222207345 3450071496859977916655509)
                ·
                  refine ⟨161722101415311464843227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3450071496859977916655509 161722101415311464843227)
                  ·
                    rfl

theorem cell22_1417287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 6].length) (baseStart_1417287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417287 prefixEnd_1417287 := by exact prefixLift 1417287
  have htrace : WordTrace (prefixWord ++ tailWord_1417287) baseStart_1417287 baseEnd_1417287 := by
    simpa [prefixWord, tailWord_1417287, baseEnd_1417287] using wordTrace_append hprefix tailTrace_1417287
  have hstable : (prefixWord ++ tailWord_1417287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417287).length < 2 ^ (prefixWord ++ tailWord_1417287).sum := by decide
  have hdescent : baseEnd_1417287 < baseStart_1417287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417304 : List Nat := [2, 1, 2, 2, 1, 4, 1, 5, 4]
def baseStart_1417304 : Nat := 118140960795 + 1417304 * 2 ^ 59
def prefixEnd_1417304 : Nat := 4983230072969 + 3 ^ 40 * 1417304 * 2
def baseEnd_1417304 : Nat := 161724041231117338951543

theorem tailTrace_1417304 : CollatzResearch.WordTrace tailWord_1417304 prefixEnd_1417304 161724041231117338951543 := by
  unfold tailWord_1417304
  simp only [CollatzResearch.WordTrace]
  refine ⟨25846661828678569548613483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34462215771571426064817977 25846661828678569548613483)
  ·
    refine ⟨38769992743017854322920225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25846661828678569548613483 38769992743017854322920225)
    ·
      refine ⟨29077494557263390742190169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38769992743017854322920225 29077494557263390742190169)
      ·
        refine ⟨21808120917947543056642627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29077494557263390742190169 21808120917947543056642627)
        ·
          refine ⟨32712181376921314584963941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21808120917947543056642627 32712181376921314584963941)
          ·
            refine ⟨6133534008172746484680739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32712181376921314584963941 6133534008172746484680739)
            ·
              refine ⟨9200301012259119727021109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6133534008172746484680739 9200301012259119727021109)
              ·
                refine ⟨862528219899292474408229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9200301012259119727021109 862528219899292474408229)
                ·
                  refine ⟨161724041231117338951543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 862528219899292474408229 161724041231117338951543)
                  ·
                    rfl

theorem cell22_1417304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 4].length) (baseStart_1417304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417304 prefixEnd_1417304 := by exact prefixLift 1417304
  have htrace : WordTrace (prefixWord ++ tailWord_1417304) baseStart_1417304 baseEnd_1417304 := by
    simpa [prefixWord, tailWord_1417304, baseEnd_1417304] using wordTrace_append hprefix tailTrace_1417304
  have hstable : (prefixWord ++ tailWord_1417304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417304).length < 2 ^ (prefixWord ++ tailWord_1417304).sum := by decide
  have hdescent : baseEnd_1417304 < baseStart_1417304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417310 : List Nat := [4, 4, 1, 1, 2, 2, 1, 2, 5]
def baseStart_1417310 : Nat := 118140960795 + 1417310 * 2 ^ 59
def prefixEnd_1417310 : Nat := 4983230072969 + 3 ^ 40 * 1417310 * 2
def baseEnd_1417310 : Nat := 161724725871990000401537

theorem tailTrace_1417310 : CollatzResearch.WordTrace tailWord_1417310 prefixEnd_1417310 161724725871990000401537 := by
  unfold tailWord_1417310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6461692811916925265243173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34462361663556934747963589 6461692811916925265243173)
  ·
    refine ⟨1211567402234423487233095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6461692811916925265243173 1211567402234423487233095)
    ·
      refine ⟨1817351103351635230849643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1211567402234423487233095 1817351103351635230849643)
      ·
        refine ⟨2726026655027452846274465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1817351103351635230849643 2726026655027452846274465)
        ·
          refine ⟨2044519991270589634705849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2726026655027452846274465 2044519991270589634705849)
          ·
            refine ⟨1533389993452942226029387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2044519991270589634705849 1533389993452942226029387)
            ·
              refine ⟨2300084990179413339044081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1533389993452942226029387 2300084990179413339044081)
              ·
                refine ⟨1725063742634560004283061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2300084990179413339044081 1725063742634560004283061)
                ·
                  refine ⟨161724725871990000401537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1725063742634560004283061 161724725871990000401537)
                  ·
                    rfl

theorem cell22_1417310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_1417310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417310 prefixEnd_1417310 := by exact prefixLift 1417310
  have htrace : WordTrace (prefixWord ++ tailWord_1417310) baseStart_1417310 baseEnd_1417310 := by
    simpa [prefixWord, tailWord_1417310, baseEnd_1417310] using wordTrace_append hprefix tailTrace_1417310
  have hstable : (prefixWord ++ tailWord_1417310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417310).length < 2 ^ (prefixWord ++ tailWord_1417310).sum := by decide
  have hdescent : baseEnd_1417310 < baseStart_1417310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417319 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 4, 3]
def baseStart_1417319 : Nat := 118140960795 + 1417319 * 2 ^ 59
def prefixEnd_1417319 : Nat := 4983230072969 + 3 ^ 40 * 1417319 * 2
def baseEnd_1417319 : Nat := 485177258499896977729583

theorem tailTrace_1417319 : CollatzResearch.WordTrace tailWord_1417319 prefixEnd_1417319 485177258499896977729583 := by
  unfold tailWord_1417319
  simp only [CollatzResearch.WordTrace]
  refine ⟨51693870752302796659023011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34462580501535197772682007 51693870752302796659023011)
  ·
    refine ⟨77540806128454194988534517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51693870752302796659023011 77540806128454194988534517)
    ·
      refine ⟨7269450574542580780175111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77540806128454194988534517 7269450574542580780175111)
      ·
        refine ⟨10904175861813871170262667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7269450574542580780175111 10904175861813871170262667)
        ·
          refine ⟨16356263792720806755394001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10904175861813871170262667 16356263792720806755394001)
          ·
            refine ⟨12267197844540605066545501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16356263792720806755394001 12267197844540605066545501)
            ·
              refine ⟨4600199191702726899954563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12267197844540605066545501 4600199191702726899954563)
              ·
                refine ⟨6900298787554090349931845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4600199191702726899954563 6900298787554090349931845)
                ·
                  refine ⟨1293806022666391940612221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6900298787554090349931845 1293806022666391940612221)
                  ·
                    refine ⟨485177258499896977729583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1293806022666391940612221 485177258499896977729583)
                    ·
                      rfl

theorem cell22_1417319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_1417319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417319 prefixEnd_1417319 := by exact prefixLift 1417319
  have htrace : WordTrace (prefixWord ++ tailWord_1417319) baseStart_1417319 baseEnd_1417319 := by
    simpa [prefixWord, tailWord_1417319, baseEnd_1417319] using wordTrace_append hprefix tailTrace_1417319
  have hstable : (prefixWord ++ tailWord_1417319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417319).length < 2 ^ (prefixWord ++ tailWord_1417319).sum := by decide
  have hdescent : baseEnd_1417319 < baseStart_1417319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417334 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_1417334 : Nat := 118140960795 + 1417334 * 2 ^ 59
def prefixEnd_1417334 : Nat := 4983230072969 + 3 ^ 40 * 1417334 * 2
def baseEnd_1417334 : Nat := 485182393306441938604537

theorem tailTrace_1417334 : CollatzResearch.WordTrace tailWord_1417334 prefixEnd_1417334 485182393306441938604537 := by
  unfold tailWord_1417334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3230901115453028388801191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34462945231498969480546037 3230901115453028388801191)
  ·
    refine ⟨4846351673179542583201787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3230901115453028388801191 4846351673179542583201787)
    ·
      refine ⟨7269527509769313874802681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4846351673179542583201787 7269527509769313874802681)
      ·
        refine ⟨5452145632326985406102011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7269527509769313874802681 5452145632326985406102011)
        ·
          refine ⟨8178218448490478109153017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5452145632326985406102011 8178218448490478109153017)
          ·
            refine ⟨6133663836367858581864763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8178218448490478109153017 6133663836367858581864763)
            ·
              refine ⟨9200495754551787872797145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6133663836367858581864763 9200495754551787872797145)
              ·
                refine ⟨6900371815913840904597859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9200495754551787872797145 6900371815913840904597859)
                ·
                  refine ⟨10350557723870761356896789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6900371815913840904597859 10350557723870761356896789)
                  ·
                    refine ⟨485182393306441938604537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10350557723870761356896789 485182393306441938604537)
                    ·
                      rfl

theorem cell22_1417334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_1417334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417334 prefixEnd_1417334 := by exact prefixLift 1417334
  have htrace : WordTrace (prefixWord ++ tailWord_1417334) baseStart_1417334 baseEnd_1417334 := by
    simpa [prefixWord, tailWord_1417334, baseEnd_1417334] using wordTrace_append hprefix tailTrace_1417334
  have hstable : (prefixWord ++ tailWord_1417334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417334).length < 2 ^ (prefixWord ++ tailWord_1417334).sum := by decide
  have hdescent : baseEnd_1417334 < baseStart_1417334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417349 : List Nat := [1, 3, 1, 1, 5, 1, 4, 6]
def baseStart_1417349 : Nat := 118140960795 + 1417349 * 2 ^ 59
def prefixEnd_1417349 : Nat := 4983230072969 + 3 ^ 40 * 1417349 * 2
def baseEnd_1417349 : Nat := 53909725345887433275499

theorem tailTrace_1417349 : CollatzResearch.WordTrace tailWord_1417349 prefixEnd_1417349 53909725345887433275499 := by
  unfold tailWord_1417349
  simp only [CollatzResearch.WordTrace]
  refine ⟨51694964942194111782615101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34463309961462741188410067 51694964942194111782615101)
  ·
    refine ⟨19385611853322791918480663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51694964942194111782615101 19385611853322791918480663)
    ·
      refine ⟨29078417779984187877720995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19385611853322791918480663 29078417779984187877720995)
      ·
        refine ⟨43617626669976281816581493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29078417779984187877720995 43617626669976281816581493)
        ·
          refine ⟨4089152500310276420304515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43617626669976281816581493 4089152500310276420304515)
          ·
            refine ⟨6133728750465414630456773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4089152500310276420304515 6133728750465414630456773)
            ·
              refine ⟨1150074140712265243210645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6133728750465414630456773 1150074140712265243210645)
              ·
                refine ⟨53909725345887433275499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1150074140712265243210645 53909725345887433275499)
                ·
                  rfl

theorem cell22_1417349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 6].length) (baseStart_1417349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417349 prefixEnd_1417349 := by exact prefixLift 1417349
  have htrace : WordTrace (prefixWord ++ tailWord_1417349) baseStart_1417349 baseEnd_1417349 := by
    simpa [prefixWord, tailWord_1417349, baseEnd_1417349] using wordTrace_append hprefix tailTrace_1417349
  have hstable : (prefixWord ++ tailWord_1417349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417349).length < 2 ^ (prefixWord ++ tailWord_1417349).sum := by decide
  have hdescent : baseEnd_1417349 < baseStart_1417349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417394 : List Nat := [3, 2, 1, 1, 1, 3, 3, 3, 5]
def baseStart_1417394 : Nat := 118140960795 + 1417394 * 2 ^ 59
def prefixEnd_1417394 : Nat := 4983230072969 + 3 ^ 40 * 1417394 * 2
def baseEnd_1417394 : Nat := 161734310844207260701451

theorem tailTrace_1417394 : CollatzResearch.WordTrace tailWord_1417394 prefixEnd_1417394 161734310844207260701451 := by
  unfold tailWord_1417394
  simp only [CollatzResearch.WordTrace]
  refine ⟨12924151556757771117000809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34464404151354056312002157 12924151556757771117000809)
  ·
    refine ⟨9693113667568328337750607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12924151556757771117000809 9693113667568328337750607)
    ·
      refine ⟨14539670501352492506625911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9693113667568328337750607 14539670501352492506625911)
      ·
        refine ⟨21809505752028738759938867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14539670501352492506625911 21809505752028738759938867)
        ·
          refine ⟨32714258628043108139908301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21809505752028738759938867 32714258628043108139908301)
          ·
            refine ⟨12267846985516165552465613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32714258628043108139908301 12267846985516165552465613)
            ·
              refine ⟨4600442619568562082174605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12267846985516165552465613 4600442619568562082174605)
              ·
                refine ⟨1725165982338210780815477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4600442619568562082174605 1725165982338210780815477)
                ·
                  refine ⟨161734310844207260701451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1725165982338210780815477 161734310844207260701451)
                  ·
                    rfl

theorem cell22_1417394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_1417394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417394 prefixEnd_1417394 := by exact prefixLift 1417394
  have htrace : WordTrace (prefixWord ++ tailWord_1417394) baseStart_1417394 baseEnd_1417394 := by
    simpa [prefixWord, tailWord_1417394, baseEnd_1417394] using wordTrace_append hprefix tailTrace_1417394
  have hstable : (prefixWord ++ tailWord_1417394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417394).length < 2 ^ (prefixWord ++ tailWord_1417394).sum := by decide
  have hdescent : baseEnd_1417394 < baseStart_1417394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417516 : List Nat := [2, 2, 1, 1, 1, 3, 4, 2, 3, 3]
def baseStart_1417516 : Nat := 118140960795 + 1417516 * 2 ^ 59
def prefixEnd_1417516 : Nat := 4983230072969 + 3 ^ 40 * 1417516 * 2
def baseEnd_1417516 : Nat := 485244695625854130553979

theorem tailTrace_1417516 : CollatzResearch.WordTrace tailWord_1417516 prefixEnd_1417516 485244695625854130553979 := by
  unfold tailWord_1417516
  simp only [CollatzResearch.WordTrace]
  refine ⟨25850527966294549651972201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34467370621726066202629601 25850527966294549651972201)
  ·
    refine ⟨19387895974720912238979151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25850527966294549651972201 19387895974720912238979151)
    ·
      refine ⟨29081843962081368358468727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19387895974720912238979151 29081843962081368358468727)
      ·
        refine ⟨43622765943122052537703091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29081843962081368358468727 43622765943122052537703091)
        ·
          refine ⟨65434148914683078806554637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43622765943122052537703091 65434148914683078806554637)
          ·
            refine ⟨24537805843006154552457989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65434148914683078806554637 24537805843006154552457989)
            ·
              refine ⟨4600838595563653978585873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24537805843006154552457989 4600838595563653978585873)
              ·
                refine ⟨3450628946672740483939405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4600838595563653978585873 3450628946672740483939405)
                ·
                  refine ⟨1293985855002277681477277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3450628946672740483939405 1293985855002277681477277)
                  ·
                    refine ⟨485244695625854130553979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1293985855002277681477277 485244695625854130553979)
                    ·
                      rfl

theorem cell22_1417516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 3].length) (baseStart_1417516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417516 prefixEnd_1417516 := by exact prefixLift 1417516
  have htrace : WordTrace (prefixWord ++ tailWord_1417516) baseStart_1417516 baseEnd_1417516 := by
    simpa [prefixWord, tailWord_1417516, baseEnd_1417516] using wordTrace_append hprefix tailTrace_1417516
  have hstable : (prefixWord ++ tailWord_1417516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417516).length < 2 ^ (prefixWord ++ tailWord_1417516).sum := by decide
  have hdescent : baseEnd_1417516 < baseStart_1417516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417518 : List Nat := [4, 1, 3, 3, 1, 1, 1, 8]
def baseStart_1417518 : Nat := 118140960795 + 1417518 * 2 ^ 59
def prefixEnd_1417518 : Nat := 4983230072969 + 3 ^ 40 * 1417518 * 2
def baseEnd_1417518 : Nat := 53916153362969643555997

theorem tailTrace_1417518 : CollatzResearch.WordTrace tailWord_1417518 prefixEnd_1417518 53916153362969643555997 := by
  unfold tailWord_1417518
  simp only [CollatzResearch.WordTrace]
  refine ⟨6462641109822731705689651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34467419252387902430344805 6462641109822731705689651)
  ·
    refine ⟨9693961664734097558534477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6462641109822731705689651 9693961664734097558534477)
    ·
      refine ⟨3635235624275286584450429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9693961664734097558534477 3635235624275286584450429)
      ·
        refine ⟨1363213359103232469168911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3635235624275286584450429 1363213359103232469168911)
        ·
          refine ⟨2044820038654848703753367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1363213359103232469168911 2044820038654848703753367)
          ·
            refine ⟨3067230057982273055630051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2044820038654848703753367 3067230057982273055630051)
            ·
              refine ⟨4600845086973409583445077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3067230057982273055630051 4600845086973409583445077)
              ·
                refine ⟨53916153362969643555997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4600845086973409583445077 53916153362969643555997)
                ·
                  rfl

theorem cell22_1417518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_1417518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417518 prefixEnd_1417518 := by exact prefixLift 1417518
  have htrace : WordTrace (prefixWord ++ tailWord_1417518) baseStart_1417518 baseEnd_1417518 := by
    simpa [prefixWord, tailWord_1417518, baseEnd_1417518] using wordTrace_append hprefix tailTrace_1417518
  have hstable : (prefixWord ++ tailWord_1417518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417518).length < 2 ^ (prefixWord ++ tailWord_1417518).sum := by decide
  have hdescent : baseEnd_1417518 < baseStart_1417518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417544 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 4, 5]
def baseStart_1417544 : Nat := 118140960795 + 1417544 * 2 ^ 59
def prefixEnd_1417544 : Nat := 4983230072969 + 3 ^ 40 * 1417544 * 2
def baseEnd_1417544 : Nat := 485254280598071390853893

theorem tailTrace_1417544 : CollatzResearch.WordTrace tailWord_1417544 prefixEnd_1417544 485254280598071390853893 := by
  unfold tailWord_1417544
  simp only [CollatzResearch.WordTrace]
  refine ⟨25851038588243830042981843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34468051450991773390642457 25851038588243830042981843)
  ·
    refine ⟨38776557882365745064472765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25851038588243830042981843 38776557882365745064472765)
    ·
      refine ⟨14541209205887154399177287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38776557882365745064472765 14541209205887154399177287)
      ·
        refine ⟨21811813808830731598765931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14541209205887154399177287 21811813808830731598765931)
        ·
          refine ⟨32717720713246097398148897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21811813808830731598765931 32717720713246097398148897)
          ·
            refine ⟨24538290534934573048611673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32717720713246097398148897 24538290534934573048611673)
            ·
              refine ⟨18403717901200929786458755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24538290534934573048611673 18403717901200929786458755)
              ·
                refine ⟨27605576851801394679688133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18403717901200929786458755 27605576851801394679688133)
                ·
                  refine ⟨5176045659712761502441525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27605576851801394679688133 5176045659712761502441525)
                  ·
                    refine ⟨485254280598071390853893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5176045659712761502441525 485254280598071390853893)
                    ·
                      rfl

theorem cell22_1417544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_1417544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417544 prefixEnd_1417544 := by exact prefixLift 1417544
  have htrace : WordTrace (prefixWord ++ tailWord_1417544) baseStart_1417544 baseEnd_1417544 := by
    simpa [prefixWord, tailWord_1417544, baseEnd_1417544] using wordTrace_append hprefix tailTrace_1417544
  have hstable : (prefixWord ++ tailWord_1417544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417544).length < 2 ^ (prefixWord ++ tailWord_1417544).sum := by decide
  have hdescent : baseEnd_1417544 < baseStart_1417544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417608 : List Nat := [2, 1, 3, 3, 1, 1, 3, 4, 4]
def baseStart_1417608 : Nat := 118140960795 + 1417608 * 2 ^ 59
def prefixEnd_1417608 : Nat := 4983230072969 + 3 ^ 40 * 1417608 * 2
def baseEnd_1417608 : Nat := 161758729701998852417899

theorem tailTrace_1417608 : CollatzResearch.WordTrace tailWord_1417608 prefixEnd_1417608 161758729701998852417899 := by
  unfold tailWord_1417608
  simp only [CollatzResearch.WordTrace]
  refine ⟨25852205724127899508146739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34469607632170532677528985 25852205724127899508146739)
  ·
    refine ⟨38778308586191849262220109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25852205724127899508146739 38778308586191849262220109)
    ·
      refine ⟨14541865719821943473332541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38778308586191849262220109 14541865719821943473332541)
      ·
        refine ⟨5453199644933228802499703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14541865719821943473332541 5453199644933228802499703)
        ·
          refine ⟨8179799467399843203749555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5453199644933228802499703 8179799467399843203749555)
          ·
            refine ⟨12269699201099764805624333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8179799467399843203749555 12269699201099764805624333)
            ·
              refine ⟨4601137200412411802109125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12269699201099764805624333 4601137200412411802109125)
              ·
                refine ⟨862713225077327212895461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4601137200412411802109125 862713225077327212895461)
                ·
                  refine ⟨161758729701998852417899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 862713225077327212895461 161758729701998852417899)
                  ·
                    rfl

theorem cell22_1417608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 4].length) (baseStart_1417608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417608 prefixEnd_1417608 := by exact prefixLift 1417608
  have htrace : WordTrace (prefixWord ++ tailWord_1417608) baseStart_1417608 baseEnd_1417608 := by
    simpa [prefixWord, tailWord_1417608, baseEnd_1417608] using wordTrace_append hprefix tailTrace_1417608
  have hstable : (prefixWord ++ tailWord_1417608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417608).length < 2 ^ (prefixWord ++ tailWord_1417608).sum := by decide
  have hdescent : baseEnd_1417608 < baseStart_1417608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417623 : List Nat := [1, 1, 3, 3, 1, 1, 4, 3, 2, 3]
def baseStart_1417623 : Nat := 118140960795 + 1417623 * 2 ^ 59
def prefixEnd_1417623 : Nat := 4983230072969 + 3 ^ 40 * 1417623 * 2
def baseEnd_1417623 : Nat := 485281323912541518128651

theorem tailTrace_1417623 : CollatzResearch.WordTrace tailWord_1417623 prefixEnd_1417623 485281323912541518128651 := by
  unfold tailWord_1417623
  simp only [CollatzResearch.WordTrace]
  refine ⟨51704958543201456578089523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34469972362134304385393015 51704958543201456578089523)
  ·
    refine ⟨77557437814802184867134285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51704958543201456578089523 77557437814802184867134285)
    ·
      refine ⟨29084039180550819325175357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77557437814802184867134285 29084039180550819325175357)
      ·
        refine ⟨10906514692706557246940759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29084039180550819325175357 10906514692706557246940759)
        ·
          refine ⟨16359772039059835870411139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10906514692706557246940759 16359772039059835870411139)
          ·
            refine ⟨24539658058589753805616709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16359772039059835870411139 24539658058589753805616709)
            ·
              refine ⟨4601185885985578838553133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24539658058589753805616709 4601185885985578838553133)
              ·
                refine ⟨1725444707244592064457425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4601185885985578838553133 1725444707244592064457425)
                ·
                  refine ⟨1294083530433444048343069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1725444707244592064457425 1294083530433444048343069)
                  ·
                    refine ⟨485281323912541518128651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1294083530433444048343069 485281323912541518128651)
                    ·
                      rfl

theorem cell22_1417623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 3].length) (baseStart_1417623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417623 prefixEnd_1417623 := by exact prefixLift 1417623
  have htrace : WordTrace (prefixWord ++ tailWord_1417623) baseStart_1417623 baseEnd_1417623 := by
    simpa [prefixWord, tailWord_1417623, baseEnd_1417623] using wordTrace_append hprefix tailTrace_1417623
  have hstable : (prefixWord ++ tailWord_1417623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417623).length < 2 ^ (prefixWord ++ tailWord_1417623).sum := by decide
  have hdescent : baseEnd_1417623 < baseStart_1417623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417681 : List Nat := [1, 2, 2, 1, 2, 1, 1, 7, 5]
def baseStart_1417681 : Nat := 118140960795 + 1417681 * 2 ^ 59
def prefixEnd_1417681 : Nat := 4983230072969 + 3 ^ 40 * 1417681 * 2
def baseEnd_1417681 : Nat := 161767059499282900059491

theorem tailTrace_1417681 : CollatzResearch.WordTrace tailWord_1417681 prefixEnd_1417681 161767059499282900059491 := by
  unfold tailWord_1417681
  simp only [CollatzResearch.WordTrace]
  refine ⟨51707073976991332483700897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34471382651327554989133931 51707073976991332483700897)
  ·
    refine ⟨38780305482743499362775673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51707073976991332483700897 38780305482743499362775673)
    ·
      refine ⟨29085229112057624522081755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38780305482743499362775673 29085229112057624522081755)
      ·
        refine ⟨43627843668086436783122633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29085229112057624522081755 43627843668086436783122633)
        ·
          refine ⟨32720882751064827587341975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43627843668086436783122633 32720882751064827587341975)
          ·
            refine ⟨49081324126597241381012963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32720882751064827587341975 49081324126597241381012963)
            ·
              refine ⟨73621986189895862071519445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49081324126597241381012963 73621986189895862071519445)
              ·
                refine ⟨1725515301325684267301237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 73621986189895862071519445 1725515301325684267301237)
                ·
                  refine ⟨161767059499282900059491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1725515301325684267301237 161767059499282900059491)
                  ·
                    rfl

theorem cell22_1417681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 5].length) (baseStart_1417681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417681 prefixEnd_1417681 := by exact prefixLift 1417681
  have htrace : WordTrace (prefixWord ++ tailWord_1417681) baseStart_1417681 baseEnd_1417681 := by
    simpa [prefixWord, tailWord_1417681, baseEnd_1417681] using wordTrace_append hprefix tailTrace_1417681
  have hstable : (prefixWord ++ tailWord_1417681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417681).length < 2 ^ (prefixWord ++ tailWord_1417681).sum := by decide
  have hdescent : baseEnd_1417681 < baseStart_1417681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417711 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 5, 4]
def baseStart_1417711 : Nat := 118140960795 + 1417711 * 2 ^ 59
def prefixEnd_1417711 : Nat := 4983230072969 + 3 ^ 40 * 1417711 * 2
def baseEnd_1417711 : Nat := 485311448110938621928381

theorem tailTrace_1417711 : CollatzResearch.WordTrace tailWord_1417711 prefixEnd_1417711 485311448110938621928381 := by
  unfold tailWord_1417711
  simp only [CollatzResearch.WordTrace]
  refine ⟨51708168166882647607292987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34472112111255098404861991 51708168166882647607292987)
  ·
    refine ⟨77562252250323971410939481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51708168166882647607292987 77562252250323971410939481)
    ·
      refine ⟨58171689187742978558204611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77562252250323971410939481 58171689187742978558204611)
      ·
        refine ⟨87257533781614467837306917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58171689187742978558204611 87257533781614467837306917)
        ·
          refine ⟨16360787584052712719495047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87257533781614467837306917 16360787584052712719495047)
          ·
            refine ⟨24541181376079069079242571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16360787584052712719495047 24541181376079069079242571)
            ·
              refine ⟨36811772064118603618863857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24541181376079069079242571 36811772064118603618863857)
              ·
                refine ⟨27608829048088952714147893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36811772064118603618863857 27608829048088952714147893)
                ·
                  refine ⟨2588327723258339316951365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27608829048088952714147893 2588327723258339316951365)
                  ·
                    refine ⟨485311448110938621928381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2588327723258339316951365 485311448110938621928381)
                    ·
                      rfl

theorem cell22_1417711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 4].length) (baseStart_1417711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417711 prefixEnd_1417711 := by exact prefixLift 1417711
  have htrace : WordTrace (prefixWord ++ tailWord_1417711) baseStart_1417711 baseEnd_1417711 := by
    simpa [prefixWord, tailWord_1417711, baseEnd_1417711] using wordTrace_append hprefix tailTrace_1417711
  have hstable : (prefixWord ++ tailWord_1417711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417711).length < 2 ^ (prefixWord ++ tailWord_1417711).sum := by decide
  have hdescent : baseEnd_1417711 < baseStart_1417711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417732 : List Nat := [2, 3, 2, 3, 1, 3, 2, 1, 5]
def baseStart_1417732 : Nat := 118140960795 + 1417732 * 2 ^ 59
def prefixEnd_1417732 : Nat := 4983230072969 + 3 ^ 40 * 1417732 * 2
def baseEnd_1417732 : Nat := 161772878946700522384439

theorem tailTrace_1417732 : CollatzResearch.WordTrace tailWord_1417732 prefixEnd_1417732 161772878946700522384439 := by
  unfold tailWord_1417732
  simp only [CollatzResearch.WordTrace]
  refine ⟨25854467049903284096903725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34472622733204378795871633 25854467049903284096903725)
  ·
    refine ⟨9695425143713731536338897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25854467049903284096903725 9695425143713731536338897)
    ·
      refine ⟨7271568857785298652254173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9695425143713731536338897 7271568857785298652254173)
      ·
        refine ⟨2726838321669486994595315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7271568857785298652254173 2726838321669486994595315)
        ·
          refine ⟨4090257482504230491892973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2726838321669486994595315 4090257482504230491892973)
          ·
            refine ⟨1533846555939086434459865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4090257482504230491892973 1533846555939086434459865)
            ·
              refine ⟨1150384916954314825844899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1533846555939086434459865 1150384916954314825844899)
              ·
                refine ⟨1725577375431472238767349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1150384916954314825844899 1725577375431472238767349)
                ·
                  refine ⟨161772878946700522384439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1725577375431472238767349 161772878946700522384439)
                  ·
                    rfl

theorem cell22_1417732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_1417732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417732 prefixEnd_1417732 := by exact prefixLift 1417732
  have htrace : WordTrace (prefixWord ++ tailWord_1417732) baseStart_1417732 baseEnd_1417732 := by
    simpa [prefixWord, tailWord_1417732, baseEnd_1417732] using wordTrace_append hprefix tailTrace_1417732
  have hstable : (prefixWord ++ tailWord_1417732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417732).length < 2 ^ (prefixWord ++ tailWord_1417732).sum := by decide
  have hdescent : baseEnd_1417732 < baseStart_1417732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417788 : List Nat := [2, 2, 2, 2, 3, 1, 3, 7]
def baseStart_1417788 : Nat := 118140960795 + 1417788 * 2 ^ 59
def prefixEnd_1417788 : Nat := 4983230072969 + 3 ^ 40 * 1417788 * 2
def baseEnd_1417788 : Nat := 53926422976059565305905

theorem tailTrace_1417788 : CollatzResearch.WordTrace tailWord_1417788 prefixEnd_1417788 53926422976059565305905 := by
  unfold tailWord_1417788
  simp only [CollatzResearch.WordTrace]
  refine ⟨25855488293801844878923009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34473984391735793171897345 25855488293801844878923009)
  ·
    refine ⟨19391616220351383659192257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25855488293801844878923009 19391616220351383659192257)
    ·
      refine ⟨14543712165263537744394193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19391616220351383659192257 14543712165263537744394193)
      ·
        refine ⟨10907784123947653308295645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14543712165263537744394193 10907784123947653308295645)
        ·
          refine ⟨4090419046480369990610867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10907784123947653308295645 4090419046480369990610867)
          ·
            refine ⟨6135628569720554985916301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4090419046480369990610867 6135628569720554985916301)
            ·
              refine ⟨2300860713645208119718613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6135628569720554985916301 2300860713645208119718613)
              ·
                refine ⟨53926422976059565305905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2300860713645208119718613 53926422976059565305905)
                ·
                  rfl

theorem cell22_1417788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 7].length) (baseStart_1417788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417788 prefixEnd_1417788 := by exact prefixLift 1417788
  have htrace : WordTrace (prefixWord ++ tailWord_1417788) baseStart_1417788 baseEnd_1417788 := by
    simpa [prefixWord, tailWord_1417788, baseEnd_1417788] using wordTrace_append hprefix tailTrace_1417788
  have hstable : (prefixWord ++ tailWord_1417788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417788).length < 2 ^ (prefixWord ++ tailWord_1417788).sum := by decide
  have hdescent : baseEnd_1417788 < baseStart_1417788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417803 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 5, 3]
def baseStart_1417803 : Nat := 118140960795 + 1417803 * 2 ^ 59
def prefixEnd_1417803 : Nat := 4983230072969 + 3 ^ 40 * 1417803 * 2
def baseEnd_1417803 : Nat := 485342941591081048628099

theorem tailTrace_1417803 : CollatzResearch.WordTrace tailWord_1417803 prefixEnd_1417803 485342941591081048628099 := by
  unfold tailWord_1417803
  simp only [CollatzResearch.WordTrace]
  refine ⟨51711523682549347319642063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34474349121699564879761375 51711523682549347319642063)
  ·
    refine ⟨77567285523824020979463095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51711523682549347319642063 77567285523824020979463095)
    ·
      refine ⟨116350928285736031469194643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77567285523824020979463095 116350928285736031469194643)
      ·
        refine ⟨174526392428604047203791965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116350928285736031469194643 174526392428604047203791965)
        ·
          refine ⟨65447397160726517701421987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174526392428604047203791965 65447397160726517701421987)
          ·
            refine ⟨98171095741089776552132981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65447397160726517701421987 98171095741089776552132981)
            ·
              refine ⟨9203540225727166551762467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98171095741089776552132981 9203540225727166551762467)
              ·
                refine ⟨13805310338590749827643701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9203540225727166551762467 13805310338590749827643701)
                ·
                  refine ⟨1294247844242882796341597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13805310338590749827643701 1294247844242882796341597)
                  ·
                    refine ⟨485342941591081048628099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1294247844242882796341597 485342941591081048628099)
                    ·
                      rfl

theorem cell22_1417803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 3].length) (baseStart_1417803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417803 prefixEnd_1417803 := by exact prefixLift 1417803
  have htrace : WordTrace (prefixWord ++ tailWord_1417803) baseStart_1417803 baseEnd_1417803 := by
    simpa [prefixWord, tailWord_1417803, baseEnd_1417803] using wordTrace_append hprefix tailTrace_1417803
  have hstable : (prefixWord ++ tailWord_1417803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417803).length < 2 ^ (prefixWord ++ tailWord_1417803).sum := by decide
  have hdescent : baseEnd_1417803 < baseStart_1417803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417826 : List Nat := [3, 3, 2, 3, 1, 2, 1, 2, 2, 3]
def baseStart_1417826 : Nat := 118140960795 + 1417826 * 2 ^ 59
def prefixEnd_1417826 : Nat := 4983230072969 + 3 ^ 40 * 1417826 * 2
def baseEnd_1417826 : Nat := 485350814961116655303029

theorem tailTrace_1417826 : CollatzResearch.WordTrace tailWord_1417826 prefixEnd_1417826 485350814961116655303029 := by
  unfold tailWord_1417826
  simp only [CollatzResearch.WordTrace]
  refine ⟨12928090640366505561932333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34474908374310681498486221 12928090640366505561932333)
  ·
    refine ⟨4848033990137439585724625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12928090640366505561932333 4848033990137439585724625)
    ·
      refine ⟨3636025492603079689293469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4848033990137439585724625 3636025492603079689293469)
      ·
        refine ⟨1363509559726154883485051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3636025492603079689293469 1363509559726154883485051)
        ·
          refine ⟨2045264339589232325227577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1363509559726154883485051 2045264339589232325227577)
          ·
            refine ⟨1533948254691924243920683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2045264339589232325227577 1533948254691924243920683)
            ·
              refine ⟨2300922382037886365881025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1533948254691924243920683 2300922382037886365881025)
              ·
                refine ⟨1725691786528414774410769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2300922382037886365881025 1725691786528414774410769)
                ·
                  refine ⟨1294268839896311080808077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1725691786528414774410769 1294268839896311080808077)
                  ·
                    refine ⟨485350814961116655303029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1294268839896311080808077 485350814961116655303029)
                    ·
                      rfl

theorem cell22_1417826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_1417826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417826 prefixEnd_1417826 := by exact prefixLift 1417826
  have htrace : WordTrace (prefixWord ++ tailWord_1417826) baseStart_1417826 baseEnd_1417826 := by
    simpa [prefixWord, tailWord_1417826, baseEnd_1417826] using wordTrace_append hprefix tailTrace_1417826
  have hstable : (prefixWord ++ tailWord_1417826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417826).length < 2 ^ (prefixWord ++ tailWord_1417826).sum := by decide
  have hdescent : baseEnd_1417826 < baseStart_1417826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417837 : List Nat := [1, 5, 1, 1, 3, 2, 2, 1, 3, 3]
def baseStart_1417837 : Nat := 118140960795 + 1417837 * 2 ^ 59
def prefixEnd_1417837 : Nat := 4983230072969 + 3 ^ 40 * 1417837 * 2
def baseEnd_1417837 : Nat := 485354580485916293277995

theorem tailTrace_1417837 : CollatzResearch.WordTrace tailWord_1417837 prefixEnd_1417837 485354580485916293277995 := by
  unfold tailWord_1417837
  simp only [CollatzResearch.WordTrace]
  refine ⟨51712763764426171126379765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34475175842950780750919843 51712763764426171126379765)
  ·
    refine ⟨4848071602914953543098103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51712763764426171126379765 4848071602914953543098103)
    ·
      refine ⟨7272107404372430314647155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4848071602914953543098103 7272107404372430314647155)
      ·
        refine ⟨10908161106558645471970733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7272107404372430314647155 10908161106558645471970733)
        ·
          refine ⟨4090560414959492051989025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10908161106558645471970733 4090560414959492051989025)
          ·
            refine ⟨3067920311219619038991769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4090560414959492051989025 3067920311219619038991769)
            ·
              refine ⟨2300940233414714279243827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3067920311219619038991769 2300940233414714279243827)
              ·
                refine ⟨3451410350122071418865741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2300940233414714279243827 3451410350122071418865741)
                ·
                  refine ⟨1294278881295776782074653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3451410350122071418865741 1294278881295776782074653)
                  ·
                    refine ⟨485354580485916293277995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1294278881295776782074653 485354580485916293277995)
                    ·
                      rfl

theorem cell22_1417837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_1417837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417837 prefixEnd_1417837 := by exact prefixLift 1417837
  have htrace : WordTrace (prefixWord ++ tailWord_1417837) baseStart_1417837 baseEnd_1417837 := by
    simpa [prefixWord, tailWord_1417837, baseEnd_1417837] using wordTrace_append hprefix tailTrace_1417837
  have hstable : (prefixWord ++ tailWord_1417837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417837).length < 2 ^ (prefixWord ++ tailWord_1417837).sum := by decide
  have hdescent : baseEnd_1417837 < baseStart_1417837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417880 : List Nat := [2, 1, 2, 4, 1, 1, 1, 5, 1, 4]
def baseStart_1417880 : Nat := 118140960795 + 1417880 * 2 ^ 59
def prefixEnd_1417880 : Nat := 4983230072969 + 3 ^ 40 * 1417880 * 2
def baseEnd_1417880 : Nat := 485369300264678514452863

theorem tailTrace_1417880 : CollatzResearch.WordTrace tailWord_1417880 prefixEnd_1417880 485369300264678514452863 := by
  unfold tailWord_1417880
  simp only [CollatzResearch.WordTrace]
  refine ⟨25857166051635194735097547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34476221402180259646796729 25857166051635194735097547)
  ·
    refine ⟨38785749077452792102646321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25857166051635194735097547 38785749077452792102646321)
    ·
      refine ⟨29089311808089594076984741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38785749077452792102646321 29089311808089594076984741)
      ·
        refine ⟨5454245964016798889434639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29089311808089594076984741 5454245964016798889434639)
        ·
          refine ⟨8181368946025198334151959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5454245964016798889434639 8181368946025198334151959)
          ·
            refine ⟨12272053419037797501227939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8181368946025198334151959 12272053419037797501227939)
            ·
              refine ⟨18408080128556696251841909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12272053419037797501227939 18408080128556696251841909)
              ·
                refine ⟨1725757512052190273610179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18408080128556696251841909 1725757512052190273610179)
                ·
                  refine ⟨2588636268078285410415269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1725757512052190273610179 2588636268078285410415269)
                  ·
                    refine ⟨485369300264678514452863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2588636268078285410415269 485369300264678514452863)
                    ·
                      rfl

theorem cell22_1417880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_1417880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417880 prefixEnd_1417880 := by exact prefixLift 1417880
  have htrace : WordTrace (prefixWord ++ tailWord_1417880) baseStart_1417880 baseEnd_1417880 := by
    simpa [prefixWord, tailWord_1417880, baseEnd_1417880] using wordTrace_append hprefix tailTrace_1417880
  have hstable : (prefixWord ++ tailWord_1417880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417880).length < 2 ^ (prefixWord ++ tailWord_1417880).sum := by decide
  have hdescent : baseEnd_1417880 < baseStart_1417880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417940 : List Nat := [2, 4, 1, 3, 2, 10]
def baseStart_1417940 : Nat := 118140960795 + 1417940 * 2 ^ 59
def prefixEnd_1417940 : Nat := 4983230072969 + 3 ^ 40 * 1417940 * 2
def baseEnd_1417940 : Nat := 5992467154208127875959

theorem tailTrace_1417940 : CollatzResearch.WordTrace tailWord_1417940 prefixEnd_1417940 5992467154208127875959 := by
  unfold tailWord_1417940
  simp only [CollatzResearch.WordTrace]
  refine ⟨25858260241526509858689637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34477680322035346478252849 25858260241526509858689637)
  ·
    refine ⟨4848423795286220598504307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25858260241526509858689637 4848423795286220598504307)
    ·
      refine ⟨7272635692929330897756461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4848423795286220598504307 7272635692929330897756461)
      ·
        refine ⟨2727238384848499086658673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7272635692929330897756461 2727238384848499086658673)
        ·
          refine ⟨2045428788636374314994005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2727238384848499086658673 2045428788636374314994005)
          ·
            refine ⟨5992467154208127875959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2045428788636374314994005 5992467154208127875959)
            ·
              rfl

theorem cell22_1417940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 10].length) (baseStart_1417940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417940 prefixEnd_1417940 := by exact prefixLift 1417940
  have htrace : WordTrace (prefixWord ++ tailWord_1417940) baseStart_1417940 baseEnd_1417940 := by
    simpa [prefixWord, tailWord_1417940, baseEnd_1417940] using wordTrace_append hprefix tailTrace_1417940
  have hstable : (prefixWord ++ tailWord_1417940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417940).length < 2 ^ (prefixWord ++ tailWord_1417940).sum := by decide
  have hdescent : baseEnd_1417940 < baseStart_1417940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417983 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 3, 7]
def baseStart_1417983 : Nat := 118140960795 + 1417983 * 2 ^ 59
def prefixEnd_1417983 : Nat := 4983230072969 + 3 ^ 40 * 1417983 * 2
def baseEnd_1417983 : Nat := 485404559269620579127547

theorem tailTrace_1417983 : CollatzResearch.WordTrace tailWord_1417983 prefixEnd_1417983 485404559269620579127547 := by
  unfold tailWord_1417983
  simp only [CollatzResearch.WordTrace]
  refine ⟨51718088821897238061194603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34478725881264825374129735 51718088821897238061194603)
  ·
    refine ⟨77577133232845857091791905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51718088821897238061194603 77577133232845857091791905)
    ·
      refine ⟨58182849924634392818843929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77577133232845857091791905 58182849924634392818843929)
      ·
        refine ⟨43637137443475794614132947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58182849924634392818843929 43637137443475794614132947)
        ·
          refine ⟨65455706165213691921199421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43637137443475794614132947 65455706165213691921199421)
          ·
            refine ⟨24545889811955134470449783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65455706165213691921199421 24545889811955134470449783)
            ·
              refine ⟨36818834717932701705674675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24545889811955134470449783 36818834717932701705674675)
              ·
                refine ⟨55228252076899052558512013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36818834717932701705674675 55228252076899052558512013)
                ·
                  refine ⟨20710594528837144709442005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55228252076899052558512013 20710594528837144709442005)
                  ·
                    refine ⟨485404559269620579127547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20710594528837144709442005 485404559269620579127547)
                    ·
                      rfl

theorem cell22_1417983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_1417983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1417983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1417983 prefixEnd_1417983 := by exact prefixLift 1417983
  have htrace : WordTrace (prefixWord ++ tailWord_1417983) baseStart_1417983 baseEnd_1417983 := by
    simpa [prefixWord, tailWord_1417983, baseEnd_1417983] using wordTrace_append hprefix tailTrace_1417983
  have hstable : (prefixWord ++ tailWord_1417983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417983).length < 2 ^ (prefixWord ++ tailWord_1417983).sum := by decide
  have hdescent : baseEnd_1417983 < baseStart_1417983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418122 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 2, 6]
def baseStart_1418122 : Nat := 118140960795 + 1418122 * 2 ^ 59
def prefixEnd_1418122 : Nat := 4983230072969 + 3 ^ 40 * 1418122 * 2
def baseEnd_1418122 : Nat := 485452141810270549902121

theorem tailTrace_1418122 : CollatzResearch.WordTrace tailWord_1418122 prefixEnd_1418122 485452141810270549902121 := by
  unfold tailWord_1418122
  simp only [CollatzResearch.WordTrace]
  refine ⟨12930789642098416200126155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34482105712262443200336413 12930789642098416200126155)
  ·
    refine ⟨19396184463147624300189233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12930789642098416200126155 19396184463147624300189233)
    ·
      refine ⟨14547138347360718225141925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19396184463147624300189233 14547138347360718225141925)
      ·
        refine ⟨2727588440130134667214111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14547138347360718225141925 2727588440130134667214111)
        ·
          refine ⟨4091382660195202000821167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2727588440130134667214111 4091382660195202000821167)
          ·
            refine ⟨6137073990292803001231751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4091382660195202000821167 6137073990292803001231751)
            ·
              refine ⟨9205610985439204501847627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6137073990292803001231751 9205610985439204501847627)
              ·
                refine ⟨13808416478158806752771441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9205610985439204501847627 13808416478158806752771441)
                ·
                  refine ⟨10356312358619105064578581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13808416478158806752771441 10356312358619105064578581)
                  ·
                    refine ⟨485452141810270549902121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10356312358619105064578581 485452141810270549902121)
                    ·
                      rfl

theorem cell22_1418122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_1418122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1418122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1418122 prefixEnd_1418122 := by exact prefixLift 1418122
  have htrace : WordTrace (prefixWord ++ tailWord_1418122) baseStart_1418122 baseEnd_1418122 := by
    simpa [prefixWord, tailWord_1418122, baseEnd_1418122] using wordTrace_append hprefix tailTrace_1418122
  have hstable : (prefixWord ++ tailWord_1418122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418122).length < 2 ^ (prefixWord ++ tailWord_1418122).sum := by decide
  have hdescent : baseEnd_1418122 < baseStart_1418122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418248 : List Nat := [2, 1, 3, 2, 1, 5, 2, 1, 2, 3]
def baseStart_1418248 : Nat := 118140960795 + 1418248 * 2 ^ 59
def prefixEnd_1418248 : Nat := 4983230072969 + 3 ^ 40 * 1418248 * 2
def baseEnd_1418248 : Nat := 485495274185248221251735

theorem tailTrace_1418248 : CollatzResearch.WordTrace tailWord_1418248 prefixEnd_1418248 485495274185248221251735 := by
  unfold tailWord_1418248
  simp only [CollatzResearch.WordTrace]
  refine ⟨25863877082968594159795699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34485169443958125546394265 25863877082968594159795699)
  ·
    refine ⟨38795815624452891239693549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25863877082968594159795699 38795815624452891239693549)
    ·
      refine ⟨14548430859169834214885081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38795815624452891239693549 14548430859169834214885081)
      ·
        refine ⟨10911323144377375661163811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14548430859169834214885081 10911323144377375661163811)
        ·
          refine ⟨16366984716566063491745717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10911323144377375661163811 16366984716566063491745717)
          ·
            refine ⟨1534404817178068452351161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16366984716566063491745717 1534404817178068452351161)
            ·
              refine ⟨1150803612883551339263371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1534404817178068452351161 1150803612883551339263371)
              ·
                refine ⟨1726205419325327008895057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1150803612883551339263371 1726205419325327008895057)
                ·
                  refine ⟨1294654064493995256671293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1726205419325327008895057 1294654064493995256671293)
                  ·
                    refine ⟨485495274185248221251735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1294654064493995256671293 485495274185248221251735)
                    ·
                      rfl

theorem cell22_1418248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_1418248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1418248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1418248 prefixEnd_1418248 := by exact prefixLift 1418248
  have htrace : WordTrace (prefixWord ++ tailWord_1418248) baseStart_1418248 baseEnd_1418248 := by
    simpa [prefixWord, tailWord_1418248, baseEnd_1418248] using wordTrace_append hprefix tailTrace_1418248
  have hstable : (prefixWord ++ tailWord_1418248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418248).length < 2 ^ (prefixWord ++ tailWord_1418248).sum := by decide
  have hdescent : baseEnd_1418248 < baseStart_1418248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418289 : List Nat := [1, 2, 2, 3, 1, 2, 4, 2, 5]
def baseStart_1418289 : Nat := 118140960795 + 1418289 * 2 ^ 59
def prefixEnd_1418289 : Nat := 4983230072969 + 3 ^ 40 * 1418289 * 2
def baseEnd_1418289 : Nat := 161836436441045926992203

theorem tailTrace_1418289 : CollatzResearch.WordTrace tailWord_1418289 prefixEnd_1418289 161836436441045926992203 := by
  unfold tailWord_1418289
  simp only [CollatzResearch.WordTrace]
  refine ⟨51729249558788652321833921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34486166372525768214555947 51729249558788652321833921)
  ·
    refine ⟨38796937169091489241375441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51729249558788652321833921 38796937169091489241375441)
    ·
      refine ⟨29097702876818616931031581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38796937169091489241375441 29097702876818616931031581)
      ·
        refine ⟨10911638578806981349136843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29097702876818616931031581 10911638578806981349136843)
        ·
          refine ⟨16367457868210472023705265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10911638578806981349136843 16367457868210472023705265)
          ·
            refine ⟨12275593401157854017778949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16367457868210472023705265 12275593401157854017778949)
            ·
              refine ⟨2301673762717097628333553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12275593401157854017778949 2301673762717097628333553)
              ·
                refine ⟨1726255322037823221250165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2301673762717097628333553 1726255322037823221250165)
                ·
                  refine ⟨161836436441045926992203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1726255322037823221250165 161836436441045926992203)
                  ·
                    rfl

theorem cell22_1418289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 5].length) (baseStart_1418289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1418289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1418289 prefixEnd_1418289 := by exact prefixLift 1418289
  have htrace : WordTrace (prefixWord ++ tailWord_1418289) baseStart_1418289 baseEnd_1418289 := by
    simpa [prefixWord, tailWord_1418289, baseEnd_1418289] using wordTrace_append hprefix tailTrace_1418289
  have hstable : (prefixWord ++ tailWord_1418289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418289).length < 2 ^ (prefixWord ++ tailWord_1418289).sum := by decide
  have hdescent : baseEnd_1418289 < baseStart_1418289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418398 : List Nat := [4, 3, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_1418398 : Nat := 118140960795 + 1418398 * 2 ^ 59
def prefixEnd_1418398 : Nat := 4983230072969 + 3 ^ 40 * 1418398 * 2
def baseEnd_1418398 : Nat := 485546622250697830001275

theorem tailTrace_1418398 : CollatzResearch.WordTrace tailWord_1418398 prefixEnd_1418398 485546622250697830001275 := by
  unfold tailWord_1418398
  simp only [CollatzResearch.WordTrace]
  refine ⟨6466653139424220492193981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34488816743595842625034565 6466653139424220492193981)
  ·
    refine ⟨2424994927284082684572743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6466653139424220492193981 2424994927284082684572743)
    ·
      refine ⟨3637492390926124026859115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2424994927284082684572743 3637492390926124026859115)
      ·
        refine ⟨5456238586389186040288673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3637492390926124026859115 5456238586389186040288673)
        ·
          refine ⟨4092178939791889530216505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5456238586389186040288673 4092178939791889530216505)
          ·
            refine ⟨3069134204843917147662379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4092178939791889530216505 3069134204843917147662379)
            ·
              refine ⟨4603701307265875721493569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3069134204843917147662379 4603701307265875721493569)
              ·
                refine ⟨3452775980449406791120177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4603701307265875721493569 3452775980449406791120177)
                ·
                  refine ⟨2589581985337055093340133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3452775980449406791120177 2589581985337055093340133)
                  ·
                    refine ⟨485546622250697830001275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2589581985337055093340133 485546622250697830001275)
                    ·
                      rfl

theorem cell22_1418398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_1418398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1418398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1418398 prefixEnd_1418398 := by exact prefixLift 1418398
  have htrace : WordTrace (prefixWord ++ tailWord_1418398) baseStart_1418398 baseEnd_1418398 := by
    simpa [prefixWord, tailWord_1418398, baseEnd_1418398] using wordTrace_append hprefix tailTrace_1418398
  have hstable : (prefixWord ++ tailWord_1418398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418398).length < 2 ^ (prefixWord ++ tailWord_1418398).sum := by decide
  have hdescent : baseEnd_1418398 < baseStart_1418398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418501 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 4, 3]
def baseStart_1418501 : Nat := 118140960795 + 1418501 * 2 ^ 59
def prefixEnd_1418501 : Nat := 4983230072969 + 3 ^ 40 * 1418501 * 2
def baseEnd_1418501 : Nat := 485581881255639894675959

theorem tailTrace_1418501 : CollatzResearch.WordTrace tailWord_1418501 prefixEnd_1418501 485581881255639894675959 := by
  unfold tailWord_1418501
  simp only [CollatzResearch.WordTrace]
  refine ⟨51736981834020612528551357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34491321222680408352367571 51736981834020612528551357)
  ·
    refine ⟨19401368187757729698206759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51736981834020612528551357 19401368187757729698206759)
    ·
      refine ⟨29102052281636594547310139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19401368187757729698206759 29102052281636594547310139)
      ·
        refine ⟨43653078422454891820965209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29102052281636594547310139 43653078422454891820965209)
        ·
          refine ⟨32739808816841168865723907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43653078422454891820965209 32739808816841168865723907)
          ·
            refine ⟨49109713225261753298585861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32739808816841168865723907 49109713225261753298585861)
            ·
              refine ⟨9208071229736578743484849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49109713225261753298585861 9208071229736578743484849)
              ·
                refine ⟨6906053422302434057613637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9208071229736578743484849 6906053422302434057613637)
                ·
                  refine ⟨1294885016681706385802557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6906053422302434057613637 1294885016681706385802557)
                  ·
                    refine ⟨485581881255639894675959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1294885016681706385802557 485581881255639894675959)
                    ·
                      rfl

theorem cell22_1418501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 3].length) (baseStart_1418501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1418501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1418501 prefixEnd_1418501 := by exact prefixLift 1418501
  have htrace : WordTrace (prefixWord ++ tailWord_1418501) baseStart_1418501 baseEnd_1418501 := by
    simpa [prefixWord, tailWord_1418501, baseEnd_1418501] using wordTrace_append hprefix tailTrace_1418501
  have hstable : (prefixWord ++ tailWord_1418501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418501).length < 2 ^ (prefixWord ++ tailWord_1418501).sum := by decide
  have hdescent : baseEnd_1418501 < baseStart_1418501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418576 : List Nat := [2, 1, 1, 1, 1, 5, 2, 4, 5]
def baseStart_1418576 : Nat := 118140960795 + 1418576 * 2 ^ 59
def prefixEnd_1418576 : Nat := 4983230072969 + 3 ^ 40 * 1418576 * 2
def baseEnd_1418576 : Nat := 161869185096121566350243

theorem tailTrace_1418576 : CollatzResearch.WordTrace tailWord_1418576 prefixEnd_1418576 161869185096121566350243 := by
  unfold tailWord_1418576
  simp only [CollatzResearch.WordTrace]
  refine ⟨25869858654374450168765791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34493144872499266891687721 25869858654374450168765791)
  ·
    refine ⟨38804787981561675253148687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25869858654374450168765791 38804787981561675253148687)
    ·
      refine ⟨58207181972342512879723031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38804787981561675253148687 58207181972342512879723031)
      ·
        refine ⟨87310772958513769319584547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58207181972342512879723031 87310772958513769319584547)
        ·
          refine ⟨130966159437770653979376821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87310772958513769319584547 130966159437770653979376821)
          ·
            refine ⟨12278077447290998810566577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 130966159437770653979376821 12278077447290998810566577)
            ·
              refine ⟨9208558085468249107924933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12278077447290998810566577 9208558085468249107924933)
              ·
                refine ⟨1726604641025296707735925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9208558085468249107924933 1726604641025296707735925)
                ·
                  refine ⟨161869185096121566350243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1726604641025296707735925 161869185096121566350243)
                  ·
                    rfl

theorem cell22_1418576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 5].length) (baseStart_1418576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1418576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1418576 prefixEnd_1418576 := by exact prefixLift 1418576
  have htrace : WordTrace (prefixWord ++ tailWord_1418576) baseStart_1418576 baseEnd_1418576 := by
    simpa [prefixWord, tailWord_1418576, baseEnd_1418576] using wordTrace_append hprefix tailTrace_1418576
  have hstable : (prefixWord ++ tailWord_1418576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418576).length < 2 ^ (prefixWord ++ tailWord_1418576).sum := by decide
  have hdescent : baseEnd_1418576 < baseStart_1418576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418636 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 3, 5]
def baseStart_1418636 : Nat := 118140960795 + 1418636 * 2 ^ 59
def prefixEnd_1418636 : Nat := 4983230072969 + 3 ^ 40 * 1418636 * 2
def baseEnd_1418636 : Nat := 485628094514544542550545

theorem tailTrace_1418636 : CollatzResearch.WordTrace tailWord_1418636 prefixEnd_1418636 485628094514544542550545 := by
  unfold tailWord_1418636
  simp only [CollatzResearch.WordTrace]
  refine ⟨25870952844265765292357881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34494603792354353723143841 25870952844265765292357881)
  ·
    refine ⟨19403214633199323969268411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25870952844265765292357881 19403214633199323969268411)
    ·
      refine ⟨29104821949798985953902617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19403214633199323969268411 29104821949798985953902617)
      ·
        refine ⟨21828616462349239465426963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29104821949798985953902617 21828616462349239465426963)
        ·
          refine ⟨32742924693523859198140445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21828616462349239465426963 32742924693523859198140445)
          ·
            refine ⟨12278596760071447199302667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32742924693523859198140445 12278596760071447199302667)
            ·
              refine ⟨18417895140107170798954001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12278596760071447199302667 18417895140107170798954001)
              ·
                refine ⟨13813421355080378099215501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18417895140107170798954001 13813421355080378099215501)
                ·
                  refine ⟨5180033008155141787205813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13813421355080378099215501 5180033008155141787205813)
                  ·
                    refine ⟨485628094514544542550545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5180033008155141787205813 485628094514544542550545)
                    ·
                      rfl

theorem cell22_1418636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_1418636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1418636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1418636 prefixEnd_1418636 := by exact prefixLift 1418636
  have htrace : WordTrace (prefixWord ++ tailWord_1418636) baseStart_1418636 baseEnd_1418636 := by
    simpa [prefixWord, tailWord_1418636, baseEnd_1418636] using wordTrace_append hprefix tailTrace_1418636
  have hstable : (prefixWord ++ tailWord_1418636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418636).length < 2 ^ (prefixWord ++ tailWord_1418636).sum := by decide
  have hdescent : baseEnd_1418636 < baseStart_1418636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418653 : List Nat := [1, 4, 2, 1, 3, 1, 1, 3, 1, 5]
def baseStart_1418653 : Nat := 118140960795 + 1418653 * 2 ^ 59
def prefixEnd_1418653 : Nat := 4983230072969 + 3 ^ 40 * 1418653 * 2
def baseEnd_1418653 : Nat := 485633913961962164875493

theorem tailTrace_1418653 : CollatzResearch.WordTrace tailWord_1418653 prefixEnd_1418653 485633913961962164875493 := by
  unfold tailWord_1418653
  simp only [CollatzResearch.WordTrace]
  refine ⟨51742525729469942488084613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34495017152979961658723075 51742525729469942488084613)
  ·
    refine ⟨9701723574275614216515865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51742525729469942488084613 9701723574275614216515865)
    ·
      refine ⟨7276292680706710662386899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9701723574275614216515865 7276292680706710662386899)
      ·
        refine ⟨10914439021060065993580349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7276292680706710662386899 10914439021060065993580349)
        ·
          refine ⟨4092914632897524747592631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10914439021060065993580349 4092914632897524747592631)
          ·
            refine ⟨6139371949346287121388947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4092914632897524747592631 6139371949346287121388947)
            ·
              refine ⟨9209057924019430682083421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6139371949346287121388947 9209057924019430682083421)
              ·
                refine ⟨3453396721507286505781283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9209057924019430682083421 3453396721507286505781283)
                ·
                  refine ⟨5180095082260929758671925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3453396721507286505781283 5180095082260929758671925)
                  ·
                    refine ⟨485633913961962164875493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5180095082260929758671925 485633913961962164875493)
                    ·
                      rfl

theorem cell22_1418653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_1418653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1418653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1418653 prefixEnd_1418653 := by exact prefixLift 1418653
  have htrace : WordTrace (prefixWord ++ tailWord_1418653) baseStart_1418653 baseEnd_1418653 := by
    simpa [prefixWord, tailWord_1418653, baseEnd_1418653] using wordTrace_append hprefix tailTrace_1418653
  have hstable : (prefixWord ++ tailWord_1418653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418653).length < 2 ^ (prefixWord ++ tailWord_1418653).sum := by decide
  have hdescent : baseEnd_1418653 < baseStart_1418653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418668 : List Nat := [2, 2, 1, 1, 1, 1, 7, 1, 2, 4]
def baseStart_1418668 : Nat := 118140960795 + 1418668 * 2 ^ 59
def prefixEnd_1418668 : Nat := 4983230072969 + 3 ^ 40 * 1418668 * 2
def baseEnd_1418668 : Nat := 485639048768507125750447

theorem tailTrace_1418668 : CollatzResearch.WordTrace tailWord_1418668 prefixEnd_1418668 485639048768507125750447 := by
  unfold tailWord_1418668
  simp only [CollatzResearch.WordTrace]
  refine ⟨25871536412207800024940329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34495381882943733366587105 25871536412207800024940329)
  ·
    refine ⟨19403652309155850018705247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25871536412207800024940329 19403652309155850018705247)
    ·
      refine ⟨29105478463733775028057871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19403652309155850018705247 29105478463733775028057871)
      ·
        refine ⟨43658217695600662542086807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29105478463733775028057871 43658217695600662542086807)
        ·
          refine ⟨65487326543400993813130211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43658217695600662542086807 65487326543400993813130211)
          ·
            refine ⟨98230989815101490719695317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65487326543400993813130211 98230989815101490719695317)
            ·
              refine ⟨2302288823791441188742859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 98230989815101490719695317 2302288823791441188742859)
              ·
                refine ⟨3453433235687161783114289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2302288823791441188742859 3453433235687161783114289)
                ·
                  refine ⟨2590074926765371337335717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3453433235687161783114289 2590074926765371337335717)
                  ·
                    refine ⟨485639048768507125750447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2590074926765371337335717 485639048768507125750447)
                    ·
                      rfl

theorem cell22_1418668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_1418668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1418668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1418668 prefixEnd_1418668 := by exact prefixLift 1418668
  have htrace : WordTrace (prefixWord ++ tailWord_1418668) baseStart_1418668 baseEnd_1418668 := by
    simpa [prefixWord, tailWord_1418668, baseEnd_1418668] using wordTrace_append hprefix tailTrace_1418668
  have hstable : (prefixWord ++ tailWord_1418668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418668).length < 2 ^ (prefixWord ++ tailWord_1418668).sum := by decide
  have hdescent : baseEnd_1418668 < baseStart_1418668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418749 : List Nat := [1, 4, 1, 1, 1, 5, 3, 2, 1, 3]
def baseStart_1418749 : Nat := 118140960795 + 1418749 * 2 ^ 59
def prefixEnd_1418749 : Nat := 4983230072969 + 3 ^ 40 * 1418749 * 2
def baseEnd_1418749 : Nat := 485666776723849914475199

theorem tailTrace_1418749 : CollatzResearch.WordTrace tailWord_1418749 prefixEnd_1418749 485666776723849914475199 := by
  unfold tailWord_1418749
  simp only [CollatzResearch.WordTrace]
  refine ⟨51746027137122150883579301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34497351424748100589052867 51746027137122150883579301)
  ·
    refine ⟨9702380088210403290671119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51746027137122150883579301 9702380088210403290671119)
    ·
      refine ⟨14553570132315604936006679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9702380088210403290671119 14553570132315604936006679)
      ·
        refine ⟨21830355198473407404010019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14553570132315604936006679 21830355198473407404010019)
        ·
          refine ⟨32745532797710111106015029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21830355198473407404010019 32745532797710111106015029)
          ·
            refine ⟨3069893699785322916188909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32745532797710111106015029 3069893699785322916188909)
            ·
              refine ⟨1151210137419496093570841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3069893699785322916188909 1151210137419496093570841)
              ·
                refine ⟨863407603064622070178131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1151210137419496093570841 863407603064622070178131)
                ·
                  refine ⟨1295111404596933105267197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 863407603064622070178131 1295111404596933105267197)
                  ·
                    refine ⟨485666776723849914475199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1295111404596933105267197 485666776723849914475199)
                    ·
                      rfl

theorem cell22_1418749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_1418749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1418749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1418749 prefixEnd_1418749 := by exact prefixLift 1418749
  have htrace : WordTrace (prefixWord ++ tailWord_1418749) baseStart_1418749 baseEnd_1418749 := by
    simpa [prefixWord, tailWord_1418749, baseEnd_1418749] using wordTrace_append hprefix tailTrace_1418749
  have hstable : (prefixWord ++ tailWord_1418749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418749).length < 2 ^ (prefixWord ++ tailWord_1418749).sum := by decide
  have hdescent : baseEnd_1418749 < baseStart_1418749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418762 : List Nat := [3, 1, 2, 2, 2, 4, 2, 1, 5]
def baseStart_1418762 : Nat := 118140960795 + 1418762 * 2 ^ 59
def prefixEnd_1418762 : Nat := 4983230072969 + 3 ^ 40 * 1418762 * 2
def baseEnd_1418762 : Nat := 161890408963174071300053

theorem tailTrace_1418762 : CollatzResearch.WordTrace tailWord_1418762 prefixEnd_1418762 161890408963174071300053 := by
  unfold tailWord_1418762
  simp only [CollatzResearch.WordTrace]
  refine ⟨12936625321518763525950635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34497667524050036069201693 12936625321518763525950635)
  ·
    refine ⟨19404937982278145288925953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12936625321518763525950635 19404937982278145288925953)
    ·
      refine ⟨14553703486708608966694465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19404937982278145288925953 14553703486708608966694465)
      ·
        refine ⟨10915277615031456725020849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14553703486708608966694465 10915277615031456725020849)
        ·
          refine ⟨8186458211273592543765637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10915277615031456725020849 8186458211273592543765637)
          ·
            refine ⟨1534960914613798601956057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8186458211273592543765637 1534960914613798601956057)
            ·
              refine ⟨1151220685960348951467043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1534960914613798601956057 1151220685960348951467043)
              ·
                refine ⟨1726831028940523427200565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1151220685960348951467043 1726831028940523427200565)
                ·
                  refine ⟨161890408963174071300053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1726831028940523427200565 161890408963174071300053)
                  ·
                    rfl

theorem cell22_1418762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 5].length) (baseStart_1418762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1418762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1418762 prefixEnd_1418762 := by exact prefixLift 1418762
  have htrace : WordTrace (prefixWord ++ tailWord_1418762) baseStart_1418762 baseEnd_1418762 := by
    simpa [prefixWord, tailWord_1418762, baseEnd_1418762] using wordTrace_append hprefix tailTrace_1418762
  have hstable : (prefixWord ++ tailWord_1418762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418762).length < 2 ^ (prefixWord ++ tailWord_1418762).sum := by decide
  have hdescent : baseEnd_1418762 < baseStart_1418762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418807 : List Nat := [1, 1, 3, 1, 2, 4, 4, 2, 4]
def baseStart_1418807 : Nat := 118140960795 + 1418807 * 2 ^ 59
def prefixEnd_1418807 : Nat := 4983230072969 + 3 ^ 40 * 1418807 * 2
def baseEnd_1418807 : Nat := 161895543769719032175007

theorem tailTrace_1418807 : CollatzResearch.WordTrace tailWord_1418807 prefixEnd_1418807 161895543769719032175007 := by
  unfold tailWord_1418807
  simp only [CollatzResearch.WordTrace]
  refine ⟨51748142570912026789190675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34498761713941351192793783 51748142570912026789190675)
  ·
    refine ⟨77622213856368040183786013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51748142570912026789190675 77622213856368040183786013)
    ·
      refine ⟨29108330196138015068919755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77622213856368040183786013 29108330196138015068919755)
      ·
        refine ⟨43662495294207022603379633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29108330196138015068919755 43662495294207022603379633)
        ·
          refine ⟨32746871470655266952534725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43662495294207022603379633 32746871470655266952534725)
          ·
            refine ⟨6140038400747862553600261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32746871470655266952534725 6140038400747862553600261)
            ·
              refine ⟨1151257200140224228800049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6140038400747862553600261 1151257200140224228800049)
              ·
                refine ⟨863442900105168171600037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1151257200140224228800049 863442900105168171600037)
                ·
                  refine ⟨161895543769719032175007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 863442900105168171600037 161895543769719032175007)
                  ·
                    rfl

theorem cell22_1418807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 4].length) (baseStart_1418807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1418807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1418807 prefixEnd_1418807 := by exact prefixLift 1418807
  have htrace : WordTrace (prefixWord ++ tailWord_1418807) baseStart_1418807 baseEnd_1418807 := by
    simpa [prefixWord, tailWord_1418807, baseEnd_1418807] using wordTrace_append hprefix tailTrace_1418807
  have hstable : (prefixWord ++ tailWord_1418807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418807).length < 2 ^ (prefixWord ++ tailWord_1418807).sum := by decide
  have hdescent : baseEnd_1418807 < baseStart_1418807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419006 : List Nat := [4, 2, 2, 1, 3, 2, 1, 1, 2, 4]
def baseStart_1419006 : Nat := 118140960795 + 1419006 * 2 ^ 59
def prefixEnd_1419006 : Nat := 4983230072969 + 3 ^ 40 * 1419006 * 2
def baseEnd_1419006 : Nat := 485754753075986910799411

theorem tailTrace_1419006 : CollatzResearch.WordTrace tailWord_1419006 prefixEnd_1419006 485754753075986910799411 := by
  unfold tailWord_1419006
  simp only [CollatzResearch.WordTrace]
  refine ⟨6469425087148885471960609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34503600464794055850456581 6469425087148885471960609)
  ·
    refine ⟨4852068815361664103970457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6469425087148885471960609 4852068815361664103970457)
    ·
      refine ⟨3639051611521248077977843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4852068815361664103970457 3639051611521248077977843)
      ·
        refine ⟨5458577417281872116966765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3639051611521248077977843 5458577417281872116966765)
        ·
          refine ⟨2046966531480702043862537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5458577417281872116966765 2046966531480702043862537)
          ·
            refine ⟨1535224898610526532896903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2046966531480702043862537 1535224898610526532896903)
            ·
              refine ⟨2302837347915789799345355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1535224898610526532896903 2302837347915789799345355)
              ·
                refine ⟨3454256021873684699018033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2302837347915789799345355 3454256021873684699018033)
                ·
                  refine ⟨2590692016405263524263525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3454256021873684699018033 2590692016405263524263525)
                  ·
                    refine ⟨485754753075986910799411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2590692016405263524263525 485754753075986910799411)
                    ·
                      rfl

theorem cell22_1419006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_1419006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419006 prefixEnd_1419006 := by exact prefixLift 1419006
  have htrace : WordTrace (prefixWord ++ tailWord_1419006) baseStart_1419006 baseEnd_1419006 := by
    simpa [prefixWord, tailWord_1419006, baseEnd_1419006] using wordTrace_append hprefix tailTrace_1419006
  have hstable : (prefixWord ++ tailWord_1419006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419006).length < 2 ^ (prefixWord ++ tailWord_1419006).sum := by decide
  have hdescent : baseEnd_1419006 < baseStart_1419006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419019 : List Nat := [1, 1, 1, 1, 5, 1, 3, 5, 1, 3]
def baseStart_1419019 : Nat := 118140960795 + 1419019 * 2 ^ 59
def prefixEnd_1419019 : Nat := 4983230072969 + 3 ^ 40 * 1419019 * 2
def baseEnd_1419019 : Nat := 485759203241659210224371

theorem tailTrace_1419019 : CollatzResearch.WordTrace tailWord_1419019 prefixEnd_1419019 485759203241659210224371 := by
  unfold tailWord_1419019
  simp only [CollatzResearch.WordTrace]
  refine ⟨51755874846143986995908111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34503916564095991330605407 51755874846143986995908111)
  ·
    refine ⟨77633812269215980493862167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51755874846143986995908111 77633812269215980493862167)
    ·
      refine ⟨116450718403823970740793251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77633812269215980493862167 116450718403823970740793251)
      ·
        refine ⟨174676077605735956111189877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116450718403823970740793251 174676077605735956111189877)
        ·
          refine ⟨16375882275537745885424051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174676077605735956111189877 16375882275537745885424051)
          ·
            refine ⟨24563823413306618828136077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16375882275537745885424051 24563823413306618828136077)
            ·
              refine ⟨9211433779989982060551029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24563823413306618828136077 9211433779989982060551029)
              ·
                refine ⟨863571916874060818176659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9211433779989982060551029 863571916874060818176659)
                ·
                  refine ⟨1295357875311091227264989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 863571916874060818176659 1295357875311091227264989)
                  ·
                    refine ⟨485759203241659210224371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1295357875311091227264989 485759203241659210224371)
                    ·
                      rfl

theorem cell22_1419019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 1, 3].length) (baseStart_1419019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419019 prefixEnd_1419019 := by exact prefixLift 1419019
  have htrace : WordTrace (prefixWord ++ tailWord_1419019) baseStart_1419019 baseEnd_1419019 := by
    simpa [prefixWord, tailWord_1419019, baseEnd_1419019] using wordTrace_append hprefix tailTrace_1419019
  have hstable : (prefixWord ++ tailWord_1419019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419019).length < 2 ^ (prefixWord ++ tailWord_1419019).sum := by decide
  have hdescent : baseEnd_1419019 < baseStart_1419019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419032 : List Nat := [2, 1, 2, 3, 1, 1, 5, 2, 5]
def baseStart_1419032 : Nat := 118140960795 + 1419032 * 2 ^ 59
def prefixEnd_1419032 : Nat := 4983230072969 + 3 ^ 40 * 1419032 * 2
def baseEnd_1419032 : Nat := 161921217802443836549777

theorem tailTrace_1419032 : CollatzResearch.WordTrace tailWord_1419032 prefixEnd_1419032 161921217802443836549777 := by
  unfold tailWord_1419032
  simp only [CollatzResearch.WordTrace]
  refine ⟨25878174497548445108065675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34504232663397926810754233 25878174497548445108065675)
  ·
    refine ⟨38817261746322667662098513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25878174497548445108065675 38817261746322667662098513)
    ·
      refine ⟨29112946309742000746573885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38817261746322667662098513 29112946309742000746573885)
      ·
        refine ⟨10917354866153250279965207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29112946309742000746573885 10917354866153250279965207)
        ·
          refine ⟨16376032299229875419947811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10917354866153250279965207 16376032299229875419947811)
          ·
            refine ⟨24564048448844813129921717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16376032299229875419947811 24564048448844813129921717)
            ·
              refine ⟨2302879542079201230930161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24564048448844813129921717 2302879542079201230930161)
              ·
                refine ⟨1727159656559400923197621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2302879542079201230930161 1727159656559400923197621)
                ·
                  refine ⟨161921217802443836549777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1727159656559400923197621 161921217802443836549777)
                  ·
                    rfl

theorem cell22_1419032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 5].length) (baseStart_1419032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419032 prefixEnd_1419032 := by exact prefixLift 1419032
  have htrace : WordTrace (prefixWord ++ tailWord_1419032) baseStart_1419032 baseEnd_1419032 := by
    simpa [prefixWord, tailWord_1419032, baseEnd_1419032] using wordTrace_append hprefix tailTrace_1419032
  have hstable : (prefixWord ++ tailWord_1419032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419032).length < 2 ^ (prefixWord ++ tailWord_1419032).sum := by decide
  have hdescent : baseEnd_1419032 < baseStart_1419032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419126 : List Nat := [5, 1, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_1419126 : Nat := 118140960795 + 1419126 * 2 ^ 59
def prefixEnd_1419126 : Nat := 4983230072969 + 3 ^ 40 * 1419126 * 2
def baseEnd_1419126 : Nat := 485795831528346597799043

theorem tailTrace_1419126 : CollatzResearch.WordTrace tailWord_1419126 prefixEnd_1419126 485795831528346597799043 := by
  unfold tailWord_1419126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3234986091047271516878327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34506518304504229513368821 3234986091047271516878327)
  ·
    refine ⟨4852479136570907275317491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3234986091047271516878327 4852479136570907275317491)
    ·
      refine ⟨7278718704856360912976237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4852479136570907275317491 7278718704856360912976237)
      ·
        refine ⟨2729519514321135342366089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7278718704856360912976237 2729519514321135342366089)
        ·
          refine ⟨2047139635740851506774567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2729519514321135342366089 2047139635740851506774567)
          ·
            refine ⟨3070709453611277260161851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047139635740851506774567 3070709453611277260161851)
            ·
              refine ⟨4606064180416915890242777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3070709453611277260161851 4606064180416915890242777)
              ·
                refine ⟨3454548135312686917682083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4606064180416915890242777 3454548135312686917682083)
                ·
                  refine ⟨5181822202969030376523125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3454548135312686917682083 5181822202969030376523125)
                  ·
                    refine ⟨485795831528346597799043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5181822202969030376523125 485795831528346597799043)
                    ·
                      rfl

theorem cell22_1419126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_1419126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419126 prefixEnd_1419126 := by exact prefixLift 1419126
  have htrace : WordTrace (prefixWord ++ tailWord_1419126) baseStart_1419126 baseEnd_1419126 := by
    simpa [prefixWord, tailWord_1419126, baseEnd_1419126] using wordTrace_append hprefix tailTrace_1419126
  have hstable : (prefixWord ++ tailWord_1419126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419126).length < 2 ^ (prefixWord ++ tailWord_1419126).sum := by decide
  have hdescent : baseEnd_1419126 < baseStart_1419126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419218 : List Nat := [3, 2, 2, 3, 2, 1, 3, 1, 5]
def baseStart_1419218 : Nat := 118140960795 + 1419218 * 2 ^ 59
def prefixEnd_1419218 : Nat := 4983230072969 + 3 ^ 40 * 1419218 * 2
def baseEnd_1419218 : Nat := 161942441669496341499587

theorem tailTrace_1419218 : CollatzResearch.WordTrace tailWord_1419218 prefixEnd_1419218 161942441669496341499587 := by
  unfold tailWord_1419218
  simp only [CollatzResearch.WordTrace]
  refine ⟨12940783243105760995600577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34508755314948695988268205 12940783243105760995600577)
  ·
    refine ⟨9705587432329320746700433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12940783243105760995600577 9705587432329320746700433)
    ·
      refine ⟨7279190574246990560025325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9705587432329320746700433 7279190574246990560025325)
      ·
        refine ⟨2729696465342621460009497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7279190574246990560025325 2729696465342621460009497)
        ·
          refine ⟨2047272349006966095007123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2729696465342621460009497 2047272349006966095007123)
          ·
            refine ⟨3070908523510449142510685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047272349006966095007123 3070908523510449142510685)
            ·
              refine ⟨1151590696316418428441507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3070908523510449142510685 1151590696316418428441507)
              ·
                refine ⟨1727386044474627642662261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1151590696316418428441507 1727386044474627642662261)
                ·
                  refine ⟨161942441669496341499587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1727386044474627642662261 161942441669496341499587)
                  ·
                    rfl

theorem cell22_1419218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_1419218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419218 prefixEnd_1419218 := by exact prefixLift 1419218
  have htrace : WordTrace (prefixWord ++ tailWord_1419218) baseStart_1419218 baseEnd_1419218 := by
    simpa [prefixWord, tailWord_1419218, baseEnd_1419218] using wordTrace_append hprefix tailTrace_1419218
  have hstable : (prefixWord ++ tailWord_1419218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419218).length < 2 ^ (prefixWord ++ tailWord_1419218).sum := by decide
  have hdescent : baseEnd_1419218 < baseStart_1419218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419231 : List Nat := [1, 1, 2, 3, 4, 2, 2, 2, 1, 4]
def baseStart_1419231 : Nat := 118140960795 + 1419231 * 2 ^ 59
def prefixEnd_1419231 : Nat := 4983230072969 + 3 ^ 40 * 1419231 * 2
def baseEnd_1419231 : Nat := 485831775174161323923721

theorem tailTrace_1419231 : CollatzResearch.WordTrace tailWord_1419231 prefixEnd_1419231 485831775174161323923721 := by
  unfold tailWord_1419231
  simp only [CollatzResearch.WordTrace]
  refine ⟨51763607121375947202625547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34509071414250631468417031 51763607121375947202625547)
  ·
    refine ⟨77645410682063920803938321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51763607121375947202625547 77645410682063920803938321)
    ·
      refine ⟨58234058011547940602953741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77645410682063920803938321 58234058011547940602953741)
      ·
        refine ⟨21837771754330477726107653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58234058011547940602953741 21837771754330477726107653)
        ·
          refine ⟨4094582203936964573645185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21837771754330477726107653 4094582203936964573645185)
          ·
            refine ⟨3070936652952723430233889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4094582203936964573645185 3070936652952723430233889)
            ·
              refine ⟨2303202489714542572675417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3070936652952723430233889 2303202489714542572675417)
              ·
                refine ⟨1727401867285906929506563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2303202489714542572675417 1727401867285906929506563)
                ·
                  refine ⟨2591102800928860394259845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1727401867285906929506563 2591102800928860394259845)
                  ·
                    refine ⟨485831775174161323923721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2591102800928860394259845 485831775174161323923721)
                    ·
                      rfl

theorem cell22_1419231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 4].length) (baseStart_1419231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419231 prefixEnd_1419231 := by exact prefixLift 1419231
  have htrace : WordTrace (prefixWord ++ tailWord_1419231) baseStart_1419231 baseEnd_1419231 := by
    simpa [prefixWord, tailWord_1419231, baseEnd_1419231] using wordTrace_append hprefix tailTrace_1419231
  have hstable : (prefixWord ++ tailWord_1419231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419231).length < 2 ^ (prefixWord ++ tailWord_1419231).sum := by decide
  have hdescent : baseEnd_1419231 < baseStart_1419231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419257 : List Nat := [1, 2, 1, 3, 1, 4, 10]
def baseStart_1419257 : Nat := 118140960795 + 1419257 * 2 ^ 59
def prefixEnd_1419257 : Nat := 4983230072969 + 3 ^ 40 * 1419257 * 2
def baseEnd_1419257 : Nat := 17994099092796515658283

theorem tailTrace_1419257 : CollatzResearch.WordTrace tailWord_1419257 prefixEnd_1419257 17994099092796515658283 := by
  unfold tailWord_1419257
  simp only [CollatzResearch.WordTrace]
  refine ⟨51764555419281753643072025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34509703612854502428714683 51764555419281753643072025)
  ·
    refine ⟨38823416564461315232304019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51764555419281753643072025 38823416564461315232304019)
    ·
      refine ⟨58235124846691972848456029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38823416564461315232304019 58235124846691972848456029)
      ·
        refine ⟨21838171817509489818171011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58235124846691972848456029 21838171817509489818171011)
        ·
          refine ⟨32757257726264234727256517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21838171817509489818171011 32757257726264234727256517)
          ·
            refine ⟨6141985823674544011360597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32757257726264234727256517 6141985823674544011360597)
            ·
              refine ⟨17994099092796515658283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6141985823674544011360597 17994099092796515658283)
              ·
                rfl

theorem cell22_1419257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 10].length) (baseStart_1419257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1419257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1419257 prefixEnd_1419257 := by exact prefixLift 1419257
  have htrace : WordTrace (prefixWord ++ tailWord_1419257) baseStart_1419257 baseEnd_1419257 := by
    simpa [prefixWord, tailWord_1419257, baseEnd_1419257] using wordTrace_append hprefix tailTrace_1419257
  have hstable : (prefixWord ++ tailWord_1419257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419257).length < 2 ^ (prefixWord ++ tailWord_1419257).sum := by decide
  have hdescent : baseEnd_1419257 < baseStart_1419257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
