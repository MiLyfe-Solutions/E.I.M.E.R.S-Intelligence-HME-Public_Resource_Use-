import V185TrunkScan21Chunk105

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1287477 : List Nat := [1, 3, 3, 1, 2, 2, 4, 2, 3]
def baseStart_1287477 : Nat := 118140960795 + 1287477 * 2 ^ 59
def prefixEnd_1287477 : Nat := 4983230072969 + 3 ^ 40 * 1287477 * 2
def baseEnd_1287477 : Nat := 293819792270561988451781

theorem tailTrace_1287477 : CollatzResearch.WordTrace tailWord_1287477 prefixEnd_1287477 293819792270561988451781 := by
  unfold tailWord_1287477
  simp only [CollatzResearch.WordTrace]
  refine ⟨46958143956698187410884685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31305429304465458273923123 46958143956698187410884685)
  ·
    refine ⟨17609303983761820279081757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46958143956698187410884685 17609303983761820279081757)
    ·
      refine ⟨6603488993910682604655659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17609303983761820279081757 6603488993910682604655659)
      ·
        refine ⟨9905233490866023906983489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6603488993910682604655659 9905233490866023906983489)
        ·
          refine ⟨7428925118149517930237617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9905233490866023906983489 7428925118149517930237617)
          ·
            refine ⟨5571693838612138447678213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7428925118149517930237617 5571693838612138447678213)
            ·
              refine ⟨1044692594739775958939665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5571693838612138447678213 1044692594739775958939665)
              ·
                refine ⟨783519446054831969204749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1044692594739775958939665 783519446054831969204749)
                ·
                  refine ⟨293819792270561988451781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 783519446054831969204749 293819792270561988451781)
                  ·
                    rfl

theorem cell21_1287477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 3].length) (baseStart_1287477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1287477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1287477 prefixEnd_1287477 := by exact prefixLift 1287477
  have htrace : WordTrace (prefixWord ++ tailWord_1287477) baseStart_1287477 baseEnd_1287477 := by
    simpa [prefixWord, tailWord_1287477, baseEnd_1287477] using wordTrace_append hprefix tailTrace_1287477
  have hstable : (prefixWord ++ tailWord_1287477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287477).length < 2 ^ (prefixWord ++ tailWord_1287477).sum := by decide
  have hdescent : baseEnd_1287477 < baseStart_1287477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287494 : List Nat := [6, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_1287494 : Nat := 118140960795 + 1287494 * 2 ^ 59
def prefixEnd_1287494 : Nat := 4983230072969 + 3 ^ 40 * 1287494 * 2
def baseEnd_1287494 : Nat := 293823671902173736668413

theorem tailTrace_1287494 : CollatzResearch.WordTrace tailWord_1287494 prefixEnd_1287494 293823671902173736668413 := by
  unfold tailWord_1287494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1467461374926143728570423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31305842665091066209502357 1467461374926143728570423)
  ·
    refine ⟨2201192062389215592855635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1467461374926143728570423 2201192062389215592855635)
    ·
      refine ⟨3301788093583823389283453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2201192062389215592855635 3301788093583823389283453)
      ·
        refine ⟨1238170535093933770981295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3301788093583823389283453 1238170535093933770981295)
        ·
          refine ⟨1857255802640900656471943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1238170535093933770981295 1857255802640900656471943)
          ·
            refine ⟨2785883703961350984707915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1857255802640900656471943 2785883703961350984707915)
            ·
              refine ⟨4178825555942026477061873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2785883703961350984707915 4178825555942026477061873)
              ·
                refine ⟨3134119166956519857796405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4178825555942026477061873 3134119166956519857796405)
                ·
                  refine ⟨293823671902173736668413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3134119166956519857796405 293823671902173736668413)
                  ·
                    rfl

theorem cell21_1287494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_1287494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1287494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1287494 prefixEnd_1287494 := by exact prefixLift 1287494
  have htrace : WordTrace (prefixWord ++ tailWord_1287494) baseStart_1287494 baseEnd_1287494 := by
    simpa [prefixWord, tailWord_1287494, baseEnd_1287494] using wordTrace_append hprefix tailTrace_1287494
  have hstable : (prefixWord ++ tailWord_1287494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287494).length < 2 ^ (prefixWord ++ tailWord_1287494).sum := by decide
  have hdescent : baseEnd_1287494 < baseStart_1287494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287547 : List Nat := [1, 1, 1, 1, 1, 6, 2, 8]
def baseStart_1287547 : Nat := 118140960795 + 1287547 * 2 ^ 59
def prefixEnd_1287547 : Nat := 4983230072969 + 3 ^ 40 * 1287547 * 2
def baseEnd_1287547 : Nat := 97945255741419140761657

theorem tailTrace_1287547 : CollatzResearch.WordTrace tailWord_1287547 prefixEnd_1287547 97945255741419140761657 := by
  unfold tailWord_1287547
  simp only [CollatzResearch.WordTrace]
  refine ⟨46960697066444589365932895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31307131377629726243955263 46960697066444589365932895)
  ·
    refine ⟨70441045599666884048899343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46960697066444589365932895 70441045599666884048899343)
    ·
      refine ⟨105661568399500326073349015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70441045599666884048899343 105661568399500326073349015)
      ·
        refine ⟨158492352599250489110023523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105661568399500326073349015 158492352599250489110023523)
        ·
          refine ⟨237738528898875733665035285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158492352599250489110023523 237738528898875733665035285)
          ·
            refine ⟨11143993542134800015548529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 237738528898875733665035285 11143993542134800015548529)
            ·
              refine ⟨8357995156601100011661397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11143993542134800015548529 8357995156601100011661397)
              ·
                refine ⟨97945255741419140761657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8357995156601100011661397 97945255741419140761657)
                ·
                  rfl

theorem cell21_1287547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 8].length) (baseStart_1287547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1287547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1287547 prefixEnd_1287547 := by exact prefixLift 1287547
  have htrace : WordTrace (prefixWord ++ tailWord_1287547) baseStart_1287547 baseEnd_1287547 := by
    simpa [prefixWord, tailWord_1287547, baseEnd_1287547] using wordTrace_append hprefix tailTrace_1287547
  have hstable : (prefixWord ++ tailWord_1287547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287547).length < 2 ^ (prefixWord ++ tailWord_1287547).sum := by decide
  have hdescent : baseEnd_1287547 < baseStart_1287547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287623 : List Nat := [1, 1, 4, 1, 1, 3, 1, 9]
def baseStart_1287623 : Nat := 118140960795 + 1287623 * 2 ^ 59
def prefixEnd_1287623 : Nat := 4983230072969 + 3 ^ 40 * 1287623 * 2
def baseEnd_1287623 : Nat := 97951037153232726339383

theorem tailTrace_1287623 : CollatzResearch.WordTrace tailWord_1287623 prefixEnd_1287623 97951037153232726339383 := by
  unfold tailWord_1287623
  simp only [CollatzResearch.WordTrace]
  refine ⟨46963469014169254345699523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31308979342779502897133015 46963469014169254345699523)
  ·
    refine ⟨70445203521253881518549285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46963469014169254345699523 70445203521253881518549285)
    ·
      refine ⟨13208475660235102784727991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70445203521253881518549285 13208475660235102784727991)
      ·
        refine ⟨19812713490352654177091987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13208475660235102784727991 19812713490352654177091987)
        ·
          refine ⟨29719070235528981265637981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19812713490352654177091987 29719070235528981265637981)
          ·
            refine ⟨11144651338323367974614243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29719070235528981265637981 11144651338323367974614243)
            ·
              refine ⟨16716977007485051961921365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11144651338323367974614243 16716977007485051961921365)
              ·
                refine ⟨97951037153232726339383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16716977007485051961921365 97951037153232726339383)
                ·
                  rfl

theorem cell21_1287623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 9].length) (baseStart_1287623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1287623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1287623 prefixEnd_1287623 := by exact prefixLift 1287623
  have htrace : WordTrace (prefixWord ++ tailWord_1287623) baseStart_1287623 baseEnd_1287623 := by
    simpa [prefixWord, tailWord_1287623, baseEnd_1287623] using wordTrace_append hprefix tailTrace_1287623
  have hstable : (prefixWord ++ tailWord_1287623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287623).length < 2 ^ (prefixWord ++ tailWord_1287623).sum := by decide
  have hdescent : baseEnd_1287623 < baseStart_1287623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287699 : List Nat := [1, 1, 1, 2, 1, 7, 8]
def baseStart_1287699 : Nat := 118140960795 + 1287699 * 2 ^ 59
def prefixEnd_1287699 : Nat := 4983230072969 + 3 ^ 40 * 1287699 * 2
def baseEnd_1287699 : Nat := 32652272855015437305703

theorem tailTrace_1287699 : CollatzResearch.WordTrace tailWord_1287699 prefixEnd_1287699 32652272855015437305703 := by
  unfold tailWord_1287699
  simp only [CollatzResearch.WordTrace]
  refine ⟨46966240961893919325466151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31310827307929279550310767 46966240961893919325466151)
  ·
    refine ⟨70449361442840878988199227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46966240961893919325466151 70449361442840878988199227)
    ·
      refine ⟨105674042164261318482298841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70449361442840878988199227 105674042164261318482298841)
      ·
        refine ⟨79255531623195988861724131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105674042164261318482298841 79255531623195988861724131)
        ·
          refine ⟨118883297434793983292586197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79255531623195988861724131 118883297434793983292586197)
          ·
            refine ⟨2786327283627983983419989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 118883297434793983292586197 2786327283627983983419989)
            ·
              refine ⟨32652272855015437305703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2786327283627983983419989 32652272855015437305703)
              ·
                rfl

theorem cell21_1287699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 8].length) (baseStart_1287699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1287699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1287699 prefixEnd_1287699 := by exact prefixLift 1287699
  have htrace : WordTrace (prefixWord ++ tailWord_1287699) baseStart_1287699 baseEnd_1287699 := by
    simpa [prefixWord, tailWord_1287699, baseEnd_1287699] using wordTrace_append hprefix tailTrace_1287699
  have hstable : (prefixWord ++ tailWord_1287699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287699).length < 2 ^ (prefixWord ++ tailWord_1287699).sum := by decide
  have hdescent : baseEnd_1287699 < baseStart_1287699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287733 : List Nat := [1, 3, 3, 1, 1, 5, 2, 5]
def baseStart_1287733 : Nat := 118140960795 + 1287733 * 2 ^ 59
def prefixEnd_1287733 : Nat := 4983230072969 + 3 ^ 40 * 1287733 * 2
def baseEnd_1287733 : Nat := 97959404986120810728197

theorem tailTrace_1287733 : CollatzResearch.WordTrace tailWord_1287733 prefixEnd_1287733 97959404986120810728197 := by
  unfold tailWord_1287733
  simp only [CollatzResearch.WordTrace]
  refine ⟨46967481043770743132203853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31311654029180495421469235 46967481043770743132203853)
  ·
    refine ⟨17612805391414028674576445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46967481043770743132203853 17612805391414028674576445)
    ·
      refine ⟨6604802021780260752966167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17612805391414028674576445 6604802021780260752966167)
      ·
        refine ⟨9907203032670391129449251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6604802021780260752966167 9907203032670391129449251)
        ·
          refine ⟨14860804549005586694173877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9907203032670391129449251 14860804549005586694173877)
          ·
            refine ⟨1393200426469273752578801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14860804549005586694173877 1393200426469273752578801)
            ·
              refine ⟨1044900319851955314434101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1393200426469273752578801 1044900319851955314434101)
              ·
                refine ⟨97959404986120810728197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1044900319851955314434101 97959404986120810728197)
                ·
                  rfl

theorem cell21_1287733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 5].length) (baseStart_1287733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1287733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1287733 prefixEnd_1287733 := by exact prefixLift 1287733
  have htrace : WordTrace (prefixWord ++ tailWord_1287733) baseStart_1287733 baseEnd_1287733 := by
    simpa [prefixWord, tailWord_1287733, baseEnd_1287733] using wordTrace_append hprefix tailTrace_1287733
  have hstable : (prefixWord ++ tailWord_1287733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287733).length < 2 ^ (prefixWord ++ tailWord_1287733).sum := by decide
  have hdescent : baseEnd_1287733 < baseStart_1287733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287750 : List Nat := [6, 1, 1, 1, 3, 2, 7]
def baseStart_1287750 : Nat := 118140960795 + 1287750 * 2 ^ 59
def prefixEnd_1287750 : Nat := 4983230072969 + 3 ^ 40 * 1287750 * 2
def baseEnd_1287750 : Nat := 32653566065552686711247

theorem tailTrace_1287750 : CollatzResearch.WordTrace tailWord_1287750 prefixEnd_1287750 32653566065552686711247 := by
  unfold tailWord_1287750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1467753158897161094861647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31312067389806103357048469 1467753158897161094861647)
  ·
    refine ⟨2201629738345741642292471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1467753158897161094861647 2201629738345741642292471)
    ·
      refine ⟨3302444607518612463438707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2201629738345741642292471 3302444607518612463438707)
      ·
        refine ⟨4953666911277918695158061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3302444607518612463438707 4953666911277918695158061)
        ·
          refine ⟨1857625091729219510684273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4953666911277918695158061 1857625091729219510684273)
          ·
            refine ⟨1393218818796914633013205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1857625091729219510684273 1393218818796914633013205)
            ·
              refine ⟨32653566065552686711247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1393218818796914633013205 32653566065552686711247)
              ·
                rfl

theorem cell21_1287750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 7].length) (baseStart_1287750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1287750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1287750 prefixEnd_1287750 := by exact prefixLift 1287750
  have htrace : WordTrace (prefixWord ++ tailWord_1287750) baseStart_1287750 baseEnd_1287750 := by
    simpa [prefixWord, tailWord_1287750, baseEnd_1287750] using wordTrace_append hprefix tailTrace_1287750
  have hstable : (prefixWord ++ tailWord_1287750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287750).length < 2 ^ (prefixWord ++ tailWord_1287750).sum := by decide
  have hdescent : baseEnd_1287750 < baseStart_1287750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287761 : List Nat := [1, 2, 2, 1, 3, 2, 2, 4, 4]
def baseStart_1287761 : Nat := 118140960795 + 1287761 * 2 ^ 59
def prefixEnd_1287761 : Nat := 4983230072969 + 3 ^ 40 * 1287761 * 2
def baseEnd_1287761 : Nat := 293884604939840605717867

theorem tailTrace_1287761 : CollatzResearch.WordTrace tailWord_1287761 prefixEnd_1287761 293884604939840605717867 := by
  unfold tailWord_1287761
  simp only [CollatzResearch.WordTrace]
  refine ⟨46968502287669303914223137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31312334858446202609482091 46968502287669303914223137)
  ·
    refine ⟨35226376715751977935667353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46968502287669303914223137 35226376715751977935667353)
    ·
      refine ⟨26419782536813983451750515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35226376715751977935667353 26419782536813983451750515)
      ·
        refine ⟨39629673805220975177625773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26419782536813983451750515 39629673805220975177625773)
        ·
          refine ⟨14861127676957865691609665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39629673805220975177625773 14861127676957865691609665)
          ·
            refine ⟨11145845757718399268707249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14861127676957865691609665 11145845757718399268707249)
            ·
              refine ⟨8359384318288799451530437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11145845757718399268707249 8359384318288799451530437)
              ·
                refine ⟨1567384559679149897161957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8359384318288799451530437 1567384559679149897161957)
                ·
                  refine ⟨293884604939840605717867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1567384559679149897161957 293884604939840605717867)
                  ·
                    rfl

theorem cell21_1287761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 4].length) (baseStart_1287761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1287761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1287761 prefixEnd_1287761 := by exact prefixLift 1287761
  have htrace : WordTrace (prefixWord ++ tailWord_1287761) baseStart_1287761 baseEnd_1287761 := by
    simpa [prefixWord, tailWord_1287761, baseEnd_1287761] using wordTrace_append hprefix tailTrace_1287761
  have hstable : (prefixWord ++ tailWord_1287761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287761).length < 2 ^ (prefixWord ++ tailWord_1287761).sum := by decide
  have hdescent : baseEnd_1287761 < baseStart_1287761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287826 : List Nat := [3, 2, 3, 1, 4, 1, 1, 6]
def baseStart_1287826 : Nat := 118140960795 + 1287826 * 2 ^ 59
def prefixEnd_1287826 : Nat := 4983230072969 + 3 ^ 40 * 1287826 * 2
def baseEnd_1287826 : Nat := 97966479608471645711467

theorem tailTrace_1287826 : CollatzResearch.WordTrace tailWord_1287826 prefixEnd_1287826 97966479608471645711467 := by
  unfold tailWord_1287826
  simp only [CollatzResearch.WordTrace]
  refine ⟨11742718258108455003834833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31313915354955880010226221 11742718258108455003834833)
  ·
    refine ⟨8807038693581341252876125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11742718258108455003834833 8807038693581341252876125)
    ·
      refine ⟨3302639510093002969828547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8807038693581341252876125 3302639510093002969828547)
      ·
        refine ⟨4953959265139504454742821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3302639510093002969828547 4953959265139504454742821)
        ·
          refine ⟨928867362213657085264279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4953959265139504454742821 928867362213657085264279)
          ·
            refine ⟨1393301043320485627896419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 928867362213657085264279 1393301043320485627896419)
            ·
              refine ⟨2089951564980728441844629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1393301043320485627896419 2089951564980728441844629)
              ·
                refine ⟨97966479608471645711467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2089951564980728441844629 97966479608471645711467)
                ·
                  rfl

theorem cell21_1287826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 6].length) (baseStart_1287826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1287826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1287826 prefixEnd_1287826 := by exact prefixLift 1287826
  have htrace : WordTrace (prefixWord ++ tailWord_1287826) baseStart_1287826 baseEnd_1287826 := by
    simpa [prefixWord, tailWord_1287826, baseEnd_1287826] using wordTrace_append hprefix tailTrace_1287826
  have hstable : (prefixWord ++ tailWord_1287826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287826).length < 2 ^ (prefixWord ++ tailWord_1287826).sum := by decide
  have hdescent : baseEnd_1287826 < baseStart_1287826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287874 : List Nat := [3, 5, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1287874 : Nat := 118140960795 + 1287874 * 2 ^ 59
def prefixEnd_1287874 : Nat := 4983230072969 + 3 ^ 40 * 1287874 * 2
def baseEnd_1287874 : Nat := 293910393079377520334303

theorem tailTrace_1287874 : CollatzResearch.WordTrace tailWord_1287874 prefixEnd_1287874 293910393079377520334303 := by
  unfold tailWord_1287874
  simp only [CollatzResearch.WordTrace]
  refine ⟨11743155934064981053271669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31315082490839949475391117 11743155934064981053271669)
  ·
    refine ⟨1100920868818591973744219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11743155934064981053271669 1100920868818591973744219)
    ·
      refine ⟨1651381303227887960616329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1100920868818591973744219 1651381303227887960616329)
      ·
        refine ⟨1238535977420915970462247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1651381303227887960616329 1238535977420915970462247)
        ·
          refine ⟨1857803966131373955693371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1238535977420915970462247 1857803966131373955693371)
          ·
            refine ⟨2786705949197060933540057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1857803966131373955693371 2786705949197060933540057)
            ·
              refine ⟨2090029461897795700155043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2786705949197060933540057 2090029461897795700155043)
              ·
                refine ⟨3135044192846693550232565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2090029461897795700155043 3135044192846693550232565)
                ·
                  refine ⟨293910393079377520334303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3135044192846693550232565 293910393079377520334303)
                  ·
                    rfl

theorem cell21_1287874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1287874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1287874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1287874 prefixEnd_1287874 := by exact prefixLift 1287874
  have htrace : WordTrace (prefixWord ++ tailWord_1287874) baseStart_1287874 baseEnd_1287874 := by
    simpa [prefixWord, tailWord_1287874, baseEnd_1287874] using wordTrace_append hprefix tailTrace_1287874
  have hstable : (prefixWord ++ tailWord_1287874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287874).length < 2 ^ (prefixWord ++ tailWord_1287874).sum := by decide
  have hdescent : baseEnd_1287874 < baseStart_1287874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1287992 : List Nat := [2, 1, 2, 1, 3, 3, 4, 2, 3]
def baseStart_1287992 : Nat := 118140960795 + 1287992 * 2 ^ 59
def prefixEnd_1287992 : Nat := 4983230072969 + 3 ^ 40 * 1287992 * 2
def baseEnd_1287992 : Nat := 293937322287035537367395

theorem tailTrace_1287992 : CollatzResearch.WordTrace tailWord_1287992 prefixEnd_1287992 293937322287035537367395 := by
  unfold tailWord_1287992
  simp only [CollatzResearch.WordTrace]
  refine ⟨23488463774916215182941115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31317951699888286910588153 23488463774916215182941115)
  ·
    refine ⟨35232695662374322774411673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23488463774916215182941115 35232695662374322774411673)
    ·
      refine ⟨26424521746780742080808755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35232695662374322774411673 26424521746780742080808755)
      ·
        refine ⟨39636782620171113121213133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26424521746780742080808755 39636782620171113121213133)
        ·
          refine ⟨14863793482564167420454925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39636782620171113121213133 14863793482564167420454925)
          ·
            refine ⟨5573922555961562782670597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14863793482564167420454925 5573922555961562782670597)
            ·
              refine ⟨1045110479242793021750737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5573922555961562782670597 1045110479242793021750737)
              ·
                refine ⟨783832859432094766313053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1045110479242793021750737 783832859432094766313053)
                ·
                  refine ⟨293937322287035537367395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 783832859432094766313053 293937322287035537367395)
                  ·
                    rfl

theorem cell21_1287992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 2, 3].length) (baseStart_1287992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1287992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1287992 prefixEnd_1287992 := by exact prefixLift 1287992
  have htrace : WordTrace (prefixWord ++ tailWord_1287992) baseStart_1287992 baseEnd_1287992 := by
    simpa [prefixWord, tailWord_1287992, baseEnd_1287992] using wordTrace_append hprefix tailTrace_1287992
  have hstable : (prefixWord ++ tailWord_1287992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1287992).length < 2 ^ (prefixWord ++ tailWord_1287992).sum := by decide
  have hdescent : baseEnd_1287992 < baseStart_1287992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1287992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288003 : List Nat := [1, 1, 1, 3, 1, 5, 3, 6]
def baseStart_1288003 : Nat := 118140960795 + 1288003 * 2 ^ 59
def prefixEnd_1288003 : Nat := 4983230072969 + 3 ^ 40 * 1288003 * 2
def baseEnd_1288003 : Nat := 97979944212300654228013

theorem tailTrace_1288003 : CollatzResearch.WordTrace tailWord_1288003 prefixEnd_1288003 97979944212300654228013 := by
  unfold tailWord_1288003
  simp only [CollatzResearch.WordTrace]
  refine ⟨46977328752792579244532663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31318219168528386163021775 46977328752792579244532663)
  ·
    refine ⟨70465993129188868866798995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46977328752792579244532663 70465993129188868866798995)
    ·
      refine ⟨105698989693783303300198493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70465993129188868866798995 105698989693783303300198493)
      ·
        refine ⟨39637121135168738737574435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105698989693783303300198493 39637121135168738737574435)
        ·
          refine ⟨59455681702753108106361653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39637121135168738737574435 59455681702753108106361653)
          ·
            refine ⟨5573970159633103884971405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59455681702753108106361653 5573970159633103884971405)
            ·
              refine ⟨2090238809862413956864277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5573970159633103884971405 2090238809862413956864277)
              ·
                refine ⟨97979944212300654228013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2090238809862413956864277 97979944212300654228013)
                ·
                  rfl

theorem cell21_1288003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 6].length) (baseStart_1288003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1288003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1288003 prefixEnd_1288003 := by exact prefixLift 1288003
  have htrace : WordTrace (prefixWord ++ tailWord_1288003) baseStart_1288003 baseEnd_1288003 := by
    simpa [prefixWord, tailWord_1288003, baseEnd_1288003] using wordTrace_append hprefix tailTrace_1288003
  have hstable : (prefixWord ++ tailWord_1288003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288003).length < 2 ^ (prefixWord ++ tailWord_1288003).sum := by decide
  have hdescent : baseEnd_1288003 < baseStart_1288003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288200 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 6]
def baseStart_1288200 : Nat := 118140960795 + 1288200 * 2 ^ 59
def prefixEnd_1288200 : Nat := 4983230072969 + 3 ^ 40 * 1288200 * 2
def baseEnd_1288200 : Nat := 293984790720873397900303

theorem tailTrace_1288200 : CollatzResearch.WordTrace tailWord_1288200 prefixEnd_1288200 293984790720873397900303 := by
  unfold tailWord_1288200
  simp only [CollatzResearch.WordTrace]
  refine ⟨23492256966539440944727027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31323009288719254592969369 23492256966539440944727027)
  ·
    refine ⟨35238385449809161417090541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23492256966539440944727027 35238385449809161417090541)
    ·
      refine ⟨13214394543678435531408953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35238385449809161417090541 13214394543678435531408953)
      ·
        refine ⟨9910795907758826648556715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13214394543678435531408953 9910795907758826648556715)
        ·
          refine ⟨14866193861638239972835073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9910795907758826648556715 14866193861638239972835073)
          ·
            refine ⟨11149645396228679979626305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14866193861638239972835073 11149645396228679979626305)
            ·
              refine ⟨8362234047171509984719729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11149645396228679979626305 8362234047171509984719729)
              ·
                refine ⟨6271675535378632488539797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8362234047171509984719729 6271675535378632488539797)
                ·
                  refine ⟨293984790720873397900303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6271675535378632488539797 293984790720873397900303)
                  ·
                    rfl

theorem cell21_1288200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_1288200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1288200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1288200 prefixEnd_1288200 := by exact prefixLift 1288200
  have htrace : WordTrace (prefixWord ++ tailWord_1288200) baseStart_1288200 baseEnd_1288200 := by
    simpa [prefixWord, tailWord_1288200, baseEnd_1288200] using wordTrace_append hprefix tailTrace_1288200
  have hstable : (prefixWord ++ tailWord_1288200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288200).length < 2 ^ (prefixWord ++ tailWord_1288200).sum := by decide
  have hdescent : baseEnd_1288200 < baseStart_1288200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288203 : List Nat := [1, 1, 1, 1, 6, 1, 4, 3, 3]
def baseStart_1288203 : Nat := 118140960795 + 1288203 * 2 ^ 59
def prefixEnd_1288203 : Nat := 4983230072969 + 3 ^ 40 * 1288203 * 2
def baseEnd_1288203 : Nat := 293985475361746059350297

theorem tailTrace_1288203 : CollatzResearch.WordTrace tailWord_1288203 prefixEnd_1288203 293985475361746059350297 := by
  unfold tailWord_1288203
  simp only [CollatzResearch.WordTrace]
  refine ⟨46984623352068013401813263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31323082234712008934542175 46984623352068013401813263)
  ·
    refine ⟨70476935028102020102719895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46984623352068013401813263 70476935028102020102719895)
    ·
      refine ⟨105715402542153030154079843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70476935028102020102719895 105715402542153030154079843)
      ·
        refine ⟨158573103813229545231119765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105715402542153030154079843 158573103813229545231119765)
        ·
          refine ⟨7433114241245134932708739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 158573103813229545231119765 7433114241245134932708739)
          ·
            refine ⟨11149671361867702399063109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7433114241245134932708739 11149671361867702399063109)
            ·
              refine ⟨2090563380350194199824333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11149671361867702399063109 2090563380350194199824333)
              ·
                refine ⟨783961267631322824934125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2090563380350194199824333 783961267631322824934125)
                ·
                  refine ⟨293985475361746059350297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 783961267631322824934125 293985475361746059350297)
                  ·
                    rfl

theorem cell21_1288203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 3].length) (baseStart_1288203 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1288203 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1288203 prefixEnd_1288203 := by exact prefixLift 1288203
  have htrace : WordTrace (prefixWord ++ tailWord_1288203) baseStart_1288203 baseEnd_1288203 := by
    simpa [prefixWord, tailWord_1288203, baseEnd_1288203] using wordTrace_append hprefix tailTrace_1288203
  have hstable : (prefixWord ++ tailWord_1288203).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288203).length < 2 ^ (prefixWord ++ tailWord_1288203).sum := by decide
  have hdescent : baseEnd_1288203 < baseStart_1288203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288254 : List Nat := [4, 2, 1, 3, 3, 1, 1, 3, 3]
def baseStart_1288254 : Nat := 118140960795 + 1288254 * 2 ^ 59
def prefixEnd_1288254 : Nat := 4983230072969 + 3 ^ 40 * 1288254 * 2
def baseEnd_1288254 : Nat := 293997114256581304000193

theorem tailTrace_1288254 : CollatzResearch.WordTrace tailWord_1288254 prefixEnd_1288254 293997114256581304000193 := by
  unfold tailWord_1288254
  simp only [CollatzResearch.WordTrace]
  refine ⟨5873310434360406138989977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31324322316588832741279877 5873310434360406138989977)
  ·
    refine ⟨4404982825770304604242483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5873310434360406138989977 4404982825770304604242483)
    ·
      refine ⟨6607474238655456906363725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4404982825770304604242483 6607474238655456906363725)
      ·
        refine ⟨2477802839495796339886397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6607474238655456906363725 2477802839495796339886397)
        ·
          refine ⟨929176064810923627457399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2477802839495796339886397 929176064810923627457399)
          ·
            refine ⟨1393764097216385441186099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929176064810923627457399 1393764097216385441186099)
            ·
              refine ⟨2090646145824578161779149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1393764097216385441186099 2090646145824578161779149)
              ·
                refine ⟨783992304684216810667181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2090646145824578161779149 783992304684216810667181)
                ·
                  refine ⟨293997114256581304000193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 783992304684216810667181 293997114256581304000193)
                  ·
                    rfl

theorem cell21_1288254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_1288254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1288254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1288254 prefixEnd_1288254 := by exact prefixLift 1288254
  have htrace : WordTrace (prefixWord ++ tailWord_1288254) baseStart_1288254 baseEnd_1288254 := by
    simpa [prefixWord, tailWord_1288254, baseEnd_1288254] using wordTrace_append hprefix tailTrace_1288254
  have hstable : (prefixWord ++ tailWord_1288254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288254).length < 2 ^ (prefixWord ++ tailWord_1288254).sum := by decide
  have hdescent : baseEnd_1288254 < baseStart_1288254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288293 : List Nat := [1, 3, 1, 3, 2, 3, 1, 3, 4]
def baseStart_1288293 : Nat := 118140960795 + 1288293 * 2 ^ 59
def prefixEnd_1288293 : Nat := 4983230072969 + 3 ^ 40 * 1288293 * 2
def baseEnd_1288293 : Nat := 294006014587925902850113

theorem tailTrace_1288293 : CollatzResearch.WordTrace tailWord_1288293 prefixEnd_1288293 294006014587925902850113 := by
  unfold tailWord_1288293
  simp only [CollatzResearch.WordTrace]
  refine ⟨46987905921741958772589533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31325270614494639181726355 46987905921741958772589533)
  ·
    refine ⟨17620464720653234539721075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46987905921741958772589533 17620464720653234539721075)
    ·
      refine ⟨26430697080979851809581613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17620464720653234539721075 26430697080979851809581613)
      ·
        refine ⟨9911511405367444428593105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26430697080979851809581613 9911511405367444428593105)
        ·
          refine ⟨7433633554025583321444829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9911511405367444428593105 7433633554025583321444829)
          ·
            refine ⟨2787612582759593745541811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7433633554025583321444829 2787612582759593745541811)
            ·
              refine ⟨4181418874139390618312717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2787612582759593745541811 4181418874139390618312717)
              ·
                refine ⟨1568032077802271481867269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4181418874139390618312717 1568032077802271481867269)
                ·
                  refine ⟨294006014587925902850113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1568032077802271481867269 294006014587925902850113)
                  ·
                    rfl

theorem cell21_1288293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_1288293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1288293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1288293 prefixEnd_1288293 := by exact prefixLift 1288293
  have htrace : WordTrace (prefixWord ++ tailWord_1288293) baseStart_1288293 baseEnd_1288293 := by
    simpa [prefixWord, tailWord_1288293, baseEnd_1288293] using wordTrace_append hprefix tailTrace_1288293
  have hstable : (prefixWord ++ tailWord_1288293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288293).length < 2 ^ (prefixWord ++ tailWord_1288293).sum := by decide
  have hdescent : baseEnd_1288293 < baseStart_1288293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288338 : List Nat := [3, 2, 3, 1, 1, 1, 2, 3, 5]
def baseStart_1288338 : Nat := 118140960795 + 1288338 * 2 ^ 59
def prefixEnd_1288338 : Nat := 4983230072969 + 3 ^ 40 * 1288338 * 2
def baseEnd_1288338 : Nat := 294016284201015824600021

theorem tailTrace_1288338 : CollatzResearch.WordTrace tailWord_1288338 prefixEnd_1288338 294016284201015824600021 := by
  unfold tailWord_1288338
  simp only [CollatzResearch.WordTrace]
  refine ⟨11747386801644732864494417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31326364804385954305318445 11747386801644732864494417)
  ·
    refine ⟨8810540101233549648370813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11747386801644732864494417 8810540101233549648370813)
    ·
      refine ⟨3303952537962581118139055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8810540101233549648370813 3303952537962581118139055)
      ·
        refine ⟨4955928806943871677208583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3303952537962581118139055 4955928806943871677208583)
        ·
          refine ⟨7433893210415807515812875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4955928806943871677208583 7433893210415807515812875)
          ·
            refine ⟨11150839815623711273719313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7433893210415807515812875 11150839815623711273719313)
            ·
              refine ⟨8363129861717783455289485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11150839815623711273719313 8363129861717783455289485)
              ·
                refine ⟨3136173698144168795733557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8363129861717783455289485 3136173698144168795733557)
                ·
                  refine ⟨294016284201015824600021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3136173698144168795733557 294016284201015824600021)
                  ·
                    rfl

theorem cell21_1288338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_1288338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1288338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1288338 prefixEnd_1288338 := by exact prefixLift 1288338
  have htrace : WordTrace (prefixWord ++ tailWord_1288338) baseStart_1288338 baseEnd_1288338 := by
    simpa [prefixWord, tailWord_1288338, baseEnd_1288338] using wordTrace_append hprefix tailTrace_1288338
  have hstable : (prefixWord ++ tailWord_1288338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288338).length < 2 ^ (prefixWord ++ tailWord_1288338).sum := by decide
  have hdescent : baseEnd_1288338 < baseStart_1288338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288411 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 8]
def baseStart_1288411 : Nat := 118140960795 + 1288411 * 2 ^ 59
def prefixEnd_1288411 : Nat := 4983230072969 + 3 ^ 40 * 1288411 * 2
def baseEnd_1288411 : Nat := 294032943795583919883205

theorem tailTrace_1288411 : CollatzResearch.WordTrace tailWord_1288411 prefixEnd_1288411 294032943795583919883205 := by
  unfold tailWord_1288411
  simp only [CollatzResearch.WordTrace]
  refine ⟨46992209735314464925385087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31328139823542976616923391 46992209735314464925385087)
  ·
    refine ⟨70488314602971697388077631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46992209735314464925385087 70488314602971697388077631)
    ·
      refine ⟨105732471904457546082116447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70488314602971697388077631 105732471904457546082116447)
      ·
        refine ⟨158598707856686319123174671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105732471904457546082116447 158598707856686319123174671)
        ·
          refine ⟨237898061785029478684762007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158598707856686319123174671 237898061785029478684762007)
          ·
            refine ⟨356847092677544218027143011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237898061785029478684762007 356847092677544218027143011)
            ·
              refine ⟨535270639016316327040714517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356847092677544218027143011 535270639016316327040714517)
              ·
                refine ⟨25090811203889827830033493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 535270639016316327040714517 25090811203889827830033493)
                ·
                  refine ⟨294032943795583919883205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25090811203889827830033493 294032943795583919883205)
                  ·
                    rfl

theorem cell21_1288411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 8].length) (baseStart_1288411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1288411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1288411 prefixEnd_1288411 := by exact prefixLift 1288411
  have htrace : WordTrace (prefixWord ++ tailWord_1288411) baseStart_1288411 baseEnd_1288411 := by
    simpa [prefixWord, tailWord_1288411, baseEnd_1288411] using wordTrace_append hprefix tailTrace_1288411
  have hstable : (prefixWord ++ tailWord_1288411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288411).length < 2 ^ (prefixWord ++ tailWord_1288411).sum := by decide
  have hdescent : baseEnd_1288411 < baseStart_1288411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288431 : List Nat := [1, 1, 2, 1, 6, 1, 3, 3, 3]
def baseStart_1288431 : Nat := 118140960795 + 1288431 * 2 ^ 59
def prefixEnd_1288431 : Nat := 4983230072969 + 3 ^ 40 * 1288431 * 2
def baseEnd_1288431 : Nat := 294037508068068329549831

theorem tailTrace_1288431 : CollatzResearch.WordTrace tailWord_1288431 prefixEnd_1288431 294037508068068329549831 := by
  unfold tailWord_1288431
  simp only [CollatzResearch.WordTrace]
  refine ⟨46992939195242008341113147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31328626130161338894075431 46992939195242008341113147)
  ·
    refine ⟨70489408792863012511669721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46992939195242008341113147 70489408792863012511669721)
    ·
      refine ⟨52867056594647259383752291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70489408792863012511669721 52867056594647259383752291)
      ·
        refine ⟨79300584891970889075628437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52867056594647259383752291 79300584891970889075628437)
        ·
          refine ⟨3717214916811135425420083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79300584891970889075628437 3717214916811135425420083)
          ·
            refine ⟨5575822375216703138130125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3717214916811135425420083 5575822375216703138130125)
            ·
              refine ⟨2090933390706263676798797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5575822375216703138130125 2090933390706263676798797)
              ·
                refine ⟨784100021514848878799549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2090933390706263676798797 784100021514848878799549)
                ·
                  refine ⟨294037508068068329549831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 784100021514848878799549 294037508068068329549831)
                  ·
                    rfl

theorem cell21_1288431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 3].length) (baseStart_1288431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1288431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1288431 prefixEnd_1288431 := by exact prefixLift 1288431
  have htrace : WordTrace (prefixWord ++ tailWord_1288431) baseStart_1288431 baseEnd_1288431 := by
    simpa [prefixWord, tailWord_1288431, baseEnd_1288431] using wordTrace_append hprefix tailTrace_1288431
  have hstable : (prefixWord ++ tailWord_1288431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288431).length < 2 ^ (prefixWord ++ tailWord_1288431).sum := by decide
  have hdescent : baseEnd_1288431 < baseStart_1288431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288442 : List Nat := [3, 1, 1, 1, 1, 5, 9]
def baseStart_1288442 : Nat := 118140960795 + 1288442 * 2 ^ 59
def prefixEnd_1288442 : Nat := 4983230072969 + 3 ^ 40 * 1288442 * 2
def baseEnd_1288442 : Nat := 32671113157548306096275

theorem tailTrace_1288442 : CollatzResearch.WordTrace tailWord_1288442 prefixEnd_1288442 32671113157548306096275 := by
  unfold tailWord_1288442
  simp only [CollatzResearch.WordTrace]
  refine ⟨11748335099550539304940895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31328893598801438146509053 11748335099550539304940895)
  ·
    refine ⟨17622502649325808957411343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11748335099550539304940895 17622502649325808957411343)
    ·
      refine ⟨26433753973988713436117015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17622502649325808957411343 26433753973988713436117015)
      ·
        refine ⟨39650630960983070154175523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26433753973988713436117015 39650630960983070154175523)
        ·
          refine ⟨59475946441474605231263285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39650630960983070154175523 59475946441474605231263285)
          ·
            refine ⟨5575869978888244240430933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59475946441474605231263285 5575869978888244240430933)
            ·
              refine ⟨32671113157548306096275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5575869978888244240430933 32671113157548306096275)
              ·
                rfl

theorem cell21_1288442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 9].length) (baseStart_1288442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1288442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1288442 prefixEnd_1288442 := by exact prefixLift 1288442
  have htrace : WordTrace (prefixWord ++ tailWord_1288442) baseStart_1288442 baseEnd_1288442 := by
    simpa [prefixWord, tailWord_1288442, baseEnd_1288442] using wordTrace_append hprefix tailTrace_1288442
  have hstable : (prefixWord ++ tailWord_1288442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288442).length < 2 ^ (prefixWord ++ tailWord_1288442).sum := by decide
  have hdescent : baseEnd_1288442 < baseStart_1288442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288504 : List Nat := [2, 1, 2, 1, 3, 1, 3, 4, 4]
def baseStart_1288504 : Nat := 118140960795 + 1288504 * 2 ^ 59
def prefixEnd_1288504 : Nat := 4983230072969 + 3 ^ 40 * 1288504 * 2
def baseEnd_1288504 : Nat := 294054167662636424833015

theorem tailTrace_1288504 : CollatzResearch.WordTrace tailWord_1288504 prefixEnd_1288504 294054167662636424833015 := by
  unfold tailWord_1288504
  simp only [CollatzResearch.WordTrace]
  refine ⟨23497800861988770904260283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31330401149318361205680377 23497800861988770904260283)
  ·
    refine ⟨35246701292983156356390425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23497800861988770904260283 35246701292983156356390425)
    ·
      refine ⟨26435025969737367267292819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35246701292983156356390425 26435025969737367267292819)
      ·
        refine ⟨39652538954606050900939229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26435025969737367267292819 39652538954606050900939229)
        ·
          refine ⟨14869702107977269087852211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39652538954606050900939229 14869702107977269087852211)
          ·
            refine ⟨22304553161965903631778317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14869702107977269087852211 22304553161965903631778317)
            ·
              refine ⟨8364207435737213861916869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22304553161965903631778317 8364207435737213861916869)
              ·
                refine ⟨1568288894200727599109413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8364207435737213861916869 1568288894200727599109413)
                ·
                  refine ⟨294054167662636424833015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1568288894200727599109413 294054167662636424833015)
                  ·
                    rfl

theorem cell21_1288504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 4].length) (baseStart_1288504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1288504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1288504 prefixEnd_1288504 := by exact prefixLift 1288504
  have htrace : WordTrace (prefixWord ++ tailWord_1288504) baseStart_1288504 baseEnd_1288504 := by
    simpa [prefixWord, tailWord_1288504, baseEnd_1288504] using wordTrace_append hprefix tailTrace_1288504
  have hstable : (prefixWord ++ tailWord_1288504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288504).length < 2 ^ (prefixWord ++ tailWord_1288504).sum := by decide
  have hdescent : baseEnd_1288504 < baseStart_1288504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288535 : List Nat := [1, 1, 3, 2, 3, 1, 5, 5]
def baseStart_1288535 : Nat := 118140960795 + 1288535 * 2 ^ 59
def prefixEnd_1288535 : Nat := 4983230072969 + 3 ^ 40 * 1288535 * 2
def baseEnd_1288535 : Nat := 98020414094995753272095

theorem tailTrace_1288535 : CollatzResearch.WordTrace tailWord_1288535 prefixEnd_1288535 98020414094995753272095 := by
  unfold tailWord_1288535
  simp only [CollatzResearch.WordTrace]
  refine ⟨46996732386865234102899059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31331154924576822735266039 46996732386865234102899059)
  ·
    refine ⟨70495098580297851154348589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46996732386865234102899059 70495098580297851154348589)
    ·
      refine ⟨26435661967611694182880721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70495098580297851154348589 26435661967611694182880721)
      ·
        refine ⟨19826746475708770637160541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26435661967611694182880721 19826746475708770637160541)
        ·
          refine ⟨7435029928390788988935203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19826746475708770637160541 7435029928390788988935203)
          ·
            refine ⟨11152544892586183483402805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7435029928390788988935203 11152544892586183483402805)
            ·
              refine ⟨1045551083679954701569013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11152544892586183483402805 1045551083679954701569013)
              ·
                refine ⟨98020414094995753272095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1045551083679954701569013 98020414094995753272095)
                ·
                  rfl

theorem cell21_1288535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 5].length) (baseStart_1288535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1288535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1288535 prefixEnd_1288535 := by exact prefixLift 1288535
  have htrace : WordTrace (prefixWord ++ tailWord_1288535) baseStart_1288535 baseEnd_1288535 := by
    simpa [prefixWord, tailWord_1288535, baseEnd_1288535] using wordTrace_append hprefix tailTrace_1288535
  have hstable : (prefixWord ++ tailWord_1288535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288535).length < 2 ^ (prefixWord ++ tailWord_1288535).sum := by decide
  have hdescent : baseEnd_1288535 < baseStart_1288535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288563 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 6]
def baseStart_1288563 : Nat := 118140960795 + 1288563 * 2 ^ 59
def prefixEnd_1288563 : Nat := 4983230072969 + 3 ^ 40 * 1288563 * 2
def baseEnd_1288563 : Nat := 294067632266465433349561

theorem tailTrace_1288563 : CollatzResearch.WordTrace tailWord_1288563 prefixEnd_1288563 294067632266465433349561 := by
  unfold tailWord_1288563
  simp only [CollatzResearch.WordTrace]
  refine ⟨46997753630763794884918343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31331835753842529923278895 46997753630763794884918343)
  ·
    refine ⟨70496630446145692327377515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46997753630763794884918343 70496630446145692327377515)
    ·
      refine ⟨105744945669218538491066273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70496630446145692327377515 105744945669218538491066273)
      ·
        refine ⟨79308709251913903868299705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105744945669218538491066273 79308709251913903868299705)
        ·
          refine ⟨59481531938935427901224779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79308709251913903868299705 59481531938935427901224779)
          ·
            refine ⟨89222297908403141851837169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59481531938935427901224779 89222297908403141851837169)
            ·
              refine ⟨66916723431302356388877877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89222297908403141851837169 66916723431302356388877877)
              ·
                refine ⟨6273442821684595911457301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66916723431302356388877877 6273442821684595911457301)
                ·
                  refine ⟨294067632266465433349561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6273442821684595911457301 294067632266465433349561)
                  ·
                    rfl

theorem cell21_1288563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 6].length) (baseStart_1288563 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1288563 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1288563 prefixEnd_1288563 := by exact prefixLift 1288563
  have htrace : WordTrace (prefixWord ++ tailWord_1288563) baseStart_1288563 baseEnd_1288563 := by
    simpa [prefixWord, tailWord_1288563, baseEnd_1288563] using wordTrace_append hprefix tailTrace_1288563
  have hstable : (prefixWord ++ tailWord_1288563).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288563).length < 2 ^ (prefixWord ++ tailWord_1288563).sum := by decide
  have hdescent : baseEnd_1288563 < baseStart_1288563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288586 : List Nat := [3, 1, 2, 5, 2, 1, 2, 5]
def baseStart_1288586 : Nat := 118140960795 + 1288586 * 2 ^ 59
def prefixEnd_1288586 : Nat := 4983230072969 + 3 ^ 40 * 1288586 * 2
def baseEnd_1288586 : Nat := 98024293726607501488727

theorem tailTrace_1288586 : CollatzResearch.WordTrace tailWord_1288586 prefixEnd_1288586 98024293726607501488727 := by
  unfold tailWord_1288586
  simp only [CollatzResearch.WordTrace]
  refine ⟨11749648127420117453251403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31332395006453646542003741 11749648127420117453251403)
  ·
    refine ⟨17624472191130176179877105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11749648127420117453251403 17624472191130176179877105)
    ·
      refine ⟨13218354143347632134907829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17624472191130176179877105 13218354143347632134907829)
      ·
        refine ⟨1239220700938840512647609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13218354143347632134907829 1239220700938840512647609)
        ·
          refine ⟨929415525704130384485707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1239220700938840512647609 929415525704130384485707)
          ·
            refine ⟨1394123288556195576728561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929415525704130384485707 1394123288556195576728561)
            ·
              refine ⟨1045592466417146682546421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1394123288556195576728561 1045592466417146682546421)
              ·
                refine ⟨98024293726607501488727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1045592466417146682546421 98024293726607501488727)
                ·
                  rfl

theorem cell21_1288586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 5].length) (baseStart_1288586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1288586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1288586 prefixEnd_1288586 := by exact prefixLift 1288586
  have htrace : WordTrace (prefixWord ++ tailWord_1288586) baseStart_1288586 baseEnd_1288586 := by
    simpa [prefixWord, tailWord_1288586, baseEnd_1288586] using wordTrace_append hprefix tailTrace_1288586
  have hstable : (prefixWord ++ tailWord_1288586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288586).length < 2 ^ (prefixWord ++ tailWord_1288586).sum := by decide
  have hdescent : baseEnd_1288586 < baseStart_1288586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288600 : List Nat := [2, 1, 2, 5, 1, 3, 1, 3, 3]
def baseStart_1288600 : Nat := 118140960795 + 1288600 * 2 ^ 59
def prefixEnd_1288600 : Nat := 4983230072969 + 3 ^ 40 * 1288600 * 2
def baseEnd_1288600 : Nat := 294076076170561591232819

theorem tailTrace_1288600 : CollatzResearch.WordTrace tailWord_1288600 prefixEnd_1288600 294076076170561591232819 := by
  unfold tailWord_1288600
  simp only [CollatzResearch.WordTrace]
  refine ⟨23499551565814875102007627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31332735421086500136010169 23499551565814875102007627)
  ·
    refine ⟨35249327348722312653011441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23499551565814875102007627 35249327348722312653011441)
    ·
      refine ⟨26436995511541734489758581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35249327348722312653011441 26436995511541734489758581)
      ·
        refine ⟨2478468329207037608414867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26436995511541734489758581 2478468329207037608414867)
        ·
          refine ⟨3717702493810556412622301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2478468329207037608414867 3717702493810556412622301)
          ·
            refine ⟨1394138435178958654733363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3717702493810556412622301 1394138435178958654733363)
            ·
              refine ⟨2091207652768437982100045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1394138435178958654733363 2091207652768437982100045)
              ·
                refine ⟨784202869788164243287517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2091207652768437982100045 784202869788164243287517)
                ·
                  refine ⟨294076076170561591232819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 784202869788164243287517 294076076170561591232819)
                  ·
                    rfl

theorem cell21_1288600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 3].length) (baseStart_1288600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1288600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1288600 prefixEnd_1288600 := by exact prefixLift 1288600
  have htrace : WordTrace (prefixWord ++ tailWord_1288600) baseStart_1288600 baseEnd_1288600 := by
    simpa [prefixWord, tailWord_1288600, baseEnd_1288600] using wordTrace_append hprefix tailTrace_1288600
  have hstable : (prefixWord ++ tailWord_1288600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288600).length < 2 ^ (prefixWord ++ tailWord_1288600).sum := by decide
  have hdescent : baseEnd_1288600 < baseStart_1288600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288701 : List Nat := [1, 4, 1, 1, 1, 3, 3, 2, 5]
def baseStart_1288701 : Nat := 118140960795 + 1288701 * 2 ^ 59
def prefixEnd_1288701 : Nat := 4983230072969 + 3 ^ 40 * 1288701 * 2
def baseEnd_1288701 : Nat := 294099125746607860049279

theorem tailTrace_1288701 : CollatzResearch.WordTrace tailWord_1288701 prefixEnd_1288701 294099125746607860049279 := by
  unfold tailWord_1288701
  simp only [CollatzResearch.WordTrace]
  refine ⟨47002786904263844453441957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31335191269509229635627971 47002786904263844453441957)
  ·
    refine ⟨8813022544549470835020367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47002786904263844453441957 8813022544549470835020367)
    ·
      refine ⟨13219533816824206252530551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8813022544549470835020367 13219533816824206252530551)
      ·
        refine ⟨19829300725236309378795827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13219533816824206252530551 19829300725236309378795827)
        ·
          refine ⟨29743951087854464068193741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19829300725236309378795827 29743951087854464068193741)
          ·
            refine ⟨11153981657945424025572653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29743951087854464068193741 11153981657945424025572653)
            ·
              refine ⟨4182743121729534009589745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11153981657945424025572653 4182743121729534009589745)
              ·
                refine ⟨3137057341297150507192309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4182743121729534009589745 3137057341297150507192309)
                ·
                  refine ⟨294099125746607860049279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3137057341297150507192309 294099125746607860049279)
                  ·
                    rfl

theorem cell21_1288701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_1288701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1288701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1288701 prefixEnd_1288701 := by exact prefixLift 1288701
  have htrace : WordTrace (prefixWord ++ tailWord_1288701) baseStart_1288701 baseEnd_1288701 := by
    simpa [prefixWord, tailWord_1288701, baseEnd_1288701] using wordTrace_append hprefix tailTrace_1288701
  have hstable : (prefixWord ++ tailWord_1288701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288701).length < 2 ^ (prefixWord ++ tailWord_1288701).sum := by decide
  have hdescent : baseEnd_1288701 < baseStart_1288701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288710 : List Nat := [6, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_1288710 : Nat := 118140960795 + 1288710 * 2 ^ 59
def prefixEnd_1288710 : Nat := 4983230072969 + 3 ^ 40 * 1288710 * 2
def baseEnd_1288710 : Nat := 294101179669225844399261

theorem tailTrace_1288710 : CollatzResearch.WordTrace tailWord_1288710 prefixEnd_1288710 294101179669225844399261 := by
  unfold tailWord_1288710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1468847348788476218453737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31335410107487492660346389 1468847348788476218453737)
  ·
    refine ⟨1101635511591357163840303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1468847348788476218453737 1101635511591357163840303)
    ·
      refine ⟨1652453267387035745760455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1101635511591357163840303 1652453267387035745760455)
      ·
        refine ⟨2478679901080553618640683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1652453267387035745760455 2478679901080553618640683)
        ·
          refine ⟨3718019851620830427961025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2478679901080553618640683 3718019851620830427961025)
          ·
            refine ⟨2788514888715622820970769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3718019851620830427961025 2788514888715622820970769)
            ·
              refine ⟨2091386166536717115728077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2788514888715622820970769 2091386166536717115728077)
              ·
                refine ⟨784269812451268918398029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2091386166536717115728077 784269812451268918398029)
                ·
                  refine ⟨294101179669225844399261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 784269812451268918398029 294101179669225844399261)
                  ·
                    rfl

theorem cell21_1288710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_1288710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1288710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1288710 prefixEnd_1288710 := by exact prefixLift 1288710
  have htrace : WordTrace (prefixWord ++ tailWord_1288710) baseStart_1288710 baseEnd_1288710 := by
    simpa [prefixWord, tailWord_1288710, baseEnd_1288710] using wordTrace_append hprefix tailTrace_1288710
  have hstable : (prefixWord ++ tailWord_1288710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288710).length < 2 ^ (prefixWord ++ tailWord_1288710).sum := by decide
  have hdescent : baseEnd_1288710 < baseStart_1288710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288732 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 6]
def baseStart_1288732 : Nat := 118140960795 + 1288732 * 2 ^ 59
def prefixEnd_1288732 : Nat := 4983230072969 + 3 ^ 40 * 1288732 * 2
def baseEnd_1288732 : Nat := 294106200368958695032549

theorem tailTrace_1288732 : CollatzResearch.WordTrace tailWord_1288732 prefixEnd_1288732 294106200368958695032549 := by
  unfold tailWord_1288732
  simp only [CollatzResearch.WordTrace]
  refine ⟨23501958783575768373910225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31335945044767691165213633 23501958783575768373910225)
  ·
    refine ⟨17626469087681826280432669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23501958783575768373910225 17626469087681826280432669)
    ·
      refine ⟨6609925907880684855162251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17626469087681826280432669 6609925907880684855162251)
      ·
        refine ⟨9914888861821027282743377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6609925907880684855162251 9914888861821027282743377)
        ·
          refine ⟨7436166646365770462057533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9914888861821027282743377 7436166646365770462057533)
          ·
            refine ⟨2788562492387163923271575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7436166646365770462057533 2788562492387163923271575)
            ·
              refine ⟨4182843738580745884907363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2788562492387163923271575 4182843738580745884907363)
              ·
                refine ⟨6274265607871118827361045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4182843738580745884907363 6274265607871118827361045)
                ·
                  refine ⟨294106200368958695032549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6274265607871118827361045 294106200368958695032549)
                  ·
                    rfl

theorem cell21_1288732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_1288732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1288732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1288732 prefixEnd_1288732 := by exact prefixLift 1288732
  have htrace : WordTrace (prefixWord ++ tailWord_1288732) baseStart_1288732 baseEnd_1288732 := by
    simpa [prefixWord, tailWord_1288732, baseEnd_1288732] using wordTrace_append hprefix tailTrace_1288732
  have hstable : (prefixWord ++ tailWord_1288732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288732).length < 2 ^ (prefixWord ++ tailWord_1288732).sum := by decide
  have hdescent : baseEnd_1288732 < baseStart_1288732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288791 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 6]
def baseStart_1288791 : Nat := 118140960795 + 1288791 * 2 ^ 59
def prefixEnd_1288791 : Nat := 4983230072969 + 3 ^ 40 * 1288791 * 2
def baseEnd_1288791 : Nat := 294119664972787703549095

theorem tailTrace_1288791 : CollatzResearch.WordTrace tailWord_1288791 prefixEnd_1288791 294119664972787703549095 := by
  unfold tailWord_1288791
  simp only [CollatzResearch.WordTrace]
  refine ⟨47006069473937789824218227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31337379649291859882812151 47006069473937789824218227)
  ·
    refine ⟨70509104210906684736327341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47006069473937789824218227 70509104210906684736327341)
    ·
      refine ⟨26440914079090006776122753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70509104210906684736327341 26440914079090006776122753)
      ·
        refine ⟨19830685559317505082092065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26440914079090006776122753 19830685559317505082092065)
        ·
          refine ⟨14873014169488128811569049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19830685559317505082092065 14873014169488128811569049)
          ·
            refine ⟨11154760627116096608676787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14873014169488128811569049 11154760627116096608676787)
            ·
              refine ⟨16732140940674144913015181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11154760627116096608676787 16732140940674144913015181)
              ·
                refine ⟨6274552852752804342380693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16732140940674144913015181 6274552852752804342380693)
                ·
                  refine ⟨294119664972787703549095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6274552852752804342380693 294119664972787703549095)
                  ·
                    rfl

theorem cell21_1288791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 6].length) (baseStart_1288791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1288791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1288791 prefixEnd_1288791 := by exact prefixLift 1288791
  have htrace : WordTrace (prefixWord ++ tailWord_1288791) baseStart_1288791 baseEnd_1288791 := by
    simpa [prefixWord, tailWord_1288791, baseEnd_1288791] using wordTrace_append hprefix tailTrace_1288791
  have hstable : (prefixWord ++ tailWord_1288791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288791).length < 2 ^ (prefixWord ++ tailWord_1288791).sum := by decide
  have hdescent : baseEnd_1288791 < baseStart_1288791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288887 : List Nat := [1, 1, 3, 1, 6, 1, 2, 3, 3]
def baseStart_1288887 : Nat := 118140960795 + 1288887 * 2 ^ 59
def prefixEnd_1288887 : Nat := 4983230072969 + 3 ^ 40 * 1288887 * 2
def baseEnd_1288887 : Nat := 294141573480712869948899

theorem tailTrace_1288887 : CollatzResearch.WordTrace tailWord_1288887 prefixEnd_1288887 294141573480712869948899 := by
  unfold tailWord_1288887
  simp only [CollatzResearch.WordTrace]
  refine ⟨47009570881589998219712915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31339713921059998813141943 47009570881589998219712915)
  ·
    refine ⟨70514356322384997329569373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47009570881589998219712915 70514356322384997329569373)
    ·
      refine ⟨26442883620894373998588515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70514356322384997329569373 26442883620894373998588515)
      ·
        refine ⟨39664325431341560997882773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26442883620894373998588515 39664325431341560997882773)
        ·
          refine ⟨1859265254594135671775755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39664325431341560997882773 1859265254594135671775755)
          ·
            refine ⟨2788897881891203507663633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1859265254594135671775755 2788897881891203507663633)
            ·
              refine ⟨2091673411418402630747725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2788897881891203507663633 2091673411418402630747725)
              ·
                refine ⟨784377529281900986530397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2091673411418402630747725 784377529281900986530397)
                ·
                  refine ⟨294141573480712869948899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 784377529281900986530397 294141573480712869948899)
                  ·
                    rfl

theorem cell21_1288887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 3].length) (baseStart_1288887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1288887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1288887 prefixEnd_1288887 := by exact prefixLift 1288887
  have htrace : WordTrace (prefixWord ++ tailWord_1288887) baseStart_1288887 baseEnd_1288887 := by
    simpa [prefixWord, tailWord_1288887, baseEnd_1288887] using wordTrace_append hprefix tailTrace_1288887
  have hstable : (prefixWord ++ tailWord_1288887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288887).length < 2 ^ (prefixWord ++ tailWord_1288887).sum := by decide
  have hdescent : baseEnd_1288887 < baseStart_1288887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288929 : List Nat := [1, 2, 3, 1, 4, 1, 2, 2, 5]
def baseStart_1288929 : Nat := 118140960795 + 1288929 * 2 ^ 59
def prefixEnd_1288929 : Nat := 4983230072969 + 3 ^ 40 * 1288929 * 2
def baseEnd_1288929 : Nat := 294151158452930130248813

theorem tailTrace_1288929 : CollatzResearch.WordTrace tailWord_1288929 prefixEnd_1288929 294151158452930130248813 := by
  unfold tailWord_1288929
  simp only [CollatzResearch.WordTrace]
  refine ⟨47011102747437839392741841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31340735164958559595161227 47011102747437839392741841)
  ·
    refine ⟨35258327060578379544556381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47011102747437839392741841 35258327060578379544556381)
    ·
      refine ⟨13221872647716892329208643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35258327060578379544556381 13221872647716892329208643)
      ·
        refine ⟨19832808971575338493812965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13221872647716892329208643 19832808971575338493812965)
        ·
          refine ⟨3718651682170375967589931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19832808971575338493812965 3718651682170375967589931)
          ·
            refine ⟨5577977523255563951384897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3718651682170375967589931 5577977523255563951384897)
            ·
              refine ⟨4183483142441672963538673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5577977523255563951384897 4183483142441672963538673)
              ·
                refine ⟨3137612356831254722654005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4183483142441672963538673 3137612356831254722654005)
                ·
                  refine ⟨294151158452930130248813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3137612356831254722654005 294151158452930130248813)
                  ·
                    rfl

theorem cell21_1288929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_1288929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1288929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1288929 prefixEnd_1288929 := by exact prefixLift 1288929
  have htrace : WordTrace (prefixWord ++ tailWord_1288929) baseStart_1288929 baseEnd_1288929 := by
    simpa [prefixWord, tailWord_1288929, baseEnd_1288929] using wordTrace_append hprefix tailTrace_1288929
  have hstable : (prefixWord ++ tailWord_1288929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288929).length < 2 ^ (prefixWord ++ tailWord_1288929).sum := by decide
  have hdescent : baseEnd_1288929 < baseStart_1288929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288943 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 6]
def baseStart_1288943 : Nat := 118140960795 + 1288943 * 2 ^ 59
def prefixEnd_1288943 : Nat := 4983230072969 + 3 ^ 40 * 1288943 * 2
def baseEnd_1288943 : Nat := 294154353443669217015451

theorem tailTrace_1288943 : CollatzResearch.WordTrace tailWord_1288943 prefixEnd_1288943 294154353443669217015451 := by
  unfold tailWord_1288943
  simp only [CollatzResearch.WordTrace]
  refine ⟨47011613369387119783751483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31341075579591413189167655 47011613369387119783751483)
  ·
    refine ⟨70517420054080679675627225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47011613369387119783751483 70517420054080679675627225)
    ·
      refine ⟨52888065040560509756720419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70517420054080679675627225 52888065040560509756720419)
      ·
        refine ⟨79332097560840764635080629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52888065040560509756720419 79332097560840764635080629)
        ·
          refine ⟨7437384146328821684538809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79332097560840764635080629 7437384146328821684538809)
          ·
            refine ⟨5578038109746616263404107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7437384146328821684538809 5578038109746616263404107)
            ·
              refine ⟨8367057164619924395106161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5578038109746616263404107 8367057164619924395106161)
              ·
                refine ⟨6275292873464943296329621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8367057164619924395106161 6275292873464943296329621)
                ·
                  refine ⟨294154353443669217015451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6275292873464943296329621 294154353443669217015451)
                  ·
                    rfl

theorem cell21_1288943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 6].length) (baseStart_1288943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1288943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1288943 prefixEnd_1288943 := by exact prefixLift 1288943
  have htrace : WordTrace (prefixWord ++ tailWord_1288943) baseStart_1288943 baseEnd_1288943 := by
    simpa [prefixWord, tailWord_1288943, baseEnd_1288943] using wordTrace_append hprefix tailTrace_1288943
  have hstable : (prefixWord ++ tailWord_1288943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288943).length < 2 ^ (prefixWord ++ tailWord_1288943).sum := by decide
  have hdescent : baseEnd_1288943 < baseStart_1288943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1288949 : List Nat := [1, 3, 6, 1, 1, 2, 7]
def baseStart_1288949 : Nat := 118140960795 + 1288949 * 2 ^ 59
def prefixEnd_1288949 : Nat := 4983230072969 + 3 ^ 40 * 1288949 * 2
def baseEnd_1288949 : Nat := 32683969191712726657271

theorem tailTrace_1288949 : CollatzResearch.WordTrace tailWord_1288949 prefixEnd_1288949 32683969191712726657271 := by
  unfold tailWord_1288949
  simp only [CollatzResearch.WordTrace]
  refine ⟨47011832207365382808469901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31341221471576921872313267 47011832207365382808469901)
  ·
    refine ⟨17629437077762018553176213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47011832207365382808469901 17629437077762018553176213)
    ·
      refine ⟨826379863020094619680135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17629437077762018553176213 826379863020094619680135)
      ·
        refine ⟨1239569794530141929520203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 826379863020094619680135 1239569794530141929520203)
        ·
          refine ⟨1859354691795212894280305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1239569794530141929520203 1859354691795212894280305)
          ·
            refine ⟨1394516018846409670710229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1859354691795212894280305 1394516018846409670710229)
            ·
              refine ⟨32683969191712726657271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1394516018846409670710229 32683969191712726657271)
              ·
                rfl

theorem cell21_1288949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 7].length) (baseStart_1288949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1288949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1288949 prefixEnd_1288949 := by exact prefixLift 1288949
  have htrace : WordTrace (prefixWord ++ tailWord_1288949) baseStart_1288949 baseEnd_1288949 := by
    simpa [prefixWord, tailWord_1288949, baseEnd_1288949] using wordTrace_append hprefix tailTrace_1288949
  have hstable : (prefixWord ++ tailWord_1288949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1288949).length < 2 ^ (prefixWord ++ tailWord_1288949).sum := by decide
  have hdescent : baseEnd_1288949 < baseStart_1288949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1288949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289014 : List Nat := [5, 1, 2, 2, 3, 1, 2, 2, 3]
def baseStart_1289014 : Nat := 118140960795 + 1289014 * 2 ^ 59
def prefixEnd_1289014 : Nat := 4983230072969 + 3 ^ 40 * 1289014 * 2
def baseEnd_1289014 : Nat := 294170556610988871331973

theorem tailTrace_1289014 : CollatzResearch.WordTrace tailWord_1289014 prefixEnd_1289014 294170556610988871331973 := by
  unfold tailWord_1289014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2938387684508118681849131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31342801968086599273057397 2938387684508118681849131)
  ·
    refine ⟨4407581526762178022773697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2938387684508118681849131 4407581526762178022773697)
    ·
      refine ⟨3305686145071633517080273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4407581526762178022773697 3305686145071633517080273)
      ·
        refine ⟨2479264608803725137810205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3305686145071633517080273 2479264608803725137810205)
        ·
          refine ⟨929724228301396926678827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2479264608803725137810205 929724228301396926678827)
          ·
            refine ⟨1394586342452095390018241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929724228301396926678827 1394586342452095390018241)
            ·
              refine ⟨1045939756839071542513681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1394586342452095390018241 1045939756839071542513681)
              ·
                refine ⟨784454817629303656885261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1045939756839071542513681 784454817629303656885261)
                ·
                  refine ⟨294170556610988871331973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 784454817629303656885261 294170556610988871331973)
                  ·
                    rfl

theorem cell21_1289014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_1289014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289014 prefixEnd_1289014 := by exact prefixLift 1289014
  have htrace : WordTrace (prefixWord ++ tailWord_1289014) baseStart_1289014 baseEnd_1289014 := by
    simpa [prefixWord, tailWord_1289014, baseEnd_1289014] using wordTrace_append hprefix tailTrace_1289014
  have hstable : (prefixWord ++ tailWord_1289014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289014).length < 2 ^ (prefixWord ++ tailWord_1289014).sum := by decide
  have hdescent : baseEnd_1289014 < baseStart_1289014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289025 : List Nat := [1, 2, 5, 3, 2, 1, 1, 6]
def baseStart_1289025 : Nat := 118140960795 + 1289025 * 2 ^ 59
def prefixEnd_1289025 : Nat := 4983230072969 + 3 ^ 40 * 1289025 * 2
def baseEnd_1289025 : Nat := 98057688986951765549539

theorem tailTrace_1289025 : CollatzResearch.WordTrace tailWord_1289025 prefixEnd_1289025 98057688986951765549539 := by
  unfold tailWord_1289025
  simp only [CollatzResearch.WordTrace]
  refine ⟨47014604155090047788236529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31343069436726698525491019 47014604155090047788236529)
  ·
    refine ⟨35260953116317535841177397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47014604155090047788236529 35260953116317535841177397)
    ·
      refine ⟨3305714354654768985110381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35260953116317535841177397 3305714354654768985110381)
      ·
        refine ⟨1239642882995538369416393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3305714354654768985110381 1239642882995538369416393)
        ·
          refine ⟨929732162246653777062295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1239642882995538369416393 929732162246653777062295)
          ·
            refine ⟨1394598243369980665593443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929732162246653777062295 1394598243369980665593443)
            ·
              refine ⟨2091897365054970998390165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1394598243369980665593443 2091897365054970998390165)
              ·
                refine ⟨98057688986951765549539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2091897365054970998390165 98057688986951765549539)
                ·
                  rfl

theorem cell21_1289025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 6].length) (baseStart_1289025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289025 prefixEnd_1289025 := by exact prefixLift 1289025
  have htrace : WordTrace (prefixWord ++ tailWord_1289025) baseStart_1289025 baseEnd_1289025 := by
    simpa [prefixWord, tailWord_1289025, baseEnd_1289025] using wordTrace_append hprefix tailTrace_1289025
  have hstable : (prefixWord ++ tailWord_1289025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289025).length < 2 ^ (prefixWord ++ tailWord_1289025).sum := by decide
  have hdescent : baseEnd_1289025 < baseStart_1289025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289036 : List Nat := [2, 2, 1, 3, 3, 1, 2, 3, 4]
def baseStart_1289036 : Nat := 118140960795 + 1289036 * 2 ^ 59
def prefixEnd_1289036 : Nat := 4983230072969 + 3 ^ 40 * 1289036 * 2
def baseEnd_1289036 : Nat := 294175577310721721965261

theorem tailTrace_1289036 : CollatzResearch.WordTrace tailWord_1289036 prefixEnd_1289036 294175577310721721965261 := by
  unfold tailWord_1289036
  simp only [CollatzResearch.WordTrace]
  refine ⟨23507502679025098333443481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31343336905366797777924641 23507502679025098333443481)
  ·
    refine ⟨17630627009268823750082611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23507502679025098333443481 17630627009268823750082611)
    ·
      refine ⟨26445940513903235625123917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17630627009268823750082611 26445940513903235625123917)
      ·
        refine ⟨9917227692713713359421469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26445940513903235625123917 9917227692713713359421469)
        ·
          refine ⟨3718960384767642509783051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9917227692713713359421469 3718960384767642509783051)
          ·
            refine ⟨5578440577151463764674577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3718960384767642509783051 5578440577151463764674577)
            ·
              refine ⟨4183830432863597823505933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5578440577151463764674577 4183830432863597823505933)
              ·
                refine ⟨1568936412323849183814725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4183830432863597823505933 1568936412323849183814725)
                ·
                  refine ⟨294175577310721721965261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1568936412323849183814725 294175577310721721965261)
                  ·
                    rfl

theorem cell21_1289036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_1289036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289036 prefixEnd_1289036 := by exact prefixLift 1289036
  have htrace : WordTrace (prefixWord ++ tailWord_1289036) baseStart_1289036 baseEnd_1289036 := by
    simpa [prefixWord, tailWord_1289036, baseEnd_1289036] using wordTrace_append hprefix tailTrace_1289036
  have hstable : (prefixWord ++ tailWord_1289036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289036).length < 2 ^ (prefixWord ++ tailWord_1289036).sum := by decide
  have hdescent : baseEnd_1289036 < baseStart_1289036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289070 : List Nat := [4, 1, 2, 3, 2, 2, 1, 2, 4]
def baseStart_1289070 : Nat := 118140960795 + 1289070 * 2 ^ 59
def prefixEnd_1289070 : Nat := 4983230072969 + 3 ^ 40 * 1289070 * 2
def baseEnd_1289070 : Nat := 294183336573945218398525

theorem tailTrace_1289070 : CollatzResearch.WordTrace tailWord_1289070 prefixEnd_1289070 294183336573945218398525 := by
  unfold tailWord_1289070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5877030679990877559203083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31344163626618013649083109 5877030679990877559203083)
  ·
    refine ⟨8815546019986316338804625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5877030679990877559203083 8815546019986316338804625)
    ·
      refine ⟨6611659514989737254103469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8815546019986316338804625 6611659514989737254103469)
      ·
        refine ⟨2479372318121151470288801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6611659514989737254103469 2479372318121151470288801)
        ·
          refine ⟨1859529238590863602716601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2479372318121151470288801 1859529238590863602716601)
          ·
            refine ⟨1394646928943147702037451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1859529238590863602716601 1394646928943147702037451)
            ·
              refine ⟨2091970393414721553056177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1394646928943147702037451 2091970393414721553056177)
              ·
                refine ⟨1568977795061041164792133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2091970393414721553056177 1568977795061041164792133)
                ·
                  refine ⟨294183336573945218398525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1568977795061041164792133 294183336573945218398525)
                  ·
                    rfl

theorem cell21_1289070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_1289070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289070 prefixEnd_1289070 := by exact prefixLift 1289070
  have htrace : WordTrace (prefixWord ++ tailWord_1289070) baseStart_1289070 baseEnd_1289070 := by
    simpa [prefixWord, tailWord_1289070, baseEnd_1289070] using wordTrace_append hprefix tailTrace_1289070
  have hstable : (prefixWord ++ tailWord_1289070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289070).length < 2 ^ (prefixWord ++ tailWord_1289070).sum := by decide
  have hdescent : baseEnd_1289070 < baseStart_1289070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289081 : List Nat := [1, 2, 1, 3, 2, 4, 2, 1, 5]
def baseStart_1289081 : Nat := 118140960795 + 1289081 * 2 ^ 59
def prefixEnd_1289081 : Nat := 4983230072969 + 3 ^ 40 * 1289081 * 2
def baseEnd_1289081 : Nat := 294185846923811643715169

theorem tailTrace_1289081 : CollatzResearch.WordTrace tailWord_1289081 prefixEnd_1289081 294185846923811643715169 := by
  unfold tailWord_1289081
  simp only [CollatzResearch.WordTrace]
  refine ⟨47016646642887169352275097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31344431095258112901516731 47016646642887169352275097)
  ·
    refine ⟨35262484982165377014206323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47016646642887169352275097 35262484982165377014206323)
    ·
      refine ⟨52893727473248065521309485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35262484982165377014206323 52893727473248065521309485)
      ·
        refine ⟨19835147802468024570491057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52893727473248065521309485 19835147802468024570491057)
        ·
          refine ⟨14876360851851018427868293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19835147802468024570491057 14876360851851018427868293)
          ·
            refine ⟨2789317659722065955225305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14876360851851018427868293 2789317659722065955225305)
            ·
              refine ⟨2091988244791549466418979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2789317659722065955225305 2091988244791549466418979)
              ·
                refine ⟨3137982367187324199628469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2091988244791549466418979 3137982367187324199628469)
                ·
                  refine ⟨294185846923811643715169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3137982367187324199628469 294185846923811643715169)
                  ·
                    rfl

theorem cell21_1289081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 5].length) (baseStart_1289081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289081 prefixEnd_1289081 := by exact prefixLift 1289081
  have htrace : WordTrace (prefixWord ++ tailWord_1289081) baseStart_1289081 baseEnd_1289081 := by
    simpa [prefixWord, tailWord_1289081, baseEnd_1289081] using wordTrace_append hprefix tailTrace_1289081
  have hstable : (prefixWord ++ tailWord_1289081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289081).length < 2 ^ (prefixWord ++ tailWord_1289081).sum := by decide
  have hdescent : baseEnd_1289081 < baseStart_1289081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289191 : List Nat := [1, 1, 5, 2, 2, 1, 4, 2, 3]
def baseStart_1289191 : Nat := 118140960795 + 1289191 * 2 ^ 59
def prefixEnd_1289191 : Nat := 4983230072969 + 3 ^ 40 * 1289191 * 2
def baseEnd_1289191 : Nat := 294210950422475896881611

theorem tailTrace_1289191 : CollatzResearch.WordTrace tailWord_1289191 prefixEnd_1289191 294210950422475896881611 := by
  unfold tailWord_1289191
  simp only [CollatzResearch.WordTrace]
  refine ⟨47020658672488658138779427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31347105781659105425852951 47020658672488658138779427)
  ·
    refine ⟨70530988008732987208169141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47020658672488658138779427 70530988008732987208169141)
    ·
      refine ⟨6612280125818717550765857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70530988008732987208169141 6612280125818717550765857)
      ·
        refine ⟨4959210094364038163074393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6612280125818717550765857 4959210094364038163074393)
        ·
          refine ⟨3719407570773028622305795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4959210094364038163074393 3719407570773028622305795)
          ·
            refine ⟨5579111356159542933458693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3719407570773028622305795 5579111356159542933458693)
            ·
              refine ⟨1046083379279914300023505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5579111356159542933458693 1046083379279914300023505)
              ·
                refine ⟨784562534459935725017629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1046083379279914300023505 784562534459935725017629)
                ·
                  refine ⟨294210950422475896881611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 784562534459935725017629 294210950422475896881611)
                  ·
                    rfl

theorem cell21_1289191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 3].length) (baseStart_1289191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289191 prefixEnd_1289191 := by exact prefixLift 1289191
  have htrace : WordTrace (prefixWord ++ tailWord_1289191) baseStart_1289191 baseEnd_1289191 := by
    simpa [prefixWord, tailWord_1289191, baseEnd_1289191] using wordTrace_append hprefix tailTrace_1289191
  have hstable : (prefixWord ++ tailWord_1289191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289191).length < 2 ^ (prefixWord ++ tailWord_1289191).sum := by decide
  have hdescent : baseEnd_1289191 < baseStart_1289191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289247 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 6]
def baseStart_1289247 : Nat := 118140960795 + 1289247 * 2 ^ 59
def prefixEnd_1289247 : Nat := 4983230072969 + 3 ^ 40 * 1289247 * 2
def baseEnd_1289247 : Nat := 294223730385432243948163

theorem tailTrace_1289247 : CollatzResearch.WordTrace tailWord_1289247 prefixEnd_1289247 294223730385432243948163 := by
  unfold tailWord_1289247
  simp only [CollatzResearch.WordTrace]
  refine ⟨47022701160285779702817995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31348467440190519801878663 47022701160285779702817995)
  ·
    refine ⟨70534051740428669554226993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47022701160285779702817995 70534051740428669554226993)
    ·
      refine ⟨52900538805321502165670245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70534051740428669554226993 52900538805321502165670245)
      ·
        refine ⟨9918851025997781656063171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52900538805321502165670245 9918851025997781656063171)
        ·
          refine ⟨14878276538996672484094757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9918851025997781656063171 14878276538996672484094757)
          ·
            refine ⟨2789676851061876090767767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14878276538996672484094757 2789676851061876090767767)
            ·
              refine ⟨4184515276592814136151651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2789676851061876090767767 4184515276592814136151651)
              ·
                refine ⟨6276772914889221204227477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4184515276592814136151651 6276772914889221204227477)
                ·
                  refine ⟨294223730385432243948163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6276772914889221204227477 294223730385432243948163)
                  ·
                    rfl

theorem cell21_1289247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 6].length) (baseStart_1289247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289247 prefixEnd_1289247 := by exact prefixLift 1289247
  have htrace : WordTrace (prefixWord ++ tailWord_1289247) baseStart_1289247 baseEnd_1289247 := by
    simpa [prefixWord, tailWord_1289247, baseEnd_1289247] using wordTrace_append hprefix tailTrace_1289247
  have hstable : (prefixWord ++ tailWord_1289247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289247).length < 2 ^ (prefixWord ++ tailWord_1289247).sum := by decide
  have hdescent : baseEnd_1289247 < baseStart_1289247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289250 : List Nat := [3, 3, 1, 1, 1, 3, 2, 4, 3]
def baseStart_1289250 : Nat := 118140960795 + 1289250 * 2 ^ 59
def prefixEnd_1289250 : Nat := 4983230072969 + 3 ^ 40 * 1289250 * 2
def baseEnd_1289250 : Nat := 294224415026304905398157

theorem tailTrace_1289250 : CollatzResearch.WordTrace tailWord_1289250 prefixEnd_1289250 294224415026304905398157 := by
  unfold tailWord_1289250
  simp only [CollatzResearch.WordTrace]
  refine ⟨11755702644818727803794301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31348540386183274143451469 11755702644818727803794301)
  ·
    refine ⟨4408388491807022926422863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11755702644818727803794301 4408388491807022926422863)
    ·
      refine ⟨6612582737710534389634295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4408388491807022926422863 6612582737710534389634295)
      ·
        refine ⟨9918874106565801584451443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6612582737710534389634295 9918874106565801584451443)
        ·
          refine ⟨14878311159848702376677165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9918874106565801584451443 14878311159848702376677165)
          ·
            refine ⟨5579366684943263391253937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14878311159848702376677165 5579366684943263391253937)
            ·
              refine ⟨4184525013707447543440453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5579366684943263391253937 4184525013707447543440453)
              ·
                refine ⟨784598440070146414395085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4184525013707447543440453 784598440070146414395085)
                ·
                  refine ⟨294224415026304905398157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 784598440070146414395085 294224415026304905398157)
                  ·
                    rfl

theorem cell21_1289250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_1289250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289250 prefixEnd_1289250 := by exact prefixLift 1289250
  have htrace : WordTrace (prefixWord ++ tailWord_1289250) baseStart_1289250 baseEnd_1289250 := by
    simpa [prefixWord, tailWord_1289250, baseEnd_1289250] using wordTrace_append hprefix tailTrace_1289250
  have hstable : (prefixWord ++ tailWord_1289250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289250).length < 2 ^ (prefixWord ++ tailWord_1289250).sum := by decide
  have hdescent : baseEnd_1289250 < baseStart_1289250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289264 : List Nat := [2, 1, 1, 1, 2, 4, 5, 1, 4]
def baseStart_1289264 : Nat := 118140960795 + 1289264 * 2 ^ 59
def prefixEnd_1289264 : Nat := 4983230072969 + 3 ^ 40 * 1289264 * 2
def baseEnd_1289264 : Nat := 294227610017043992164795

theorem tailTrace_1289264 : CollatzResearch.WordTrace tailWord_1289264 prefixEnd_1289264 294227610017043992164795 := by
  unfold tailWord_1289264
  simp only [CollatzResearch.WordTrace]
  refine ⟨23511660600612095803093423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31348880800816127737457897 23511660600612095803093423)
  ·
    refine ⟨35267490900918143704640135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23511660600612095803093423 35267490900918143704640135)
    ·
      refine ⟨52901236351377215556960203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35267490900918143704640135 52901236351377215556960203)
      ·
        refine ⟨79351854527065823335440305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52901236351377215556960203 79351854527065823335440305)
        ·
          refine ⟨59513890895299367501580229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79351854527065823335440305 59513890895299367501580229)
          ·
            refine ⟨11158854542868631406546293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59513890895299367501580229 11158854542868631406546293)
            ·
              refine ⟨1046142613393934194363715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11158854542868631406546293 1046142613393934194363715)
              ·
                refine ⟨1569213920090901291545573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1046142613393934194363715 1569213920090901291545573)
                ·
                  refine ⟨294227610017043992164795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1569213920090901291545573 294227610017043992164795)
                  ·
                    rfl

theorem cell21_1289264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 4].length) (baseStart_1289264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289264 prefixEnd_1289264 := by exact prefixLift 1289264
  have htrace : WordTrace (prefixWord ++ tailWord_1289264) baseStart_1289264 baseEnd_1289264 := by
    simpa [prefixWord, tailWord_1289264, baseEnd_1289264] using wordTrace_append hprefix tailTrace_1289264
  have hstable : (prefixWord ++ tailWord_1289264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289264).length < 2 ^ (prefixWord ++ tailWord_1289264).sum := by decide
  have hdescent : baseEnd_1289264 < baseStart_1289264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289427 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 9]
def baseStart_1289427 : Nat := 118140960795 + 1289427 * 2 ^ 59
def prefixEnd_1289427 : Nat := 4983230072969 + 3 ^ 40 * 1289427 * 2
def baseEnd_1289427 : Nat := 294264808837791930947795

theorem tailTrace_1289427 : CollatzResearch.WordTrace tailWord_1289427 prefixEnd_1289427 294264808837791930947795 := by
  unfold tailWord_1289427
  simp only [CollatzResearch.WordTrace]
  refine ⟨47029266299633670444370535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31352844199755780296247023 47029266299633670444370535)
  ·
    refine ⟨70543899449450505666555803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47029266299633670444370535 70543899449450505666555803)
    ·
      refine ⟨105815849174175758499833705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70543899449450505666555803 105815849174175758499833705)
      ·
        refine ⟨79361886880631818874875279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105815849174175758499833705 79361886880631818874875279)
        ·
          refine ⟨119042830320947728312312919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79361886880631818874875279 119042830320947728312312919)
          ·
            refine ⟨178564245481421592468469379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119042830320947728312312919 178564245481421592468469379)
            ·
              refine ⟨267846368222132388702704069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178564245481421592468469379 267846368222132388702704069)
              ·
                refine ⟨50221194041649822881757013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 267846368222132388702704069 50221194041649822881757013)
                ·
                  refine ⟨294264808837791930947795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50221194041649822881757013 294264808837791930947795)
                  ·
                    rfl

theorem cell21_1289427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 9].length) (baseStart_1289427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289427 prefixEnd_1289427 := by exact prefixLift 1289427
  have htrace : WordTrace (prefixWord ++ tailWord_1289427) baseStart_1289427 baseEnd_1289427 := by
    simpa [prefixWord, tailWord_1289427, baseEnd_1289427] using wordTrace_append hprefix tailTrace_1289427
  have hstable : (prefixWord ++ tailWord_1289427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289427).length < 2 ^ (prefixWord ++ tailWord_1289427).sum := by decide
  have hdescent : baseEnd_1289427 < baseStart_1289427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289444 : List Nat := [2, 3, 1, 1, 1, 2, 4, 2, 5]
def baseStart_1289444 : Nat := 118140960795 + 1289444 * 2 ^ 59
def prefixEnd_1289444 : Nat := 4983230072969 + 3 ^ 40 * 1289444 * 2
def baseEnd_1289444 : Nat := 294268688469403679164427

theorem tailTrace_1289444 : CollatzResearch.WordTrace tailWord_1289444 prefixEnd_1289444 294268688469403679164427 := by
  unfold tailWord_1289444
  simp only [CollatzResearch.WordTrace]
  refine ⟨23514943170286041173869693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31353257560381388231826257 23514943170286041173869693)
  ·
    refine ⟨8818103688857265440201135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23514943170286041173869693 8818103688857265440201135)
    ·
      refine ⟨13227155533285898160301703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8818103688857265440201135 13227155533285898160301703)
      ·
        refine ⟨19840733299928847240452555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13227155533285898160301703 19840733299928847240452555)
        ·
          refine ⟨29761099949893270860678833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19840733299928847240452555 29761099949893270860678833)
          ·
            refine ⟨22320824962419953145509125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29761099949893270860678833 22320824962419953145509125)
            ·
              refine ⟨4185154680453741214782961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22320824962419953145509125 4185154680453741214782961)
              ·
                refine ⟨3138866010340305911087221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4185154680453741214782961 3138866010340305911087221)
                ·
                  refine ⟨294268688469403679164427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3138866010340305911087221 294268688469403679164427)
                  ·
                    rfl

theorem cell21_1289444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_1289444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289444 prefixEnd_1289444 := by exact prefixLift 1289444
  have htrace : WordTrace (prefixWord ++ tailWord_1289444) baseStart_1289444 baseEnd_1289444 := by
    simpa [prefixWord, tailWord_1289444, baseEnd_1289444] using wordTrace_append hprefix tailTrace_1289444
  have hstable : (prefixWord ++ tailWord_1289444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289444).length < 2 ^ (prefixWord ++ tailWord_1289444).sum := by decide
  have hdescent : baseEnd_1289444 < baseStart_1289444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289489 : List Nat := [1, 2, 2, 1, 1, 4, 4, 6]
def baseStart_1289489 : Nat := 118140960795 + 1289489 * 2 ^ 59
def prefixEnd_1289489 : Nat := 4983230072969 + 3 ^ 40 * 1289489 * 2
def baseEnd_1289489 : Nat := 98092986027497866971445

theorem tailTrace_1289489 : CollatzResearch.WordTrace tailWord_1289489 prefixEnd_1289489 98092986027497866971445 := by
  unfold tailWord_1289489
  simp only [CollatzResearch.WordTrace]
  refine ⟨47031527625409055033127521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31354351750272703355418347 47031527625409055033127521)
  ·
    refine ⟨35273645719056791274845641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47031527625409055033127521 35273645719056791274845641)
    ·
      refine ⟨26455234289292593456134231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35273645719056791274845641 26455234289292593456134231)
      ·
        refine ⟨39682851433938890184201347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26455234289292593456134231 39682851433938890184201347)
        ·
          refine ⟨59524277150908335276302021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39682851433938890184201347 59524277150908335276302021)
          ·
            refine ⟨11160801965795312864306629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59524277150908335276302021 11160801965795312864306629)
            ·
              refine ⟨2092650368586621162057493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11160801965795312864306629 2092650368586621162057493)
              ·
                refine ⟨98092986027497866971445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2092650368586621162057493 98092986027497866971445)
                ·
                  rfl

theorem cell21_1289489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 6].length) (baseStart_1289489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289489 prefixEnd_1289489 := by exact prefixLift 1289489
  have htrace : WordTrace (prefixWord ++ tailWord_1289489) baseStart_1289489 baseEnd_1289489 := by
    simpa [prefixWord, tailWord_1289489, baseEnd_1289489] using wordTrace_append hprefix tailTrace_1289489
  have hstable : (prefixWord ++ tailWord_1289489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289489).length < 2 ^ (prefixWord ++ tailWord_1289489).sum := by decide
  have hdescent : baseEnd_1289489 < baseStart_1289489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289526 : List Nat := [5, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_1289526 : Nat := 118140960795 + 1289526 * 2 ^ 59
def prefixEnd_1289526 : Nat := 4983230072969 + 3 ^ 40 * 1289526 * 2
def baseEnd_1289526 : Nat := 294287401986589758797593

theorem tailTrace_1289526 : CollatzResearch.WordTrace tailWord_1289526 prefixEnd_1289526 294287401986589758797593 := by
  unfold tailWord_1289526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2939554820392188147014027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31355251417516673568149621 2939554820392188147014027)
  ·
    refine ⟨4409332230588282220521041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2939554820392188147014027 4409332230588282220521041)
    ·
      refine ⟨3306999172941211665390781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4409332230588282220521041 3306999172941211665390781)
      ·
        refine ⟨1240124689852954374521543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3306999172941211665390781 1240124689852954374521543)
        ·
          refine ⟨1860187034779431561782315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1240124689852954374521543 1860187034779431561782315)
          ·
            refine ⟨2790280552169147342673473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1860187034779431561782315 2790280552169147342673473)
            ·
              refine ⟨2092710414126860507005105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2790280552169147342673473 2092710414126860507005105)
              ·
                refine ⟨1569532810595145380253829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2092710414126860507005105 1569532810595145380253829)
                ·
                  refine ⟨294287401986589758797593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1569532810595145380253829 294287401986589758797593)
                  ·
                    rfl

theorem cell21_1289526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_1289526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289526 prefixEnd_1289526 := by exact prefixLift 1289526
  have htrace : WordTrace (prefixWord ++ tailWord_1289526) baseStart_1289526 baseEnd_1289526 := by
    simpa [prefixWord, tailWord_1289526, baseEnd_1289526] using wordTrace_append hprefix tailTrace_1289526
  have hstable : (prefixWord ++ tailWord_1289526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289526).length < 2 ^ (prefixWord ++ tailWord_1289526).sum := by decide
  have hdescent : baseEnd_1289526 < baseStart_1289526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289596 : List Nat := [2, 2, 2, 1, 1, 1, 6, 1, 5]
def baseStart_1289596 : Nat := 118140960795 + 1289596 * 2 ^ 59
def prefixEnd_1289596 : Nat := 4983230072969 + 3 ^ 40 * 1289596 * 2
def baseEnd_1289596 : Nat := 294303376940285192630783

theorem tailTrace_1289596 : CollatzResearch.WordTrace tailWord_1289596 prefixEnd_1289596 294303376940285192630783 := by
  unfold tailWord_1289596
  simp only [CollatzResearch.WordTrace]
  refine ⟨23517715118010706153636321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31356953490680941538181761 23517715118010706153636321)
  ·
    refine ⟨17638286338508029615227241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23517715118010706153636321 17638286338508029615227241)
    ·
      refine ⟨13228714753881022211420431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17638286338508029615227241 13228714753881022211420431)
      ·
        refine ⟨19843072130821533317130647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13228714753881022211420431 19843072130821533317130647)
        ·
          refine ⟨29764608196232299975695971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19843072130821533317130647 29764608196232299975695971)
          ·
            refine ⟨44646912294348449963543957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29764608196232299975695971 44646912294348449963543957)
            ·
              refine ⟨2092824013797583592041123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44646912294348449963543957 2092824013797583592041123)
              ·
                refine ⟨3139236020696375388061685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2092824013797583592041123 3139236020696375388061685)
                ·
                  refine ⟨294303376940285192630783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3139236020696375388061685 294303376940285192630783)
                  ·
                    rfl

theorem cell21_1289596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_1289596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289596 prefixEnd_1289596 := by exact prefixLift 1289596
  have htrace : WordTrace (prefixWord ++ tailWord_1289596) baseStart_1289596 baseEnd_1289596 := by
    simpa [prefixWord, tailWord_1289596, baseEnd_1289596] using wordTrace_append hprefix tailTrace_1289596
  have hstable : (prefixWord ++ tailWord_1289596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289596).length < 2 ^ (prefixWord ++ tailWord_1289596).sum := by decide
  have hdescent : baseEnd_1289596 < baseStart_1289596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289602 : List Nat := [3, 4, 2, 1, 1, 2, 3, 1, 4]
def baseStart_1289602 : Nat := 118140960795 + 1289602 * 2 ^ 59
def prefixEnd_1289602 : Nat := 4983230072969 + 3 ^ 40 * 1289602 * 2
def baseEnd_1289602 : Nat := 294304746222030515530771

theorem tailTrace_1289602 : CollatzResearch.WordTrace tailWord_1289602 prefixEnd_1289602 294304746222030515530771 := by
  unfold tailWord_1289602
  simp only [CollatzResearch.WordTrace]
  refine ⟨11758912268499918832997765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31357099382666450221327373 11758912268499918832997765)
  ·
    refine ⟨2204796050343734781187081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11758912268499918832997765 2204796050343734781187081)
    ·
      refine ⟨1653597037757801085890311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2204796050343734781187081 1653597037757801085890311)
      ·
        refine ⟨2480395556636701628835467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1653597037757801085890311 2480395556636701628835467)
        ·
          refine ⟨3720593334955052443253201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2480395556636701628835467 3720593334955052443253201)
          ·
            refine ⟨2790445001216289332439901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3720593334955052443253201 2790445001216289332439901)
            ·
              refine ⟨1046416875456108499664963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2790445001216289332439901 1046416875456108499664963)
              ·
                refine ⟨1569625313184162749497445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1046416875456108499664963 1569625313184162749497445)
                ·
                  refine ⟨294304746222030515530771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1569625313184162749497445 294304746222030515530771)
                  ·
                    rfl

theorem cell21_1289602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_1289602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289602 prefixEnd_1289602 := by exact prefixLift 1289602
  have htrace : WordTrace (prefixWord ++ tailWord_1289602) baseStart_1289602 baseEnd_1289602 := by
    simpa [prefixWord, tailWord_1289602, baseEnd_1289602] using wordTrace_append hprefix tailTrace_1289602
  have hstable : (prefixWord ++ tailWord_1289602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289602).length < 2 ^ (prefixWord ++ tailWord_1289602).sum := by decide
  have hdescent : baseEnd_1289602 < baseStart_1289602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289703 : List Nat := [1, 1, 5, 2, 1, 2, 1, 4, 4]
def baseStart_1289703 : Nat := 118140960795 + 1289703 * 2 ^ 59
def prefixEnd_1289703 : Nat := 4983230072969 + 3 ^ 40 * 1289703 * 2
def baseEnd_1289703 : Nat := 294327795798076784347231

theorem tailTrace_1289703 : CollatzResearch.WordTrace tailWord_1289703 prefixEnd_1289703 294327795798076784347231 := by
  unfold tailWord_1289703
  simp only [CollatzResearch.WordTrace]
  refine ⟨47039332846633769581417763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31359555231089179720945175 47039332846633769581417763)
  ·
    refine ⟨70558999269950654372126645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47039332846633769581417763 70558999269950654372126645)
    ·
      refine ⟨6614906181557873847386873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70558999269950654372126645 6614906181557873847386873)
      ·
        refine ⟨4961179636168405385540155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6614906181557873847386873 4961179636168405385540155)
        ·
          refine ⟨7441769454252608078310233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4961179636168405385540155 7441769454252608078310233)
          ·
            refine ⟨5581327090689456058732675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7441769454252608078310233 5581327090689456058732675)
            ·
              refine ⟨8371990636034184088099013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5581327090689456058732675 8371990636034184088099013)
              ·
                refine ⟨1569748244256409516518565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8371990636034184088099013 1569748244256409516518565)
                ·
                  refine ⟨294327795798076784347231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1569748244256409516518565 294327795798076784347231)
                  ·
                    rfl

theorem cell21_1289703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 4].length) (baseStart_1289703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289703 prefixEnd_1289703 := by exact prefixLift 1289703
  have htrace : WordTrace (prefixWord ++ tailWord_1289703) baseStart_1289703 baseEnd_1289703 := by
    simpa [prefixWord, tailWord_1289703, baseEnd_1289703] using wordTrace_append hprefix tailTrace_1289703
  have hstable : (prefixWord ++ tailWord_1289703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289703).length < 2 ^ (prefixWord ++ tailWord_1289703).sum := by decide
  have hdescent : baseEnd_1289703 < baseStart_1289703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289706 : List Nat := [3, 1, 3, 1, 4, 1, 1, 4, 3]
def baseStart_1289706 : Nat := 118140960795 + 1289706 * 2 ^ 59
def prefixEnd_1289706 : Nat := 4983230072969 + 3 ^ 40 * 1289706 * 2
def baseEnd_1289706 : Nat := 294328480438949445797225

theorem tailTrace_1289706 : CollatzResearch.WordTrace tailWord_1289706 prefixEnd_1289706 294328480438949445797225 := by
  unfold tailWord_1289706
  simp only [CollatzResearch.WordTrace]
  refine ⟨11759860566405725273444243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31359628177081934062517981 11759860566405725273444243)
  ·
    refine ⟨17639790849608587910166365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11759860566405725273444243 17639790849608587910166365)
    ·
      refine ⟨6614921568603220466312387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17639790849608587910166365 6614921568603220466312387)
      ·
        refine ⟨9922382352904830699468581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6614921568603220466312387 9922382352904830699468581)
        ·
          refine ⟨1860446691169655756150359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9922382352904830699468581 1860446691169655756150359)
          ·
            refine ⟨2790670036754483634225539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1860446691169655756150359 2790670036754483634225539)
            ·
              refine ⟨4186005055131725451338309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2790670036754483634225539 4186005055131725451338309)
              ·
                refine ⟨784875947837198522125933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4186005055131725451338309 784875947837198522125933)
                ·
                  refine ⟨294328480438949445797225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 784875947837198522125933 294328480438949445797225)
                  ·
                    rfl

theorem cell21_1289706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 3].length) (baseStart_1289706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289706 prefixEnd_1289706 := by exact prefixLift 1289706
  have htrace : WordTrace (prefixWord ++ tailWord_1289706) baseStart_1289706 baseEnd_1289706 := by
    simpa [prefixWord, tailWord_1289706, baseEnd_1289706] using wordTrace_append hprefix tailTrace_1289706
  have hstable : (prefixWord ++ tailWord_1289706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289706).length < 2 ^ (prefixWord ++ tailWord_1289706).sum := by decide
  have hdescent : baseEnd_1289706 < baseStart_1289706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289776 : List Nat := [2, 1, 1, 1, 2, 3, 1, 10]
def baseStart_1289776 : Nat := 118140960795 + 1289776 * 2 ^ 59
def prefixEnd_1289776 : Nat := 4983230072969 + 3 ^ 40 * 1289776 * 2
def baseEnd_1289776 : Nat := 98114818464214959876805

theorem tailTrace_1289776 : CollatzResearch.WordTrace tailWord_1289776 prefixEnd_1289776 98114818464214959876805 := by
  unfold tailWord_1289776
  simp only [CollatzResearch.WordTrace]
  refine ⟨23520997687684651524412591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31361330250246202032550121 23520997687684651524412591)
  ·
    refine ⟨35281496531526977286618887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23520997687684651524412591 35281496531526977286618887)
    ·
      refine ⟨52922244797290465929928331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35281496531526977286618887 52922244797290465929928331)
      ·
        refine ⟨79383367195935698894892497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52922244797290465929928331 79383367195935698894892497)
        ·
          refine ⟨59537525396951774171169373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79383367195935698894892497 59537525396951774171169373)
          ·
            refine ⟨22326572023856915314188515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59537525396951774171169373 22326572023856915314188515)
            ·
              refine ⟨33489858035785372971282773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22326572023856915314188515 33489858035785372971282773)
              ·
                refine ⟨98114818464214959876805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33489858035785372971282773 98114818464214959876805)
                ·
                  rfl

theorem cell21_1289776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 10].length) (baseStart_1289776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289776 prefixEnd_1289776 := by exact prefixLift 1289776
  have htrace : WordTrace (prefixWord ++ tailWord_1289776) baseStart_1289776 baseEnd_1289776 := by
    simpa [prefixWord, tailWord_1289776, baseEnd_1289776] using wordTrace_append hprefix tailTrace_1289776
  have hstable : (prefixWord ++ tailWord_1289776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289776).length < 2 ^ (prefixWord ++ tailWord_1289776).sum := by decide
  have hdescent : baseEnd_1289776 < baseStart_1289776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289793 : List Nat := [1, 2, 5, 1, 1, 1, 3, 7]
def baseStart_1289793 : Nat := 118140960795 + 1289793 * 2 ^ 59
def prefixEnd_1289793 : Nat := 4983230072969 + 3 ^ 40 * 1289793 * 2
def baseEnd_1289793 : Nat := 98116111674752209282349

theorem tailTrace_1289793 : CollatzResearch.WordTrace tailWord_1289793 prefixEnd_1289793 98116111674752209282349 := by
  unfold tailWord_1289793
  simp only [CollatzResearch.WordTrace]
  refine ⟨47042615416307714952194033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31361743610871809968129355 47042615416307714952194033)
  ·
    refine ⟨35281961562230786214145525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47042615416307714952194033 35281961562230786214145525)
    ·
      refine ⟨3307683896459136207576143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35281961562230786214145525 3307683896459136207576143)
      ·
        refine ⟨4961525844688704311364215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3307683896459136207576143 4961525844688704311364215)
        ·
          refine ⟨7442288767033056467046323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4961525844688704311364215 7442288767033056467046323)
          ·
            refine ⟨11163433150549584700569485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7442288767033056467046323 11163433150549584700569485)
            ·
              refine ⟨4186287431456094262713557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11163433150549584700569485 4186287431456094262713557)
              ·
                refine ⟨98116111674752209282349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4186287431456094262713557 98116111674752209282349)
                ·
                  rfl

theorem cell21_1289793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 7].length) (baseStart_1289793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289793 prefixEnd_1289793 := by exact prefixLift 1289793
  have htrace : WordTrace (prefixWord ++ tailWord_1289793) baseStart_1289793 baseEnd_1289793 := by
    simpa [prefixWord, tailWord_1289793, baseEnd_1289793] using wordTrace_append hprefix tailTrace_1289793
  have hstable : (prefixWord ++ tailWord_1289793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289793).length < 2 ^ (prefixWord ++ tailWord_1289793).sum := by decide
  have hdescent : baseEnd_1289793 < baseStart_1289793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289799 : List Nat := [1, 1, 4, 1, 6, 1, 1, 3, 3]
def baseStart_1289799 : Nat := 118140960795 + 1289799 * 2 ^ 59
def prefixEnd_1289799 : Nat := 4983230072969 + 3 ^ 40 * 1289799 * 2
def baseEnd_1289799 : Nat := 294349704306001950747035

theorem tailTrace_1289799 : CollatzResearch.WordTrace tailWord_1289799 prefixEnd_1289799 294349704306001950747035 := by
  unfold tailWord_1289799
  simp only [CollatzResearch.WordTrace]
  refine ⟨47042834254285977976912451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31361889502857318651274967 47042834254285977976912451)
  ·
    refine ⟨70564251381428966965368677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47042834254285977976912451 70564251381428966965368677)
    ·
      refine ⟨13230797134017931306006627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70564251381428966965368677 13230797134017931306006627)
      ·
        refine ⟨19846195701026896959009941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13230797134017931306006627 19846195701026896959009941)
        ·
          refine ⟨930290423485635794953591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19846195701026896959009941 930290423485635794953591)
          ·
            refine ⟨1395435635228453692430387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930290423485635794953591 1395435635228453692430387)
            ·
              refine ⟨2093153452842680538645581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1395435635228453692430387 2093153452842680538645581)
              ·
                refine ⟨784932544816005201992093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2093153452842680538645581 784932544816005201992093)
                ·
                  refine ⟨294349704306001950747035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 784932544816005201992093 294349704306001950747035)
                  ·
                    rfl

theorem cell21_1289799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 3].length) (baseStart_1289799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289799 prefixEnd_1289799 := by exact prefixLift 1289799
  have htrace : WordTrace (prefixWord ++ tailWord_1289799) baseStart_1289799 baseEnd_1289799 := by
    simpa [prefixWord, tailWord_1289799, baseEnd_1289799] using wordTrace_append hprefix tailTrace_1289799
  have hstable : (prefixWord ++ tailWord_1289799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289799).length < 2 ^ (prefixWord ++ tailWord_1289799).sum := by decide
  have hdescent : baseEnd_1289799 < baseStart_1289799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289886 : List Nat := [4, 3, 1, 1, 1, 2, 3, 6]
def baseStart_1289886 : Nat := 118140960795 + 1289886 * 2 ^ 59
def prefixEnd_1289886 : Nat := 4983230072969 + 3 ^ 40 * 1289886 * 2
def baseEnd_1289886 : Nat := 98123186297103044265619

theorem tailTrace_1289886 : CollatzResearch.WordTrace tailWord_1289886 prefixEnd_1289886 98123186297103044265619 := by
  unfold tailWord_1289886
  simp only [CollatzResearch.WordTrace]
  refine ⟨5880750925621348979416189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31364004936647194556886341 5880750925621348979416189)
  ·
    refine ⟨2205281597108005867281071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5880750925621348979416189 2205281597108005867281071)
    ·
      refine ⟨3307922395662008800921607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2205281597108005867281071 3307922395662008800921607)
      ·
        refine ⟨4961883593493013201382411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3307922395662008800921607 4961883593493013201382411)
        ·
          refine ⟨7442825390239519802073617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4961883593493013201382411 7442825390239519802073617)
          ·
            refine ⟨5582119042679639851555213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7442825390239519802073617 5582119042679639851555213)
            ·
              refine ⟨2093294641004864944333205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5582119042679639851555213 2093294641004864944333205)
              ·
                refine ⟨98123186297103044265619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2093294641004864944333205 98123186297103044265619)
                ·
                  rfl

theorem cell21_1289886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_1289886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289886 prefixEnd_1289886 := by exact prefixLift 1289886
  have htrace : WordTrace (prefixWord ++ tailWord_1289886) baseStart_1289886 baseEnd_1289886 := by
    simpa [prefixWord, tailWord_1289886, baseEnd_1289886] using wordTrace_append hprefix tailTrace_1289886
  have hstable : (prefixWord ++ tailWord_1289886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289886).length < 2 ^ (prefixWord ++ tailWord_1289886).sum := by decide
  have hdescent : baseEnd_1289886 < baseStart_1289886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289917 : List Nat := [1, 4, 1, 2, 1, 2, 4, 3, 3]
def baseStart_1289917 : Nat := 118140960795 + 1289917 * 2 ^ 59
def prefixEnd_1289917 : Nat := 4983230072969 + 3 ^ 40 * 1289917 * 2
def baseEnd_1289917 : Nat := 294376633513659967780127

theorem tailTrace_1289917 : CollatzResearch.WordTrace tailWord_1289917 prefixEnd_1289917 294376633513659967780127 := by
  unfold tailWord_1289917
  simp only [CollatzResearch.WordTrace]
  refine ⟨47047138067858484129708005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31364758711905656086472003 47047138067858484129708005)
  ·
    refine ⟨8821338387723465774320251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47047138067858484129708005 8821338387723465774320251)
    ·
      refine ⟨13232007581585198661480377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8821338387723465774320251 13232007581585198661480377)
      ·
        refine ⟨9924005686188898996110283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13232007581585198661480377 9924005686188898996110283)
        ·
          refine ⟨14886008529283348494165425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9924005686188898996110283 14886008529283348494165425)
          ·
            refine ⟨11164506396962511370624069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14886008529283348494165425 11164506396962511370624069)
            ·
              refine ⟨2093344949430470881992013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11164506396962511370624069 2093344949430470881992013)
              ·
                refine ⟨785004356036426580747005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2093344949430470881992013 785004356036426580747005)
                ·
                  refine ⟨294376633513659967780127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 785004356036426580747005 294376633513659967780127)
                  ·
                    rfl

theorem cell21_1289917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_1289917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289917 prefixEnd_1289917 := by exact prefixLift 1289917
  have htrace : WordTrace (prefixWord ++ tailWord_1289917) baseStart_1289917 baseEnd_1289917 := by
    simpa [prefixWord, tailWord_1289917, baseEnd_1289917] using wordTrace_append hprefix tailTrace_1289917
  have hstable : (prefixWord ++ tailWord_1289917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289917).length < 2 ^ (prefixWord ++ tailWord_1289917).sum := by decide
  have hdescent : baseEnd_1289917 < baseStart_1289917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289928 : List Nat := [2, 1, 3, 1, 2, 2, 10]
def baseStart_1289928 : Nat := 118140960795 + 1289928 * 2 ^ 59
def prefixEnd_1289928 : Nat := 4983230072969 + 3 ^ 40 * 1289928 * 2
def baseEnd_1289928 : Nat := 32708793762614043677419

theorem tailTrace_1289928 : CollatzResearch.WordTrace tailWord_1289928 prefixEnd_1289928 32708793762614043677419 := by
  unfold tailWord_1289928
  simp only [CollatzResearch.WordTrace]
  refine ⟨23523769635409316504179219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31365026180545755338905625 23523769635409316504179219)
  ·
    refine ⟨35285654453113974756268829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23523769635409316504179219 35285654453113974756268829)
    ·
      refine ⟨13232120419917740533600811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35285654453113974756268829 13232120419917740533600811)
      ·
        refine ⟨19848180629876610800401217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13232120419917740533600811 19848180629876610800401217)
        ·
          refine ⟨14886135472407458100300913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19848180629876610800401217 14886135472407458100300913)
          ·
            refine ⟨11164601604305593575225685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14886135472407458100300913 11164601604305593575225685)
            ·
              refine ⟨32708793762614043677419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11164601604305593575225685 32708793762614043677419)
              ·
                rfl

theorem cell21_1289928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 10].length) (baseStart_1289928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289928 prefixEnd_1289928 := by exact prefixLift 1289928
  have htrace : WordTrace (prefixWord ++ tailWord_1289928) baseStart_1289928 baseEnd_1289928 := by
    simpa [prefixWord, tailWord_1289928, baseEnd_1289928] using wordTrace_append hprefix tailTrace_1289928
  have hstable : (prefixWord ++ tailWord_1289928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289928).length < 2 ^ (prefixWord ++ tailWord_1289928).sum := by decide
  have hdescent : baseEnd_1289928 < baseStart_1289928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1289976 : List Nat := [2, 1, 2, 1, 1, 2, 2, 7, 3]
def baseStart_1289976 : Nat := 118140960795 + 1289976 * 2 ^ 59
def prefixEnd_1289976 : Nat := 4983230072969 + 3 ^ 40 * 1289976 * 2
def baseEnd_1289976 : Nat := 294390098117488976296673

theorem tailTrace_1289976 : CollatzResearch.WordTrace tailWord_1289976 prefixEnd_1289976 294390098117488976296673 := by
  unfold tailWord_1289976
  simp only [CollatzResearch.WordTrace]
  refine ⟨23524644987322368603052891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31366193316429824804070521 23524644987322368603052891)
  ·
    refine ⟨35286967480983552904579337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23524644987322368603052891 35286967480983552904579337)
    ·
      refine ⟨26465225610737664678434503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35286967480983552904579337 26465225610737664678434503)
      ·
        refine ⟨39697838416106497017651755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26465225610737664678434503 39697838416106497017651755)
        ·
          refine ⟨59546757624159745526477633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39697838416106497017651755 59546757624159745526477633)
          ·
            refine ⟨44660068218119809144858225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59546757624159745526477633 44660068218119809144858225)
            ·
              refine ⟨33495051163589856858643669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44660068218119809144858225 33495051163589856858643669)
              ·
                refine ⟨785040261646637270124461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 33495051163589856858643669 785040261646637270124461)
                ·
                  refine ⟨294390098117488976296673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 785040261646637270124461 294390098117488976296673)
                  ·
                    rfl

theorem cell21_1289976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 3].length) (baseStart_1289976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1289976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1289976 prefixEnd_1289976 := by exact prefixLift 1289976
  have htrace : WordTrace (prefixWord ++ tailWord_1289976) baseStart_1289976 baseEnd_1289976 := by
    simpa [prefixWord, tailWord_1289976, baseEnd_1289976] using wordTrace_append hprefix tailTrace_1289976
  have hstable : (prefixWord ++ tailWord_1289976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1289976).length < 2 ^ (prefixWord ++ tailWord_1289976).sum := by decide
  have hdescent : baseEnd_1289976 < baseStart_1289976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1289976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290007 : List Nat := [1, 1, 3, 4, 2, 2, 1, 3, 4]
def baseStart_1290007 : Nat := 118140960795 + 1290007 * 2 ^ 59
def prefixEnd_1290007 : Nat := 4983230072969 + 3 ^ 40 * 1290007 * 2
def baseEnd_1290007 : Nat := 294397172739839811279943

theorem tailTrace_1290007 : CollatzResearch.WordTrace tailWord_1290007 prefixEnd_1290007 294397172739839811279943 := by
  unfold tailWord_1290007
  simp only [CollatzResearch.WordTrace]
  refine ⟨47050420637532429500484275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31366947091688286333656183 47050420637532429500484275)
  ·
    refine ⟨70575630956298644250726413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47050420637532429500484275 70575630956298644250726413)
    ·
      refine ⟨26465861608611991594022405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70575630956298644250726413 26465861608611991594022405)
      ·
        refine ⟨4962349051614748423879201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26465861608611991594022405 4962349051614748423879201)
        ·
          refine ⟨3721761788711061317909401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4962349051614748423879201 3721761788711061317909401)
          ·
            refine ⟨2791321341533295988432051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3721761788711061317909401 2791321341533295988432051)
            ·
              refine ⟨4186982012299943982648077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2791321341533295988432051 4186982012299943982648077)
              ·
                refine ⟨1570118254612478993493029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4186982012299943982648077 1570118254612478993493029)
                ·
                  refine ⟨294397172739839811279943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1570118254612478993493029 294397172739839811279943)
                  ·
                    rfl

theorem cell21_1290007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 4].length) (baseStart_1290007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1290007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1290007 prefixEnd_1290007 := by exact prefixLift 1290007
  have htrace : WordTrace (prefixWord ++ tailWord_1290007) baseStart_1290007 baseEnd_1290007 := by
    simpa [prefixWord, tailWord_1290007, baseEnd_1290007] using wordTrace_append hprefix tailTrace_1290007
  have hstable : (prefixWord ++ tailWord_1290007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290007).length < 2 ^ (prefixWord ++ tailWord_1290007).sum := by decide
  have hdescent : baseEnd_1290007 < baseStart_1290007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290173 : List Nat := [1, 4, 1, 2, 3, 2, 2, 6]
def baseStart_1290173 : Nat := 118140960795 + 1290173 * 2 ^ 59
def prefixEnd_1290173 : Nat := 4983230072969 + 3 ^ 40 * 1290173 * 2
def baseEnd_1290173 : Nat := 98145018733820137170979

theorem tailTrace_1290173 : CollatzResearch.WordTrace tailWord_1290173 prefixEnd_1290173 98145018733820137170979 := by
  unfold tailWord_1290173
  simp only [CollatzResearch.WordTrace]
  refine ⟨47056475154931039851027173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31370983436620693234018115 47056475154931039851027173)
  ·
    refine ⟨8823089091549569972067595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47056475154931039851027173 8823089091549569972067595)
    ·
      refine ⟨13234633637324354958101393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8823089091549569972067595 13234633637324354958101393)
      ·
        refine ⟨9925975227993266218576045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13234633637324354958101393 9925975227993266218576045)
        ·
          refine ⟨3722240710497474831966017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9925975227993266218576045 3722240710497474831966017)
          ·
            refine ⟨2791680532873106123974513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3722240710497474831966017 2791680532873106123974513)
            ·
              refine ⟨2093760399654829592980885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2791680532873106123974513 2093760399654829592980885)
              ·
                refine ⟨98145018733820137170979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2093760399654829592980885 98145018733820137170979)
                ·
                  rfl

theorem cell21_1290173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 6].length) (baseStart_1290173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1290173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1290173 prefixEnd_1290173 := by exact prefixLift 1290173
  have htrace : WordTrace (prefixWord ++ tailWord_1290173) baseStart_1290173 baseEnd_1290173 := by
    simpa [prefixWord, tailWord_1290173, baseEnd_1290173] using wordTrace_append hprefix tailTrace_1290173
  have hstable : (prefixWord ++ tailWord_1290173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290173).length < 2 ^ (prefixWord ++ tailWord_1290173).sum := by decide
  have hdescent : baseEnd_1290173 < baseStart_1290173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290232 : List Nat := [2, 1, 2, 1, 1, 3, 5, 6]
def baseStart_1290232 : Nat := 118140960795 + 1290232 * 2 ^ 59
def prefixEnd_1290232 : Nat := 4983230072969 + 3 ^ 40 * 1290232 * 2
def baseEnd_1290232 : Nat := 98149506935096473343161

theorem tailTrace_1290232 : CollatzResearch.WordTrace tailWord_1290232 prefixEnd_1290232 98149506935096473343161 := by
  unfold tailWord_1290232
  simp only [CollatzResearch.WordTrace]
  refine ⟨23529313530858646463712475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31372418041144861951616633 23529313530858646463712475)
  ·
    refine ⟨35293970296287969695568713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23529313530858646463712475 35293970296287969695568713)
    ·
      refine ⟨26470477722215977271676535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35293970296287969695568713 26470477722215977271676535)
      ·
        refine ⟨39705716583323965907514803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26470477722215977271676535 39705716583323965907514803)
        ·
          refine ⟨59558574874985948861272205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39705716583323965907514803 59558574874985948861272205)
          ·
            refine ⟨22334465578119730822977077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59558574874985948861272205 22334465578119730822977077)
            ·
              refine ⟨2093856147948724764654101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22334465578119730822977077 2093856147948724764654101)
              ·
                refine ⟨98149506935096473343161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2093856147948724764654101 98149506935096473343161)
                ·
                  rfl

theorem cell21_1290232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 6].length) (baseStart_1290232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1290232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1290232 prefixEnd_1290232 := by exact prefixLift 1290232
  have htrace : WordTrace (prefixWord ++ tailWord_1290232) baseStart_1290232 baseEnd_1290232 := by
    simpa [prefixWord, tailWord_1290232, baseEnd_1290232] using wordTrace_append hprefix tailTrace_1290232
  have hstable : (prefixWord ++ tailWord_1290232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290232).length < 2 ^ (prefixWord ++ tailWord_1290232).sum := by decide
  have hdescent : baseEnd_1290232 < baseStart_1290232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290339 : List Nat := [1, 1, 1, 5, 1, 1, 5, 1, 5]
def baseStart_1290339 : Nat := 118140960795 + 1290339 * 2 ^ 59
def prefixEnd_1290339 : Nat := 4983230072969 + 3 ^ 40 * 1290339 * 2
def baseEnd_1290339 : Nat := 294472939663081011745931

theorem tailTrace_1290339 : CollatzResearch.WordTrace tailWord_1290339 prefixEnd_1290339 294472939663081011745931 := by
  unfold tailWord_1290339
  simp only [CollatzResearch.WordTrace]
  refine ⟨47062529672329650201570071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31375019781553100134380047 47062529672329650201570071)
  ·
    refine ⟨70593794508494475302355107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47062529672329650201570071 70593794508494475302355107)
    ·
      refine ⟨105890691762741712953532661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70593794508494475302355107 105890691762741712953532661)
      ·
        refine ⟨9927252352757035589393687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105890691762741712953532661 9927252352757035589393687)
        ·
          refine ⟨14890878529135553384090531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9927252352757035589393687 14890878529135553384090531)
          ·
            refine ⟨22336317793703330076135797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14890878529135553384090531 22336317793703330076135797)
            ·
              refine ⟨2094029793159687194637731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22336317793703330076135797 2094029793159687194637731)
              ·
                refine ⟨3141044689739530791956597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2094029793159687194637731 3141044689739530791956597)
                ·
                  refine ⟨294472939663081011745931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3141044689739530791956597 294472939663081011745931)
                  ·
                    rfl

theorem cell21_1290339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 5].length) (baseStart_1290339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1290339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1290339 prefixEnd_1290339 := by exact prefixLift 1290339
  have htrace : WordTrace (prefixWord ++ tailWord_1290339) baseStart_1290339 baseEnd_1290339 := by
    simpa [prefixWord, tailWord_1290339, baseEnd_1290339] using wordTrace_append hprefix tailTrace_1290339
  have hstable : (prefixWord ++ tailWord_1290339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290339).length < 2 ^ (prefixWord ++ tailWord_1290339).sum := by decide
  have hdescent : baseEnd_1290339 < baseStart_1290339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290401 : List Nat := [1, 2, 3, 3, 1, 4, 1, 6]
def baseStart_1290401 : Nat := 118140960795 + 1290401 * 2 ^ 59
def prefixEnd_1290401 : Nat := 4983230072969 + 3 ^ 40 * 1290401 * 2
def baseEnd_1290401 : Nat := 98162362969260893904157

theorem tailTrace_1290401 : CollatzResearch.WordTrace tailWord_1290401 prefixEnd_1290401 98162362969260893904157 := by
  unfold tailWord_1290401
  simp only [CollatzResearch.WordTrace]
  refine ⟨47064790998105034790327057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31376527332070023193551371 47064790998105034790327057)
  ·
    refine ⟨35298593248578776092745293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47064790998105034790327057 35298593248578776092745293)
    ·
      refine ⟨13236972468217041034779485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35298593248578776092745293 13236972468217041034779485)
      ·
        refine ⟨4963864675581390388042307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13236972468217041034779485 4963864675581390388042307)
        ·
          refine ⟨7445797013372085582063461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4963864675581390388042307 7445797013372085582063461)
          ·
            refine ⟨1396086940007266046636899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7445797013372085582063461 1396086940007266046636899)
            ·
              refine ⟨2094130410010899069955349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1396086940007266046636899 2094130410010899069955349)
              ·
                refine ⟨98162362969260893904157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2094130410010899069955349 98162362969260893904157)
                ·
                  rfl

theorem cell21_1290401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 6].length) (baseStart_1290401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1290401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1290401 prefixEnd_1290401 := by exact prefixLift 1290401
  have htrace : WordTrace (prefixWord ++ tailWord_1290401) baseStart_1290401 baseEnd_1290401 := by
    simpa [prefixWord, tailWord_1290401, baseEnd_1290401] using wordTrace_append hprefix tailTrace_1290401
  have hstable : (prefixWord ++ tailWord_1290401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290401).length < 2 ^ (prefixWord ++ tailWord_1290401).sum := by decide
  have hdescent : baseEnd_1290401 < baseStart_1290401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290429 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 6]
def baseStart_1290429 : Nat := 118140960795 + 1290429 * 2 ^ 59
def prefixEnd_1290429 : Nat := 4983230072969 + 3 ^ 40 * 1290429 * 2
def baseEnd_1290429 : Nat := 294493478889260855245747

theorem tailTrace_1290429 : CollatzResearch.WordTrace tailWord_1290429 prefixEnd_1290429 294493478889260855245747 := by
  unfold tailWord_1290429
  simp only [CollatzResearch.WordTrace]
  refine ⟨47065812242003595572346341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31377208161335730381564227 47065812242003595572346341)
  ·
    refine ⟨8824839795375674169814939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47065812242003595572346341 8824839795375674169814939)
    ·
      refine ⟨13237259693063511254722409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8824839795375674169814939 13237259693063511254722409)
      ·
        refine ⟨9927944769797633441041807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13237259693063511254722409 9927944769797633441041807)
        ·
          refine ⟨14891917154696450161562711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9927944769797633441041807 14891917154696450161562711)
          ·
            refine ⟨22337875732044675242344067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14891917154696450161562711 22337875732044675242344067)
            ·
              refine ⟨33506813598067012863516101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22337875732044675242344067 33506813598067012863516101)
              ·
                refine ⟨6282527549637564911909269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33506813598067012863516101 6282527549637564911909269)
                ·
                  refine ⟨294493478889260855245747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6282527549637564911909269 294493478889260855245747)
                  ·
                    rfl

theorem cell21_1290429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_1290429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1290429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1290429 prefixEnd_1290429 := by exact prefixLift 1290429
  have htrace : WordTrace (prefixWord ++ tailWord_1290429) baseStart_1290429 baseEnd_1290429 := by
    simpa [prefixWord, tailWord_1290429, baseEnd_1290429] using wordTrace_append hprefix tailTrace_1290429
  have hstable : (prefixWord ++ tailWord_1290429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290429).length < 2 ^ (prefixWord ++ tailWord_1290429).sum := by decide
  have hdescent : baseEnd_1290429 < baseStart_1290429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290432 : List Nat := [2, 1, 1, 2, 5, 1, 1, 5, 3]
def baseStart_1290432 : Nat := 118140960795 + 1290432 * 2 ^ 59
def prefixEnd_1290432 : Nat := 4983230072969 + 3 ^ 40 * 1290432 * 2
def baseEnd_1290432 : Nat := 294494163530133516695741

theorem tailTrace_1290432 : CollatzResearch.WordTrace tailWord_1290432 prefixEnd_1290432 294494163530133516695741 := by
  unfold tailWord_1290432
  simp only [CollatzResearch.WordTrace]
  refine ⟨23532960830496363542352775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31377281107328484723137033 23532960830496363542352775)
  ·
    refine ⟨35299441245744545313529163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23532960830496363542352775 35299441245744545313529163)
    ·
      refine ⟨52949161868616817970293745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35299441245744545313529163 52949161868616817970293745)
      ·
        refine ⟨39711871401462613477720309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52949161868616817970293745 39711871401462613477720309)
        ·
          refine ⟨3722987943887120013536279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39711871401462613477720309 3722987943887120013536279)
          ·
            refine ⟨5584481915830680020304419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3722987943887120013536279 5584481915830680020304419)
            ·
              refine ⟨8376722873746020030456629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5584481915830680020304419 8376722873746020030456629)
              ·
                refine ⟨785317769413689377855309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8376722873746020030456629 785317769413689377855309)
                ·
                  refine ⟨294494163530133516695741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 785317769413689377855309 294494163530133516695741)
                  ·
                    rfl

theorem cell21_1290432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 3].length) (baseStart_1290432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1290432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1290432 prefixEnd_1290432 := by exact prefixLift 1290432
  have htrace : WordTrace (prefixWord ++ tailWord_1290432) baseStart_1290432 baseEnd_1290432 := by
    simpa [prefixWord, tailWord_1290432, baseEnd_1290432] using wordTrace_append hprefix tailTrace_1290432
  have hstable : (prefixWord ++ tailWord_1290432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290432).length < 2 ^ (prefixWord ++ tailWord_1290432).sum := by decide
  have hdescent : baseEnd_1290432 < baseStart_1290432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290443 : List Nat := [1, 1, 1, 1, 3, 2, 12]
def baseStart_1290443 : Nat := 118140960795 + 1290443 * 2 ^ 59
def prefixEnd_1290443 : Nat := 4983230072969 + 3 ^ 40 * 1290443 * 2
def baseEnd_1290443 : Nat := 32721852653333326890265

theorem tailTrace_1290443 : CollatzResearch.WordTrace tailWord_1290443 prefixEnd_1290443 32721852653333326890265 := by
  unfold tailWord_1290443
  simp only [CollatzResearch.WordTrace]
  refine ⟨47066322863952875963355983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31377548575968583975570655 47066322863952875963355983)
  ·
    refine ⟨70599484295929313945033975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47066322863952875963355983 70599484295929313945033975)
    ·
      refine ⟨105899226443893970917550963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70599484295929313945033975 105899226443893970917550963)
      ·
        refine ⟨158848839665840956376326445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105899226443893970917550963 158848839665840956376326445)
        ·
          refine ⟨59568314874690358641122417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158848839665840956376326445 59568314874690358641122417)
          ·
            refine ⟨44676236156017768980841813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59568314874690358641122417 44676236156017768980841813)
            ·
              refine ⟨32721852653333326890265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 44676236156017768980841813 32721852653333326890265)
              ·
                rfl

theorem cell21_1290443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 12].length) (baseStart_1290443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1290443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1290443 prefixEnd_1290443 := by exact prefixLift 1290443
  have htrace : WordTrace (prefixWord ++ tailWord_1290443) baseStart_1290443 baseEnd_1290443 := by
    simpa [prefixWord, tailWord_1290443, baseEnd_1290443] using wordTrace_append hprefix tailTrace_1290443
  have hstable : (prefixWord ++ tailWord_1290443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290443).length < 2 ^ (prefixWord ++ tailWord_1290443).sum := by decide
  have hdescent : baseEnd_1290443 < baseStart_1290443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290446 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 6]
def baseStart_1290446 : Nat := 118140960795 + 1290446 * 2 ^ 59
def prefixEnd_1290446 : Nat := 4983230072969 + 3 ^ 40 * 1290446 * 2
def baseEnd_1290446 : Nat := 294497358520872603462379

theorem tailTrace_1290446 : CollatzResearch.WordTrace tailWord_1290446 prefixEnd_1290446 294497358520872603462379 := by
  unfold tailWord_1290446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5883304035367750934464399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31377621521961338317143461 5883304035367750934464399)
  ·
    refine ⟨8824956053051626401696599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5883304035367750934464399 8824956053051626401696599)
    ·
      refine ⟨13237434079577439602544899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8824956053051626401696599 13237434079577439602544899)
      ·
        refine ⟨19856151119366159403817349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13237434079577439602544899 19856151119366159403817349)
        ·
          refine ⟨3723028334881154888215753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19856151119366159403817349 3723028334881154888215753)
          ·
            refine ⟨2792271251160866166161815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3723028334881154888215753 2792271251160866166161815)
            ·
              refine ⟨4188406876741299249242723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2792271251160866166161815 4188406876741299249242723)
              ·
                refine ⟨6282610315111948873864085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4188406876741299249242723 6282610315111948873864085)
                ·
                  refine ⟨294497358520872603462379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6282610315111948873864085 294497358520872603462379)
                  ·
                    rfl

theorem cell21_1290446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_1290446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1290446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1290446 prefixEnd_1290446 := by exact prefixLift 1290446
  have htrace : WordTrace (prefixWord ++ tailWord_1290446) baseStart_1290446 baseEnd_1290446 := by
    simpa [prefixWord, tailWord_1290446, baseEnd_1290446] using wordTrace_append hprefix tailTrace_1290446
  have hstable : (prefixWord ++ tailWord_1290446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290446).length < 2 ^ (prefixWord ++ tailWord_1290446).sum := by decide
  have hdescent : baseEnd_1290446 < baseStart_1290446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290477 : List Nat := [1, 5, 1, 2, 3, 1, 1, 7]
def baseStart_1290477 : Nat := 118140960795 + 1290477 * 2 ^ 59
def prefixEnd_1290477 : Nat := 4983230072969 + 3 ^ 40 * 1290477 * 2
def baseEnd_1290477 : Nat := 98168144381074479481883

theorem tailTrace_1290477 : CollatzResearch.WordTrace tailWord_1290477 prefixEnd_1290477 98168144381074479481883 := by
  unfold tailWord_1290477
  simp only [CollatzResearch.WordTrace]
  refine ⟨47067562945829699770093685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31378375297219799846729123 47067562945829699770093685)
  ·
    refine ⟨4412584026171534353446283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47067562945829699770093685 4412584026171534353446283)
    ·
      refine ⟨6618876039257301530169425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4412584026171534353446283 6618876039257301530169425)
      ·
        refine ⟨4964157029442976147627069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6618876039257301530169425 4964157029442976147627069)
        ·
          refine ⟨1861558886041116055360151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4964157029442976147627069 1861558886041116055360151)
          ·
            refine ⟨2792338329061674083040227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1861558886041116055360151 2792338329061674083040227)
            ·
              refine ⟨4188507493592511124560341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2792338329061674083040227 4188507493592511124560341)
              ·
                refine ⟨98168144381074479481883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4188507493592511124560341 98168144381074479481883)
                ·
                  rfl

theorem cell21_1290477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 7].length) (baseStart_1290477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1290477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1290477 prefixEnd_1290477 := by exact prefixLift 1290477
  have htrace : WordTrace (prefixWord ++ tailWord_1290477) baseStart_1290477 baseEnd_1290477 := by
    simpa [prefixWord, tailWord_1290477, baseEnd_1290477] using wordTrace_append hprefix tailTrace_1290477
  have hstable : (prefixWord ++ tailWord_1290477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290477).length < 2 ^ (prefixWord ++ tailWord_1290477).sum := by decide
  have hdescent : baseEnd_1290477 < baseStart_1290477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290505 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 6]
def baseStart_1290505 : Nat := 118140960795 + 1290505 * 2 ^ 59
def prefixEnd_1290505 : Nat := 4983230072969 + 3 ^ 40 * 1290505 * 2
def baseEnd_1290505 : Nat := 294510823124701611978925

theorem tailTrace_1290505 : CollatzResearch.WordTrace tailWord_1290505 prefixEnd_1290505 294510823124701611978925 := by
  unfold tailWord_1290505
  simp only [CollatzResearch.WordTrace]
  refine ⟨47068584189728260552112969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31379056126485507034741979 47068584189728260552112969)
  ·
    refine ⟨35301438142296195414084727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47068584189728260552112969 35301438142296195414084727)
    ·
      refine ⟨52952157213444293121127091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35301438142296195414084727 52952157213444293121127091)
      ·
        refine ⟨79428235820166439681690637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52952157213444293121127091 79428235820166439681690637)
        ·
          refine ⟨29785588432562414880633989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79428235820166439681690637 29785588432562414880633989)
          ·
            refine ⟨5584797831105452790118873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29785588432562414880633989 5584797831105452790118873)
            ·
              refine ⟨4188598373329089592589155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5584797831105452790118873 4188598373329089592589155)
              ·
                refine ⟨6282897559993634388883733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4188598373329089592589155 6282897559993634388883733)
                ·
                  refine ⟨294510823124701611978925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6282897559993634388883733 294510823124701611978925)
                  ·
                    rfl

theorem cell21_1290505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_1290505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1290505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1290505 prefixEnd_1290505 := by exact prefixLift 1290505
  have htrace : WordTrace (prefixWord ++ tailWord_1290505) baseStart_1290505 baseEnd_1290505 := by
    simpa [prefixWord, tailWord_1290505, baseEnd_1290505] using wordTrace_append hprefix tailTrace_1290505
  have hstable : (prefixWord ++ tailWord_1290505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290505).length < 2 ^ (prefixWord ++ tailWord_1290505).sum := by decide
  have hdescent : baseEnd_1290505 < baseStart_1290505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290660 : List Nat := [2, 3, 1, 2, 1, 1, 5, 3, 3]
def baseStart_1290660 : Nat := 118140960795 + 1290660 * 2 ^ 59
def prefixEnd_1290660 : Nat := 4983230072969 + 3 ^ 40 * 1290660 * 2
def baseEnd_1290660 : Nat := 294546196236455786895275

theorem tailTrace_1290660 : CollatzResearch.WordTrace tailWord_1290660 prefixEnd_1290660 294546196236455786895275 := by
  unfold tailWord_1290660
  simp only [CollatzResearch.WordTrace]
  refine ⟨23537118752083361012002717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31382825002777814682670289 23537118752083361012002717)
  ·
    refine ⟨8826419532031260379501019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23537118752083361012002717 8826419532031260379501019)
    ·
      refine ⟨13239629298046890569251529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8826419532031260379501019 13239629298046890569251529)
      ·
        refine ⟨9929721973535167926938647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13239629298046890569251529 9929721973535167926938647)
        ·
          refine ⟨14894582960302751890407971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9929721973535167926938647 14894582960302751890407971)
          ·
            refine ⟨22341874440454127835611957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14894582960302751890407971 22341874440454127835611957)
            ·
              refine ⟨2094550728792574484588621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22341874440454127835611957 2094550728792574484588621)
              ·
                refine ⟨785456523297215431720733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2094550728792574484588621 785456523297215431720733)
                ·
                  refine ⟨294546196236455786895275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 785456523297215431720733 294546196236455786895275)
                  ·
                    rfl

theorem cell21_1290660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_1290660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1290660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1290660 prefixEnd_1290660 := by exact prefixLift 1290660
  have htrace : WordTrace (prefixWord ++ tailWord_1290660) baseStart_1290660 baseEnd_1290660 := by
    simpa [prefixWord, tailWord_1290660, baseEnd_1290660] using wordTrace_append hprefix tailTrace_1290660
  have hstable : (prefixWord ++ tailWord_1290660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290660).length < 2 ^ (prefixWord ++ tailWord_1290660).sum := by decide
  have hdescent : baseEnd_1290660 < baseStart_1290660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290677 : List Nat := [1, 3, 3, 2, 4, 1, 1, 1, 5]
def baseStart_1290677 : Nat := 118140960795 + 1290677 * 2 ^ 59
def prefixEnd_1290677 : Nat := 4983230072969 + 3 ^ 40 * 1290677 * 2
def baseEnd_1290677 : Nat := 294550075868067535111907

theorem tailTrace_1290677 : CollatzResearch.WordTrace tailWord_1290677 prefixEnd_1290677 294550075868067535111907 := by
  unfold tailWord_1290677
  simp only [CollatzResearch.WordTrace]
  refine ⟨47074857545105133927374285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31383238363403422618249523 47074857545105133927374285)
  ·
    refine ⟨17653071579414425222765357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47074857545105133927374285 17653071579414425222765357)
    ·
      refine ⟨6619901842280409458537009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17653071579414425222765357 6619901842280409458537009)
      ·
        refine ⟨4964926381710307093902757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6619901842280409458537009 4964926381710307093902757)
        ·
          refine ⟨930923696570682580106767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4964926381710307093902757 930923696570682580106767)
          ·
            refine ⟨1396385544856023870160151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 930923696570682580106767 1396385544856023870160151)
            ·
              refine ⟨2094578317284035805240227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1396385544856023870160151 2094578317284035805240227)
              ·
                refine ⟨3141867475926053707860341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2094578317284035805240227 3141867475926053707860341)
                ·
                  refine ⟨294550075868067535111907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3141867475926053707860341 294550075868067535111907)
                  ·
                    rfl

theorem cell21_1290677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 5].length) (baseStart_1290677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1290677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1290677 prefixEnd_1290677 := by exact prefixLift 1290677
  have htrace : WordTrace (prefixWord ++ tailWord_1290677) baseStart_1290677 baseEnd_1290677 := by
    simpa [prefixWord, tailWord_1290677, baseEnd_1290677] using wordTrace_append hprefix tailTrace_1290677
  have hstable : (prefixWord ++ tailWord_1290677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290677).length < 2 ^ (prefixWord ++ tailWord_1290677).sum := by decide
  have hdescent : baseEnd_1290677 < baseStart_1290677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290702 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_1290702 : Nat := 118140960795 + 1290702 * 2 ^ 59
def prefixEnd_1290702 : Nat := 4983230072969 + 3 ^ 40 * 1290702 * 2
def baseEnd_1290702 : Nat := 294555781208673047195189

theorem tailTrace_1290702 : CollatzResearch.WordTrace tailWord_1290702 prefixEnd_1290702 294555781208673047195189 := by
  unfold tailWord_1290702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5884471171251820399629295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31383846246676375464689573 5884471171251820399629295)
  ·
    refine ⟨8826706756877730599443943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5884471171251820399629295 8826706756877730599443943)
    ·
      refine ⟨13240060135316595899165915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8826706756877730599443943 13240060135316595899165915)
      ·
        refine ⟨19860090202974893848748873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13240060135316595899165915 19860090202974893848748873)
        ·
          refine ⟨14895067652231170386561655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19860090202974893848748873 14895067652231170386561655)
          ·
            refine ⟨22342601478346755579842483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14895067652231170386561655 22342601478346755579842483)
            ·
              refine ⟨33513902217520133369763725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22342601478346755579842483 33513902217520133369763725)
              ·
                refine ⟨12567713331570050013661397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33513902217520133369763725 12567713331570050013661397)
                ·
                  refine ⟨294555781208673047195189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12567713331570050013661397 294555781208673047195189)
                  ·
                    rfl

theorem cell21_1290702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_1290702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1290702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1290702 prefixEnd_1290702 := by exact prefixLift 1290702
  have htrace : WordTrace (prefixWord ++ tailWord_1290702) baseStart_1290702 baseEnd_1290702 := by
    simpa [prefixWord, tailWord_1290702, baseEnd_1290702] using wordTrace_append hprefix tailTrace_1290702
  have hstable : (prefixWord ++ tailWord_1290702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290702).length < 2 ^ (prefixWord ++ tailWord_1290702).sum := by decide
  have hdescent : baseEnd_1290702 < baseStart_1290702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290722 : List Nat := [3, 3, 3, 2, 2, 8]
def baseStart_1290722 : Nat := 118140960795 + 1290722 * 2 ^ 59
def prefixEnd_1290722 : Nat := 4983230072969 + 3 ^ 40 * 1290722 * 2
def baseEnd_1290722 : Nat := 10909642425228053957845

theorem tailTrace_1290722 : CollatzResearch.WordTrace tailWord_1290722 prefixEnd_1290722 10909642425228053957845 := by
  unfold tailWord_1290722
  simp only [CollatzResearch.WordTrace]
  refine ⟨11769124707485526653190605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31384332553294737741841613 11769124707485526653190605)
  ·
    refine ⟨4413421765307072494946477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11769124707485526653190605 4413421765307072494946477)
    ·
      refine ⟨1655033161990152185604929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4413421765307072494946477 1655033161990152185604929)
      ·
        refine ⟨1241274871492614139203697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1655033161990152185604929 1241274871492614139203697)
        ·
          refine ⟨930956153619460604402773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1241274871492614139203697 930956153619460604402773)
          ·
            refine ⟨10909642425228053957845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 930956153619460604402773 10909642425228053957845)
            ·
              rfl

theorem cell21_1290722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 8].length) (baseStart_1290722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1290722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1290722 prefixEnd_1290722 := by exact prefixLift 1290722
  have htrace : WordTrace (prefixWord ++ tailWord_1290722) baseStart_1290722 baseEnd_1290722 := by
    simpa [prefixWord, tailWord_1290722, baseEnd_1290722] using wordTrace_append hprefix tailTrace_1290722
  have hstable : (prefixWord ++ tailWord_1290722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290722).length < 2 ^ (prefixWord ++ tailWord_1290722).sum := by decide
  have hdescent : baseEnd_1290722 < baseStart_1290722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290784 : List Nat := [2, 1, 1, 6, 3, 1, 1, 2, 4]
def baseStart_1290784 : Nat := 118140960795 + 1290784 * 2 ^ 59
def prefixEnd_1290784 : Nat := 4983230072969 + 3 ^ 40 * 1290784 * 2
def baseEnd_1290784 : Nat := 294574494725859126828355

theorem tailTrace_1290784 : CollatzResearch.WordTrace tailWord_1290784 prefixEnd_1290784 294574494725859126828355 := by
  unfold tailWord_1290784
  simp only [CollatzResearch.WordTrace]
  refine ⟨23539380077858745600759703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31385840103811660801012937 23539380077858745600759703)
  ·
    refine ⟨35309070116788118401139555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23539380077858745600759703 35309070116788118401139555)
    ·
      refine ⟨52963605175182177601709333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35309070116788118401139555 52963605175182177601709333)
      ·
        refine ⟨2482668992586664575080125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52963605175182177601709333 2482668992586664575080125)
        ·
          refine ⟨931000872219999215655047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2482668992586664575080125 931000872219999215655047)
          ·
            refine ⟨1396501308329998823482571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 931000872219999215655047 1396501308329998823482571)
            ·
              refine ⟨2094751962494998235223857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1396501308329998823482571 2094751962494998235223857)
              ·
                refine ⟨1571063971871248676417893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2094751962494998235223857 1571063971871248676417893)
                ·
                  refine ⟨294574494725859126828355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1571063971871248676417893 294574494725859126828355)
                  ·
                    rfl

theorem cell21_1290784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 4].length) (baseStart_1290784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1290784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1290784 prefixEnd_1290784 := by exact prefixLift 1290784
  have htrace : WordTrace (prefixWord ++ tailWord_1290784) baseStart_1290784 baseEnd_1290784 := by
    simpa [prefixWord, tailWord_1290784, baseEnd_1290784] using wordTrace_append hprefix tailTrace_1290784
  have hstable : (prefixWord ++ tailWord_1290784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290784).length < 2 ^ (prefixWord ++ tailWord_1290784).sum := by decide
  have hdescent : baseEnd_1290784 < baseStart_1290784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290829 : List Nat := [1, 6, 1, 1, 2, 1, 3, 3, 3]
def baseStart_1290829 : Nat := 118140960795 + 1290829 * 2 ^ 59
def prefixEnd_1290829 : Nat := 4983230072969 + 3 ^ 40 * 1290829 * 2
def baseEnd_1290829 : Nat := 294584764338949048578263

theorem tailTrace_1290829 : CollatzResearch.WordTrace tailWord_1290829 prefixEnd_1290829 294584764338949048578263 := by
  unfold tailWord_1290829
  simp only [CollatzResearch.WordTrace]
  refine ⟨47080401440554463886907541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31386934293702975924605027 47080401440554463886907541)
  ·
    refine ⟨2206893817525990494698791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47080401440554463886907541 2206893817525990494698791)
    ·
      refine ⟨3310340726288985742048187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2206893817525990494698791 3310340726288985742048187)
      ·
        refine ⟨4965511089433478613072281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3310340726288985742048187 4965511089433478613072281)
        ·
          refine ⟨3724133317075108959804211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4965511089433478613072281 3724133317075108959804211)
          ·
            refine ⟨5586199975612663439706317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3724133317075108959804211 5586199975612663439706317)
            ·
              refine ⟨2094824990854748789889869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5586199975612663439706317 2094824990854748789889869)
              ·
                refine ⟨785559371570530796208701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2094824990854748789889869 785559371570530796208701)
                ·
                  refine ⟨294584764338949048578263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 785559371570530796208701 294584764338949048578263)
                  ·
                    rfl

theorem cell21_1290829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_1290829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1290829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1290829 prefixEnd_1290829 := by exact prefixLift 1290829
  have htrace : WordTrace (prefixWord ++ tailWord_1290829) baseStart_1290829 baseEnd_1290829 := by
    simpa [prefixWord, tailWord_1290829, baseEnd_1290829] using wordTrace_append hprefix tailTrace_1290829
  have hstable : (prefixWord ++ tailWord_1290829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290829).length < 2 ^ (prefixWord ++ tailWord_1290829).sum := by decide
  have hdescent : baseEnd_1290829 < baseStart_1290829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290933 : List Nat := [1, 3, 3, 3, 1, 2, 3, 5]
def baseStart_1290933 : Nat := 118140960795 + 1290933 * 2 ^ 59
def prefixEnd_1290933 : Nat := 4983230072969 + 3 ^ 40 * 1290933 * 2
def baseEnd_1290933 : Nat := 98202832851955992948239

theorem tailTrace_1290933 : CollatzResearch.WordTrace tailWord_1290933 prefixEnd_1290933 98202832851955992948239 := by
  unfold tailWord_1290933
  simp only [CollatzResearch.WordTrace]
  refine ⟨47084194632177689648693453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31389463088118459765795635 47084194632177689648693453)
  ·
    refine ⟨17656572987066633618260045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47084194632177689648693453 17656572987066633618260045)
    ·
      refine ⟨6621214870149987606847517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17656572987066633618260045 6621214870149987606847517)
      ·
        refine ⟨2482955576306245352567819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6621214870149987606847517 2482955576306245352567819)
        ·
          refine ⟨3724433364459368028851729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2482955576306245352567819 3724433364459368028851729)
          ·
            refine ⟨2793325023344526021638797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3724433364459368028851729 2793325023344526021638797)
            ·
              refine ⟨1047496883754197258114549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2793325023344526021638797 1047496883754197258114549)
              ·
                refine ⟨98202832851955992948239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1047496883754197258114549 98202832851955992948239)
                ·
                  rfl

theorem cell21_1290933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 5].length) (baseStart_1290933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1290933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1290933 prefixEnd_1290933 := by exact prefixLift 1290933
  have htrace : WordTrace (prefixWord ++ tailWord_1290933) baseStart_1290933 baseEnd_1290933 := by
    simpa [prefixWord, tailWord_1290933, baseEnd_1290933] using wordTrace_append hprefix tailTrace_1290933
  have hstable : (prefixWord ++ tailWord_1290933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290933).length < 2 ^ (prefixWord ++ tailWord_1290933).sum := by decide
  have hdescent : baseEnd_1290933 < baseStart_1290933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290950 : List Nat := [6, 1, 2, 1, 2, 1, 8]
def baseStart_1290950 : Nat := 118140960795 + 1290950 * 2 ^ 59
def prefixEnd_1290950 : Nat := 4983230072969 + 3 ^ 40 * 1290950 * 2
def baseEnd_1290950 : Nat := 32734708687497747451261

theorem tailTrace_1290950 : CollatzResearch.WordTrace tailWord_1290950 prefixEnd_1290950 32734708687497747451261 := by
  unfold tailWord_1290950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1471400458534878173501947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31389876448744067701374869 1471400458534878173501947)
  ·
    refine ⟨2207100687802317260252921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1471400458534878173501947 2207100687802317260252921)
    ·
      refine ⟨1655325515851737945189691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2207100687802317260252921 1655325515851737945189691)
      ·
        refine ⟨2482988273777606917784537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1655325515851737945189691 2482988273777606917784537)
        ·
          refine ⟨1862241205333205188338403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2482988273777606917784537 1862241205333205188338403)
          ·
            refine ⟨2793361807999807782507605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1862241205333205188338403 2793361807999807782507605)
            ·
              refine ⟨32734708687497747451261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2793361807999807782507605 32734708687497747451261)
              ·
                rfl

theorem cell21_1290950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 8].length) (baseStart_1290950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1290950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1290950 prefixEnd_1290950 := by exact prefixLift 1290950
  have htrace : WordTrace (prefixWord ++ tailWord_1290950) baseStart_1290950 baseEnd_1290950 := by
    simpa [prefixWord, tailWord_1290950, baseEnd_1290950] using wordTrace_append hprefix tailTrace_1290950
  have hstable : (prefixWord ++ tailWord_1290950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290950).length < 2 ^ (prefixWord ++ tailWord_1290950).sum := by decide
  have hdescent : baseEnd_1290950 < baseStart_1290950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1290964 : List Nat := [2, 4, 1, 3, 2, 1, 2, 1, 5]
def baseStart_1290964 : Nat := 118140960795 + 1290964 * 2 ^ 59
def prefixEnd_1290964 : Nat := 4983230072969 + 3 ^ 40 * 1290964 * 2
def baseEnd_1290964 : Nat := 294615573178218813827987

theorem tailTrace_1290964 : CollatzResearch.WordTrace tailWord_1290964 prefixEnd_1290964 294615573178218813827987 := by
  unfold tailWord_1290964
  simp only [CollatzResearch.WordTrace]
  refine ⟨23542662647532690971535973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31390216863376921295381297 23542662647532690971535973)
  ·
    refine ⟨4414249246412379557162995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23542662647532690971535973 4414249246412379557162995)
    ·
      refine ⟨6621373869618569335744493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4414249246412379557162995 6621373869618569335744493)
      ·
        refine ⟨2483015201106963500904185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6621373869618569335744493 2483015201106963500904185)
        ·
          refine ⟨1862261400830222625678139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2483015201106963500904185 1862261400830222625678139)
          ·
            refine ⟨2793392101245333938517209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1862261400830222625678139 2793392101245333938517209)
            ·
              refine ⟨2095044075934000453887907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2793392101245333938517209 2095044075934000453887907)
              ·
                refine ⟨3142566113901000680831861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2095044075934000453887907 3142566113901000680831861)
                ·
                  refine ⟨294615573178218813827987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3142566113901000680831861 294615573178218813827987)
                  ·
                    rfl

theorem cell21_1290964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_1290964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1290964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1290964 prefixEnd_1290964 := by exact prefixLift 1290964
  have htrace : WordTrace (prefixWord ++ tailWord_1290964) baseStart_1290964 baseEnd_1290964 := by
    simpa [prefixWord, tailWord_1290964, baseEnd_1290964] using wordTrace_append hprefix tailTrace_1290964
  have hstable : (prefixWord ++ tailWord_1290964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1290964).length < 2 ^ (prefixWord ++ tailWord_1290964).sum := by decide
  have hdescent : baseEnd_1290964 < baseStart_1290964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1290964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291172 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 8]
def baseStart_1291172 : Nat := 118140960795 + 1291172 * 2 ^ 59
def prefixEnd_1291172 : Nat := 4983230072969 + 3 ^ 40 * 1291172 * 2
def baseEnd_1291172 : Nat := 294663041612056674360895

theorem tailTrace_1291172 : CollatzResearch.WordTrace tailWord_1291172 prefixEnd_1291172 294663041612056674360895 := by
  unfold tailWord_1291172
  simp only [CollatzResearch.WordTrace]
  refine ⟨23546455839155916733321885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31395274452207888977762513 23546455839155916733321885)
  ·
    refine ⟨8829920939683468774995707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23546455839155916733321885 8829920939683468774995707)
    ·
      refine ⟨13244881409525203162493561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8829920939683468774995707 13244881409525203162493561)
      ·
        refine ⟨9933661057143902371870171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13244881409525203162493561 9933661057143902371870171)
        ·
          refine ⟨14900491585715853557805257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9933661057143902371870171 14900491585715853557805257)
          ·
            refine ⟨11175368689286890168353943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14900491585715853557805257 11175368689286890168353943)
            ·
              refine ⟨16763053033930335252530915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11175368689286890168353943 16763053033930335252530915)
              ·
                refine ⟨25144579550895502878796373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16763053033930335252530915 25144579550895502878796373)
                ·
                  refine ⟨294663041612056674360895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25144579550895502878796373 294663041612056674360895)
                  ·
                    rfl

theorem cell21_1291172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_1291172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1291172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1291172 prefixEnd_1291172 := by exact prefixLift 1291172
  have htrace : WordTrace (prefixWord ++ tailWord_1291172) baseStart_1291172 baseEnd_1291172 := by
    simpa [prefixWord, tailWord_1291172, baseEnd_1291172] using wordTrace_append hprefix tailTrace_1291172
  have hstable : (prefixWord ++ tailWord_1291172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291172).length < 2 ^ (prefixWord ++ tailWord_1291172).sum := by decide
  have hdescent : baseEnd_1291172 < baseStart_1291172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291189 : List Nat := [1, 3, 3, 2, 1, 1, 2, 4, 4]
def baseStart_1291189 : Nat := 118140960795 + 1291189 * 2 ^ 59
def prefixEnd_1291189 : Nat := 4983230072969 + 3 ^ 40 * 1291189 * 2
def baseEnd_1291189 : Nat := 294666921243668422577527

theorem tailTrace_1291189 : CollatzResearch.WordTrace tailWord_1291189 prefixEnd_1291189 294666921243668422577527 := by
  unfold tailWord_1291189
  simp only [CollatzResearch.WordTrace]
  refine ⟨47093531719250245370012621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31395687812833496913341747 47093531719250245370012621)
  ·
    refine ⟨17660074394718842013754733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47093531719250245370012621 17660074394718842013754733)
    ·
      refine ⟨6622527898019565755158025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17660074394718842013754733 6622527898019565755158025)
      ·
        refine ⟨4966895923514674316368519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6622527898019565755158025 4966895923514674316368519)
        ·
          refine ⟨7450343885272011474552779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4966895923514674316368519 7450343885272011474552779)
          ·
            refine ⟨11175515827908017211829169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7450343885272011474552779 11175515827908017211829169)
            ·
              refine ⟨8381636870931012908871877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11175515827908017211829169 8381636870931012908871877)
              ·
                refine ⟨1571556913299564920413477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8381636870931012908871877 1571556913299564920413477)
                ·
                  refine ⟨294666921243668422577527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1571556913299564920413477 294666921243668422577527)
                  ·
                    rfl

theorem cell21_1291189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_1291189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1291189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1291189 prefixEnd_1291189 := by exact prefixLift 1291189
  have htrace : WordTrace (prefixWord ++ tailWord_1291189) baseStart_1291189 baseEnd_1291189 := by
    simpa [prefixWord, tailWord_1291189, baseEnd_1291189] using wordTrace_append hprefix tailTrace_1291189
  have hstable : (prefixWord ++ tailWord_1291189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291189).length < 2 ^ (prefixWord ++ tailWord_1291189).sum := by decide
  have hdescent : baseEnd_1291189 < baseStart_1291189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291192 : List Nat := [2, 1, 2, 1, 2, 5, 3, 2, 3]
def baseStart_1291192 : Nat := 118140960795 + 1291192 * 2 ^ 59
def prefixEnd_1291192 : Nat := 4983230072969 + 3 ^ 40 * 1291192 * 2
def baseEnd_1291192 : Nat := 294667605884541084027521

theorem tailTrace_1291192 : CollatzResearch.WordTrace tailWord_1291192 prefixEnd_1291192 294667605884541084027521 := by
  unfold tailWord_1291192
  simp only [CollatzResearch.WordTrace]
  refine ⟨23546820569119688441185915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31395760758826251254914553 23546820569119688441185915)
  ·
    refine ⟨35320230853679532661778873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23546820569119688441185915 35320230853679532661778873)
    ·
      refine ⟨26490173140259649496334155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35320230853679532661778873 26490173140259649496334155)
      ·
        refine ⟨39735259710389474244501233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26490173140259649496334155 39735259710389474244501233)
        ·
          refine ⟨29801444782792105683375925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39735259710389474244501233 29801444782792105683375925)
          ·
            refine ⟨2793885448386759907816493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29801444782792105683375925 2793885448386759907816493)
            ·
              refine ⟨1047707043145034965431185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2793885448386759907816493 1047707043145034965431185)
              ·
                refine ⟨785780282358776224073389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1047707043145034965431185 785780282358776224073389)
                ·
                  refine ⟨294667605884541084027521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 785780282358776224073389 294667605884541084027521)
                  ·
                    rfl

theorem cell21_1291192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 3].length) (baseStart_1291192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1291192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1291192 prefixEnd_1291192 := by exact prefixLift 1291192
  have htrace : WordTrace (prefixWord ++ tailWord_1291192) baseStart_1291192 baseEnd_1291192 := by
    simpa [prefixWord, tailWord_1291192, baseEnd_1291192] using wordTrace_append hprefix tailTrace_1291192
  have hstable : (prefixWord ++ tailWord_1291192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291192).length < 2 ^ (prefixWord ++ tailWord_1291192).sum := by decide
  have hdescent : baseEnd_1291192 < baseStart_1291192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291217 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 7]
def baseStart_1291217 : Nat := 118140960795 + 1291217 * 2 ^ 59
def prefixEnd_1291217 : Nat := 4983230072969 + 3 ^ 40 * 1291217 * 2
def baseEnd_1291217 : Nat := 294673311225146596110803

theorem tailTrace_1291217 : CollatzResearch.WordTrace tailWord_1291217 prefixEnd_1291217 294673311225146596110803 := by
  unfold tailWord_1291217
  simp only [CollatzResearch.WordTrace]
  refine ⟨47094552963148806152031905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31396368642099204101354603 47094552963148806152031905)
  ·
    refine ⟨35320914722361604614023929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47094552963148806152031905 35320914722361604614023929)
    ·
      refine ⟨26490686041771203460517947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35320914722361604614023929 26490686041771203460517947)
      ·
        refine ⟨39736029062656805190776921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26490686041771203460517947 39736029062656805190776921)
        ·
          refine ⟨29802021796992603893082691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39736029062656805190776921 29802021796992603893082691)
          ·
            refine ⟨44703032695488905839624037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29802021796992603893082691 44703032695488905839624037)
            ·
              refine ⟨8381818630404169844929507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44703032695488905839624037 8381818630404169844929507)
              ·
                refine ⟨12572727945606254767394261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8381818630404169844929507 12572727945606254767394261)
                ·
                  refine ⟨294673311225146596110803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12572727945606254767394261 294673311225146596110803)
                  ·
                    rfl

theorem cell21_1291217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_1291217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1291217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1291217 prefixEnd_1291217 := by exact prefixLift 1291217
  have htrace : WordTrace (prefixWord ++ tailWord_1291217) baseStart_1291217 baseEnd_1291217 := by
    simpa [prefixWord, tailWord_1291217, baseEnd_1291217] using wordTrace_append hprefix tailTrace_1291217
  have hstable : (prefixWord ++ tailWord_1291217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291217).length < 2 ^ (prefixWord ++ tailWord_1291217).sum := by decide
  have hdescent : baseEnd_1291217 < baseStart_1291217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291265 : List Nat := [1, 2, 4, 1, 2, 2, 2, 3, 4]
def baseStart_1291265 : Nat := 118140960795 + 1291265 * 2 ^ 59
def prefixEnd_1291265 : Nat := 4983230072969 + 3 ^ 40 * 1291265 * 2
def baseEnd_1291265 : Nat := 294684265479109179310705

theorem tailTrace_1291265 : CollatzResearch.WordTrace tailWord_1291265 prefixEnd_1291265 294684265479109179310705 := by
  unfold tailWord_1291265
  simp only [CollatzResearch.WordTrace]
  refine ⟨47096303666974910349779249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31397535777983273566519499 47096303666974910349779249)
  ·
    refine ⟨35322227750231182762334437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47096303666974910349779249 35322227750231182762334437)
    ·
      refine ⟨6622917703168346767937707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35322227750231182762334437 6622917703168346767937707)
      ·
        refine ⟨9934376554752520151906561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6622917703168346767937707 9934376554752520151906561)
        ·
          refine ⟨7450782416064390113929921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9934376554752520151906561 7450782416064390113929921)
          ·
            refine ⟨5588086812048292585447441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7450782416064390113929921 5588086812048292585447441)
            ·
              refine ⟨4191065109036219439085581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5588086812048292585447441 4191065109036219439085581)
              ·
                refine ⟨1571649415888582289657093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4191065109036219439085581 1571649415888582289657093)
                ·
                  refine ⟨294684265479109179310705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1571649415888582289657093 294684265479109179310705)
                  ·
                    rfl

theorem cell21_1291265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 4].length) (baseStart_1291265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1291265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1291265 prefixEnd_1291265 := by exact prefixLift 1291265
  have htrace : WordTrace (prefixWord ++ tailWord_1291265) baseStart_1291265 baseEnd_1291265 := by
    simpa [prefixWord, tailWord_1291265, baseEnd_1291265] using wordTrace_append hprefix tailTrace_1291265
  have hstable : (prefixWord ++ tailWord_1291265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291265).length < 2 ^ (prefixWord ++ tailWord_1291265).sum := by decide
  have hdescent : baseEnd_1291265 < baseStart_1291265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291296 : List Nat := [2, 1, 1, 7, 1, 1, 8]
def baseStart_1291296 : Nat := 118140960795 + 1291296 * 2 ^ 59
def prefixEnd_1291296 : Nat := 4983230072969 + 3 ^ 40 * 1291296 * 2
def baseEnd_1291296 : Nat := 32743482233495557143775

theorem tailTrace_1291296 : CollatzResearch.WordTrace tailWord_1291296 prefixEnd_1291296 32743482233495557143775 := by
  unfold tailWord_1291296
  simp only [CollatzResearch.WordTrace]
  refine ⟨23548717164931301322078871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31398289553241735096105161 23548717164931301322078871)
  ·
    refine ⟨35323075747396951983118307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23548717164931301322078871 35323075747396951983118307)
    ·
      refine ⟨52984613621095427974677461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35323075747396951983118307 52984613621095427974677461)
      ·
        refine ⟨1241826881744424093156503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 52984613621095427974677461 1241826881744424093156503)
        ·
          refine ⟨1862740322616636139734755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1241826881744424093156503 1862740322616636139734755)
          ·
            refine ⟨2794110483924954209602133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1862740322616636139734755 2794110483924954209602133)
            ·
              refine ⟨32743482233495557143775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2794110483924954209602133 32743482233495557143775)
              ·
                rfl

theorem cell21_1291296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 8].length) (baseStart_1291296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1291296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1291296 prefixEnd_1291296 := by exact prefixLift 1291296
  have htrace : WordTrace (prefixWord ++ tailWord_1291296) baseStart_1291296 baseEnd_1291296 := by
    simpa [prefixWord, tailWord_1291296, baseEnd_1291296] using wordTrace_append hprefix tailTrace_1291296
  have hstable : (prefixWord ++ tailWord_1291296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291296).length < 2 ^ (prefixWord ++ tailWord_1291296).sum := by decide
  have hdescent : baseEnd_1291296 < baseStart_1291296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291341 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1291341 : Nat := 118140960795 + 1291341 * 2 ^ 59
def prefixEnd_1291341 : Nat := 4983230072969 + 3 ^ 40 * 1291341 * 2
def baseEnd_1291341 : Nat := 294701609714549936043883

theorem tailTrace_1291341 : CollatzResearch.WordTrace tailWord_1291341 prefixEnd_1291341 294701609714549936043883 := by
  unfold tailWord_1291341
  simp only [CollatzResearch.WordTrace]
  refine ⟨47099075614699575329545877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31399383743133050219697251 47099075614699575329545877)
  ·
    refine ⟨2207769169439042593572463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47099075614699575329545877 2207769169439042593572463)
    ·
      refine ⟨3311653754158563890358695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2207769169439042593572463 3311653754158563890358695)
      ·
        refine ⟨4967480631237845835538043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3311653754158563890358695 4967480631237845835538043)
        ·
          refine ⟨7451220946856768753307065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4967480631237845835538043 7451220946856768753307065)
          ·
            refine ⟨5588415710142576564980299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7451220946856768753307065 5588415710142576564980299)
            ·
              refine ⟨8382623565213864847470449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5588415710142576564980299 8382623565213864847470449)
              ·
                refine ⟨6286967673910398635602837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8382623565213864847470449 6286967673910398635602837)
                ·
                  refine ⟨294701609714549936043883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6286967673910398635602837 294701609714549936043883)
                  ·
                    rfl

theorem cell21_1291341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1291341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1291341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1291341 prefixEnd_1291341 := by exact prefixLift 1291341
  have htrace : WordTrace (prefixWord ++ tailWord_1291341) baseStart_1291341 baseEnd_1291341 := by
    simpa [prefixWord, tailWord_1291341, baseEnd_1291341] using wordTrace_append hprefix tailTrace_1291341
  have hstable : (prefixWord ++ tailWord_1291341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291341).length < 2 ^ (prefixWord ++ tailWord_1291341).sum := by decide
  have hdescent : baseEnd_1291341 < baseStart_1291341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291420 : List Nat := [2, 2, 3, 2, 1, 2, 4, 2, 3]
def baseStart_1291420 : Nat := 118140960795 + 1291420 * 2 ^ 59
def prefixEnd_1291420 : Nat := 4983230072969 + 3 ^ 40 * 1291420 * 2
def baseEnd_1291420 : Nat := 294719638590863354227055

theorem tailTrace_1291420 : CollatzResearch.WordTrace tailWord_1291420 prefixEnd_1291420 294719638590863354227055 := by
  unfold tailWord_1291420
  simp only [CollatzResearch.WordTrace]
  refine ⟨23550978490706685910835857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31401304654275581214447809 23550978490706685910835857)
  ·
    refine ⟨17663233868030014433126893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23550978490706685910835857 17663233868030014433126893)
    ·
      refine ⟨6623712700511255412422585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17663233868030014433126893 6623712700511255412422585)
      ·
        refine ⟨4967784525383441559316939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6623712700511255412422585 4967784525383441559316939)
        ·
          refine ⟨7451676788075162338975409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4967784525383441559316939 7451676788075162338975409)
          ·
            refine ⟨5588757591056371754231557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7451676788075162338975409 5588757591056371754231557)
            ·
              refine ⟨1047892048323069703918417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5588757591056371754231557 1047892048323069703918417)
              ·
                refine ⟨785919036242302277938813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1047892048323069703918417 785919036242302277938813)
                ·
                  refine ⟨294719638590863354227055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 785919036242302277938813 294719638590863354227055)
                  ·
                    rfl

theorem cell21_1291420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 3].length) (baseStart_1291420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1291420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1291420 prefixEnd_1291420 := by exact prefixLift 1291420
  have htrace : WordTrace (prefixWord ++ tailWord_1291420) baseStart_1291420 baseEnd_1291420 := by
    simpa [prefixWord, tailWord_1291420, baseEnd_1291420] using wordTrace_append hprefix tailTrace_1291420
  have hstable : (prefixWord ++ tailWord_1291420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291420).length < 2 ^ (prefixWord ++ tailWord_1291420).sum := by decide
  have hdescent : baseEnd_1291420 < baseStart_1291420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291434 : List Nat := [3, 1, 5, 1, 1, 1, 2, 3, 4]
def baseStart_1291434 : Nat := 118140960795 + 1291434 * 2 ^ 59
def prefixEnd_1291434 : Nat := 4983230072969 + 3 ^ 40 * 1291434 * 2
def baseEnd_1291434 : Nat := 294722833581602440993693

theorem tailTrace_1291434 : CollatzResearch.WordTrace tailWord_1291434 prefixEnd_1291434 294722833581602440993693 := by
  unfold tailWord_1291434
  simp only [CollatzResearch.WordTrace]
  refine ⟨11775616900840663053170339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31401645068908434808454237 11775616900840663053170339)
  ·
    refine ⟨17663425351260994579755509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11775616900840663053170339 17663425351260994579755509)
    ·
      refine ⟨1655946126680718241852079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17663425351260994579755509 1655946126680718241852079)
      ·
        refine ⟨2483919190021077362778119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1655946126680718241852079 2483919190021077362778119)
        ·
          refine ⟨3725878785031616044167179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2483919190021077362778119 3725878785031616044167179)
          ·
            refine ⟨5588818177547424066250769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3725878785031616044167179 5588818177547424066250769)
            ·
              refine ⟨4191613633160568049688077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5588818177547424066250769 4191613633160568049688077)
              ·
                refine ⟨1571855112435213018633029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4191613633160568049688077 1571855112435213018633029)
                ·
                  refine ⟨294722833581602440993693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1571855112435213018633029 294722833581602440993693)
                  ·
                    rfl

theorem cell21_1291434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_1291434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1291434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1291434 prefixEnd_1291434 := by exact prefixLift 1291434
  have htrace : WordTrace (prefixWord ++ tailWord_1291434) baseStart_1291434 baseEnd_1291434 := by
    simpa [prefixWord, tailWord_1291434, baseEnd_1291434] using wordTrace_append hprefix tailTrace_1291434
  have hstable : (prefixWord ++ tailWord_1291434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291434).length < 2 ^ (prefixWord ++ tailWord_1291434).sum := by decide
  have hdescent : baseEnd_1291434 < baseStart_1291434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291507 : List Nat := [1, 1, 1, 2, 2, 5, 4, 5]
def baseStart_1291507 : Nat := 118140960795 + 1291507 * 2 ^ 59
def prefixEnd_1291507 : Nat := 4983230072969 + 3 ^ 40 * 1291507 * 2
def baseEnd_1291507 : Nat := 98246497725390178758959

theorem tailTrace_1291507 : CollatzResearch.WordTrace tailWord_1291507 prefixEnd_1291507 98246497725390178758959 := by
  unfold tailWord_1291507
  simp only [CollatzResearch.WordTrace]
  refine ⟨47105130132098185680088775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31403420088065457120059183 47105130132098185680088775)
  ·
    refine ⟨70657695198147278520133163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47105130132098185680088775 70657695198147278520133163)
    ·
      refine ⟨105986542797220917780199745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70657695198147278520133163 105986542797220917780199745)
      ·
        refine ⟨79489907097915688335149809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105986542797220917780199745 79489907097915688335149809)
        ·
          refine ⟨59617430323436766251362357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79489907097915688335149809 59617430323436766251362357)
          ·
            refine ⟨5589134092822196836065221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59617430323436766251362357 5589134092822196836065221)
            ·
              refine ⟨1047962642404161906762229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5589134092822196836065221 1047962642404161906762229)
              ·
                refine ⟨98246497725390178758959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1047962642404161906762229 98246497725390178758959)
                ·
                  rfl

theorem cell21_1291507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 5].length) (baseStart_1291507 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1291507 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1291507 prefixEnd_1291507 := by exact prefixLift 1291507
  have htrace : WordTrace (prefixWord ++ tailWord_1291507) baseStart_1291507 baseEnd_1291507 := by
    simpa [prefixWord, tailWord_1291507, baseEnd_1291507] using wordTrace_append hprefix tailTrace_1291507
  have hstable : (prefixWord ++ tailWord_1291507).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291507).length < 2 ^ (prefixWord ++ tailWord_1291507).sum := by decide
  have hdescent : baseEnd_1291507 < baseStart_1291507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291673 : List Nat := [1, 2, 1, 2, 1, 5, 2, 2, 5]
def baseStart_1291673 : Nat := 118140960795 + 1291673 * 2 ^ 59
def prefixEnd_1291673 : Nat := 4983230072969 + 3 ^ 40 * 1291673 * 2
def baseEnd_1291673 : Nat := 294777376637791136509871

theorem tailTrace_1291673 : CollatzResearch.WordTrace tailWord_1291673 prefixEnd_1291673 294777376637791136509871 := by
  unfold tailWord_1291673
  simp only [CollatzResearch.WordTrace]
  refine ⟨47111184649496796030631673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31407456432997864020421115 47111184649496796030631673)
  ·
    refine ⟨35333388487122597022973755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47111184649496796030631673 35333388487122597022973755)
    ·
      refine ⟨53000082730683895534460633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35333388487122597022973755 53000082730683895534460633)
      ·
        refine ⟨39750062048012921650845475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53000082730683895534460633 39750062048012921650845475)
        ·
          refine ⟨59625093072019382476268213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39750062048012921650845475 59625093072019382476268213)
          ·
            refine ⟨5589852475501817107150145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59625093072019382476268213 5589852475501817107150145)
            ·
              refine ⟨4192389356626362830362609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5589852475501817107150145 4192389356626362830362609)
              ·
                refine ⟨3144292017469772122771957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4192389356626362830362609 3144292017469772122771957)
                ·
                  refine ⟨294777376637791136509871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3144292017469772122771957 294777376637791136509871)
                  ·
                    rfl

theorem cell21_1291673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_1291673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1291673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1291673 prefixEnd_1291673 := by exact prefixLift 1291673
  have htrace : WordTrace (prefixWord ++ tailWord_1291673) baseStart_1291673 baseEnd_1291673 := by
    simpa [prefixWord, tailWord_1291673, baseEnd_1291673] using wordTrace_append hprefix tailTrace_1291673
  have hstable : (prefixWord ++ tailWord_1291673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291673).length < 2 ^ (prefixWord ++ tailWord_1291673).sum := by decide
  have hdescent : baseEnd_1291673 < baseStart_1291673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291676 : List Nat := [2, 2, 3, 4, 1, 1, 1, 7]
def baseStart_1291676 : Nat := 118140960795 + 1291676 * 2 ^ 59
def prefixEnd_1291676 : Nat := 4983230072969 + 3 ^ 40 * 1291676 * 2
def baseEnd_1291676 : Nat := 98259353759554599319955

theorem tailTrace_1291676 : CollatzResearch.WordTrace tailWord_1291676 prefixEnd_1291676 98259353759554599319955 := by
  unfold tailWord_1291676
  simp only [CollatzResearch.WordTrace]
  refine ⟨23555647034242963771495441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31407529378990618361993921 23555647034242963771495441)
  ·
    refine ⟨17666735275682222828621581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23555647034242963771495441 17666735275682222828621581)
    ·
      refine ⟨6625025728380833560733093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17666735275682222828621581 6625025728380833560733093)
      ·
        refine ⟨1242192324071406292637455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6625025728380833560733093 1242192324071406292637455)
        ·
          refine ⟨1863288486107109438956183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1242192324071406292637455 1863288486107109438956183)
          ·
            refine ⟨2794932729160664158434275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1863288486107109438956183 2794932729160664158434275)
            ·
              refine ⟨4192399093740996237651413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2794932729160664158434275 4192399093740996237651413)
              ·
                refine ⟨98259353759554599319955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4192399093740996237651413 98259353759554599319955)
                ·
                  rfl

theorem cell21_1291676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 7].length) (baseStart_1291676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1291676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1291676 prefixEnd_1291676 := by exact prefixLift 1291676
  have htrace : WordTrace (prefixWord ++ tailWord_1291676) baseStart_1291676 baseEnd_1291676 := by
    simpa [prefixWord, tailWord_1291676, baseEnd_1291676] using wordTrace_append hprefix tailTrace_1291676
  have hstable : (prefixWord ++ tailWord_1291676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291676).length < 2 ^ (prefixWord ++ tailWord_1291676).sum := by decide
  have hdescent : baseEnd_1291676 < baseStart_1291676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291862 : List Nat := [5, 2, 2, 2, 2, 1, 7]
def baseStart_1291862 : Nat := 118140960795 + 1291862 * 2 ^ 59
def prefixEnd_1291862 : Nat := 4983230072969 + 3 ^ 40 * 1291862 * 2
def baseEnd_1291862 : Nat := 32757834334752089762165

theorem tailTrace_1291862 : CollatzResearch.WordTrace tailWord_1291862 prefixEnd_1291862 32757834334752089762165 := by
  unfold tailWord_1291862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2944879877863255081828865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31412052030541387539507893 2944879877863255081828865)
  ·
    refine ⟨2208659908397441311371649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2944879877863255081828865 2208659908397441311371649)
    ·
      refine ⟨1656494931298080983528737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2208659908397441311371649 1656494931298080983528737)
      ·
        refine ⟨1242371198473560737646553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1656494931298080983528737 1242371198473560737646553)
        ·
          refine ⟨931778398855170553234915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1242371198473560737646553 931778398855170553234915)
          ·
            refine ⟨1397667598282755829852373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 931778398855170553234915 1397667598282755829852373)
            ·
              refine ⟨32757834334752089762165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1397667598282755829852373 32757834334752089762165)
              ·
                rfl

theorem cell21_1291862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 7].length) (baseStart_1291862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1291862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1291862 prefixEnd_1291862 := by exact prefixLift 1291862
  have htrace : WordTrace (prefixWord ++ tailWord_1291862) baseStart_1291862 baseEnd_1291862 := by
    simpa [prefixWord, tailWord_1291862, baseEnd_1291862] using wordTrace_append hprefix tailTrace_1291862
  have hstable : (prefixWord ++ tailWord_1291862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291862).length < 2 ^ (prefixWord ++ tailWord_1291862).sum := by decide
  have hdescent : baseEnd_1291862 < baseStart_1291862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291890 : List Nat := [3, 2, 1, 2, 3, 3, 2, 1, 4]
def baseStart_1291890 : Nat := 118140960795 + 1291890 * 2 ^ 59
def prefixEnd_1291890 : Nat := 4983230072969 + 3 ^ 40 * 1291890 * 2
def baseEnd_1291890 : Nat := 294826898994246981392761

theorem tailTrace_1291890 : CollatzResearch.WordTrace tailWord_1291890 prefixEnd_1291890 294826898994246981392761 := by
  unfold tailWord_1291890
  simp only [CollatzResearch.WordTrace]
  refine ⟨11779774822427660522820281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31412732859807094727520749 11779774822427660522820281)
  ·
    refine ⟨8834831116820745392115211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11779774822427660522820281 8834831116820745392115211)
    ·
      refine ⟨13252246675231118088172817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8834831116820745392115211 13252246675231118088172817)
      ·
        refine ⟨9939185006423338566129613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13252246675231118088172817 9939185006423338566129613)
        ·
          refine ⟨3727194377408751962298605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9939185006423338566129613 3727194377408751962298605)
          ·
            refine ⟨1397697891528281985861977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3727194377408751962298605 1397697891528281985861977)
            ·
              refine ⟨1048273418646211489396483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1397697891528281985861977 1048273418646211489396483)
              ·
                refine ⟨1572410127969317234094725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1048273418646211489396483 1572410127969317234094725)
                ·
                  refine ⟨294826898994246981392761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1572410127969317234094725 294826898994246981392761)
                  ·
                    rfl

theorem cell21_1291890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_1291890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1291890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1291890 prefixEnd_1291890 := by exact prefixLift 1291890
  have htrace : WordTrace (prefixWord ++ tailWord_1291890) baseStart_1291890 baseEnd_1291890 := by
    simpa [prefixWord, tailWord_1291890, baseEnd_1291890] using wordTrace_append hprefix tailTrace_1291890
  have hstable : (prefixWord ++ tailWord_1291890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291890).length < 2 ^ (prefixWord ++ tailWord_1291890).sum := by decide
  have hdescent : baseEnd_1291890 < baseStart_1291890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291991 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 6]
def baseStart_1291991 : Nat := 118140960795 + 1291991 * 2 ^ 59
def prefixEnd_1291991 : Nat := 4983230072969 + 3 ^ 40 * 1291991 * 2
def baseEnd_1291991 : Nat := 294849948570293250209221

theorem tailTrace_1291991 : CollatzResearch.WordTrace tailWord_1291991 prefixEnd_1291991 294849948570293250209221 := by
  unfold tailWord_1291991
  simp only [CollatzResearch.WordTrace]
  refine ⟨47122783062344736340707827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31415188708229824227138551 47122783062344736340707827)
  ·
    refine ⟨70684174593517104511061741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47122783062344736340707827 70684174593517104511061741)
    ·
      refine ⟨26506565472568914191648153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70684174593517104511061741 26506565472568914191648153)
      ·
        refine ⟨19879924104426685643736115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26506565472568914191648153 19879924104426685643736115)
        ·
          refine ⟨29819886156640028465604173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19879924104426685643736115 29819886156640028465604173)
          ·
            refine ⟨11182457308740010674601565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29819886156640028465604173 11182457308740010674601565)
            ·
              refine ⟨4193421490777504002975587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11182457308740010674601565 4193421490777504002975587)
              ·
                refine ⟨6290132236166256004463381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4193421490777504002975587 6290132236166256004463381)
                ·
                  refine ⟨294849948570293250209221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6290132236166256004463381 294849948570293250209221)
                  ·
                    rfl

theorem cell21_1291991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 6].length) (baseStart_1291991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1291991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1291991 prefixEnd_1291991 := by exact prefixLift 1291991
  have htrace : WordTrace (prefixWord ++ tailWord_1291991) baseStart_1291991 baseEnd_1291991 := by
    simpa [prefixWord, tailWord_1291991, baseEnd_1291991] using wordTrace_append hprefix tailTrace_1291991
  have hstable : (prefixWord ++ tailWord_1291991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291991).length < 2 ^ (prefixWord ++ tailWord_1291991).sum := by decide
  have hdescent : baseEnd_1291991 < baseStart_1291991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1291994 : List Nat := [3, 1, 1, 2, 2, 3, 2, 4, 3]
def baseStart_1291994 : Nat := 118140960795 + 1291994 * 2 ^ 59
def prefixEnd_1291994 : Nat := 4983230072969 + 3 ^ 40 * 1291994 * 2
def baseEnd_1291994 : Nat := 294850633211165911659215

theorem tailTrace_1291994 : CollatzResearch.WordTrace tailWord_1291994 prefixEnd_1291994 294850633211165911659215 := by
  unfold tailWord_1291994
  simp only [CollatzResearch.WordTrace]
  refine ⟨11780723120333466963266759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31415261654222578568711357 11780723120333466963266759)
  ·
    refine ⟨17671084680500200444900139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11780723120333466963266759 17671084680500200444900139)
    ·
      refine ⟨26506627020750300667350209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17671084680500200444900139 26506627020750300667350209)
      ·
        refine ⟨19879970265562725500512657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26506627020750300667350209 19879970265562725500512657)
        ·
          refine ⟨14909977699172044125384493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19879970265562725500512657 14909977699172044125384493)
          ·
            refine ⟨5591241637189516547019185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14909977699172044125384493 5591241637189516547019185)
            ·
              refine ⟨4193431227892137410264389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5591241637189516547019185 4193431227892137410264389)
              ·
                refine ⟨786268355229775764424573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4193431227892137410264389 786268355229775764424573)
                ·
                  refine ⟨294850633211165911659215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 786268355229775764424573 294850633211165911659215)
                  ·
                    rfl

theorem cell21_1291994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 3].length) (baseStart_1291994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1291994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1291994 prefixEnd_1291994 := by exact prefixLift 1291994
  have htrace : WordTrace (prefixWord ++ tailWord_1291994) baseStart_1291994 baseEnd_1291994 := by
    simpa [prefixWord, tailWord_1291994, baseEnd_1291994] using wordTrace_append hprefix tailTrace_1291994
  have hstable : (prefixWord ++ tailWord_1291994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1291994).length < 2 ^ (prefixWord ++ tailWord_1291994).sum := by decide
  have hdescent : baseEnd_1291994 < baseStart_1291994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1291994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292039 : List Nat := [1, 1, 4, 4, 2, 2, 7]
def baseStart_1292039 : Nat := 118140960795 + 1292039 * 2 ^ 59
def prefixEnd_1292039 : Nat := 4983230072969 + 3 ^ 40 * 1292039 * 2
def baseEnd_1292039 : Nat := 32762322536028425934347

theorem tailTrace_1292039 : CollatzResearch.WordTrace tailWord_1292039 prefixEnd_1292039 32762322536028425934347 := by
  unfold tailWord_1292039
  simp only [CollatzResearch.WordTrace]
  refine ⟨47124533766170840538455171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31416355844113893692303447 47124533766170840538455171)
  ·
    refine ⟨70686800649256260807682757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47124533766170840538455171 70686800649256260807682757)
    ·
      refine ⟨13253775121735548901440517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70686800649256260807682757 13253775121735548901440517)
      ·
        refine ⟨2485082835325415419020097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13253775121735548901440517 2485082835325415419020097)
        ·
          refine ⟨1863812126494061564265073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2485082835325415419020097 1863812126494061564265073)
          ·
            refine ⟨1397859094870546173198805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1863812126494061564265073 1397859094870546173198805)
            ·
              refine ⟨32762322536028425934347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1397859094870546173198805 32762322536028425934347)
              ·
                rfl

theorem cell21_1292039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 7].length) (baseStart_1292039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1292039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1292039 prefixEnd_1292039 := by exact prefixLift 1292039
  have htrace : WordTrace (prefixWord ++ tailWord_1292039) baseStart_1292039 baseEnd_1292039 := by
    simpa [prefixWord, tailWord_1292039, baseEnd_1292039] using wordTrace_append hprefix tailTrace_1292039
  have hstable : (prefixWord ++ tailWord_1292039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292039).length < 2 ^ (prefixWord ++ tailWord_1292039).sum := by decide
  have hdescent : baseEnd_1292039 < baseStart_1292039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292053 : List Nat := [1, 3, 2, 1, 2, 3, 3, 1, 5]
def baseStart_1292053 : Nat := 118140960795 + 1292053 * 2 ^ 59
def prefixEnd_1292053 : Nat := 4983230072969 + 3 ^ 40 * 1292053 * 2
def baseEnd_1292053 : Nat := 294864097814994920175761

theorem tailTrace_1292053 : CollatzResearch.WordTrace tailWord_1292053 prefixEnd_1292053 294864097814994920175761 := by
  unfold tailWord_1292053
  simp only [CollatzResearch.WordTrace]
  refine ⟨47125044388120120929464813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31416696258746747286309875 47125044388120120929464813)
  ·
    refine ⟨17671891645545045348549305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47125044388120120929464813 17671891645545045348549305)
    ·
      refine ⟨13253918734158784011411979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17671891645545045348549305 13253918734158784011411979)
      ·
        refine ⟨19880878101238176017117969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13253918734158784011411979 19880878101238176017117969)
        ·
          refine ⟨14910658575928632012838477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19880878101238176017117969 14910658575928632012838477)
          ·
            refine ⟨5591496965973237004814429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14910658575928632012838477 5591496965973237004814429)
            ·
              refine ⟨2096811362239963876805411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5591496965973237004814429 2096811362239963876805411)
              ·
                refine ⟨3145217043359945815208117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2096811362239963876805411 3145217043359945815208117)
                ·
                  refine ⟨294864097814994920175761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3145217043359945815208117 294864097814994920175761)
                  ·
                    rfl

theorem cell21_1292053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_1292053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1292053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1292053 prefixEnd_1292053 := by exact prefixLift 1292053
  have htrace : WordTrace (prefixWord ++ tailWord_1292053) baseStart_1292053 baseEnd_1292053 := by
    simpa [prefixWord, tailWord_1292053, baseEnd_1292053] using wordTrace_append hprefix tailTrace_1292053
  have hstable : (prefixWord ++ tailWord_1292053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292053).length < 2 ^ (prefixWord ++ tailWord_1292053).sum := by decide
  have hdescent : baseEnd_1292053 < baseStart_1292053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292112 : List Nat := [2, 1, 1, 1, 1, 4, 1, 5, 5]
def baseStart_1292112 : Nat := 118140960795 + 1292112 * 2 ^ 59
def prefixEnd_1292112 : Nat := 4983230072969 + 3 ^ 40 * 1292112 * 2
def baseEnd_1292112 : Nat := 294877562418823928692307

theorem tailTrace_1292112 : CollatzResearch.WordTrace tailWord_1292112 prefixEnd_1292112 294877562418823928692307 := by
  unfold tailWord_1292112
  simp only [CollatzResearch.WordTrace]
  refine ⟨23563598147453187002931295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31418130863270916003908393 23563598147453187002931295)
  ·
    refine ⟨35345397221179780504396943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23563598147453187002931295 35345397221179780504396943)
    ·
      refine ⟨53018095831769670756595415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35345397221179780504396943 53018095831769670756595415)
      ·
        refine ⟨79527143747654506134893123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53018095831769670756595415 79527143747654506134893123)
        ·
          refine ⟨119290715621481759202339685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79527143747654506134893123 119290715621481759202339685)
          ·
            refine ⟨22367009179027829850438691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119290715621481759202339685 22367009179027829850438691)
            ·
              refine ⟨33550513768541744775658037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22367009179027829850438691 33550513768541744775658037)
              ·
                refine ⟨3145360665800788572717941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33550513768541744775658037 3145360665800788572717941)
                ·
                  refine ⟨294877562418823928692307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3145360665800788572717941 294877562418823928692307)
                  ·
                    rfl

theorem cell21_1292112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_1292112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1292112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1292112 prefixEnd_1292112 := by exact prefixLift 1292112
  have htrace : WordTrace (prefixWord ++ tailWord_1292112) baseStart_1292112 baseEnd_1292112 := by
    simpa [prefixWord, tailWord_1292112, baseEnd_1292112] using wordTrace_append hprefix tailTrace_1292112
  have hstable : (prefixWord ++ tailWord_1292112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292112).length < 2 ^ (prefixWord ++ tailWord_1292112).sum := by decide
  have hdescent : baseEnd_1292112 < baseStart_1292112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292222 : List Nat := [4, 2, 1, 1, 1, 5, 1, 1, 5]
def baseStart_1292222 : Nat := 118140960795 + 1292222 * 2 ^ 59
def prefixEnd_1292222 : Nat := 4983230072969 + 3 ^ 40 * 1292222 * 2
def baseEnd_1292222 : Nat := 294902665917488181858749

theorem tailTrace_1292222 : CollatzResearch.WordTrace tailWord_1292222 prefixEnd_1292222 294902665917488181858749 := by
  unfold tailWord_1292222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5891401040563482849045865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31420805549671908528244613 5891401040563482849045865)
  ·
    refine ⟨4418550780422612136784399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5891401040563482849045865 4418550780422612136784399)
    ·
      refine ⟨6627826170633918205176599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4418550780422612136784399 6627826170633918205176599)
      ·
        refine ⟨9941739255950877307764899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6627826170633918205176599 9941739255950877307764899)
        ·
          refine ⟨14912608883926315961647349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9941739255950877307764899 14912608883926315961647349)
          ·
            refine ⟨1398057082868092121404439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14912608883926315961647349 1398057082868092121404439)
            ·
              refine ⟨2097085624302138182106659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1398057082868092121404439 2097085624302138182106659)
              ·
                refine ⟨3145628436453207273159989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2097085624302138182106659 3145628436453207273159989)
                ·
                  refine ⟨294902665917488181858749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3145628436453207273159989 294902665917488181858749)
                  ·
                    rfl

theorem cell21_1292222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_1292222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1292222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1292222 prefixEnd_1292222 := by exact prefixLift 1292222
  have htrace : WordTrace (prefixWord ++ tailWord_1292222) baseStart_1292222 baseEnd_1292222 := by
    simpa [prefixWord, tailWord_1292222, baseEnd_1292222] using wordTrace_append hprefix tailTrace_1292222
  have hstable : (prefixWord ++ tailWord_1292222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292222).length < 2 ^ (prefixWord ++ tailWord_1292222).sum := by decide
  have hdescent : baseEnd_1292222 < baseStart_1292222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292236 : List Nat := [2, 2, 1, 4, 1, 3, 1, 3, 4]
def baseStart_1292236 : Nat := 118140960795 + 1292236 * 2 ^ 59
def prefixEnd_1292236 : Nat := 4983230072969 + 3 ^ 40 * 1292236 * 2
def baseEnd_1292236 : Nat := 294905860908227268625387

theorem tailTrace_1292236 : CollatzResearch.WordTrace tailWord_1292236 prefixEnd_1292236 294905860908227268625387 := by
  unfold tailWord_1292236
  simp only [CollatzResearch.WordTrace]
  refine ⟨23565859473228571591688281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31421145964304762122251041 23565859473228571591688281)
  ·
    refine ⟨17674394604921428693766211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23565859473228571591688281 17674394604921428693766211)
    ·
      refine ⟨26511591907382143040649317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17674394604921428693766211 26511591907382143040649317)
      ·
        refine ⟨4970923482634151820121747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26511591907382143040649317 4970923482634151820121747)
        ·
          refine ⟨7456385223951227730182621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4970923482634151820121747 7456385223951227730182621)
          ·
            refine ⟨2796144458981710398818483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7456385223951227730182621 2796144458981710398818483)
            ·
              refine ⟨4194216688472565598227725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2796144458981710398818483 4194216688472565598227725)
              ·
                refine ⟨1572831258177212099335397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4194216688472565598227725 1572831258177212099335397)
                ·
                  refine ⟨294905860908227268625387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1572831258177212099335397 294905860908227268625387)
                  ·
                    rfl

theorem cell21_1292236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_1292236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1292236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1292236 prefixEnd_1292236 := by exact prefixLift 1292236
  have htrace : WordTrace (prefixWord ++ tailWord_1292236) baseStart_1292236 baseEnd_1292236 := by
    simpa [prefixWord, tailWord_1292236, baseEnd_1292236] using wordTrace_append hprefix tailTrace_1292236
  have hstable : (prefixWord ++ tailWord_1292236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292236).length < 2 ^ (prefixWord ++ tailWord_1292236).sum := by decide
  have hdescent : baseEnd_1292236 < baseStart_1292236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292402 : List Nat := [3, 2, 1, 2, 2, 3, 2, 6]
def baseStart_1292402 : Nat := 118140960795 + 1292402 * 2 ^ 59
def prefixEnd_1292402 : Nat := 4983230072969 + 3 ^ 40 * 1292402 * 2
def baseEnd_1292402 : Nat := 98314581456615956286127

theorem tailTrace_1292402 : CollatzResearch.WordTrace tailWord_1292402 prefixEnd_1292402 98314581456615956286127 := by
  unfold tailWord_1292402
  simp only [CollatzResearch.WordTrace]
  refine ⟨11784443365963938383479865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31425182309237169022612973 11784443365963938383479865)
  ·
    refine ⟨8838332524472953787609899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11784443365963938383479865 8838332524472953787609899)
    ·
      refine ⟨13257498786709430681414849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8838332524472953787609899 13257498786709430681414849)
      ·
        refine ⟨9943124090032073011061137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13257498786709430681414849 9943124090032073011061137)
        ·
          refine ⟨7457343067524054758295853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9943124090032073011061137 7457343067524054758295853)
          ·
            refine ⟨2796503650321520534360945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7457343067524054758295853 2796503650321520534360945)
            ·
              refine ⟨2097377737741140400770709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2796503650321520534360945 2097377737741140400770709)
              ·
                refine ⟨98314581456615956286127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2097377737741140400770709 98314581456615956286127)
                ·
                  rfl

theorem cell21_1292402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_1292402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1292402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1292402 prefixEnd_1292402 := by exact prefixLift 1292402
  have htrace : WordTrace (prefixWord ++ tailWord_1292402) baseStart_1292402 baseEnd_1292402 := by
    simpa [prefixWord, tailWord_1292402, baseEnd_1292402] using wordTrace_append hprefix tailTrace_1292402
  have hstable : (prefixWord ++ tailWord_1292402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292402).length < 2 ^ (prefixWord ++ tailWord_1292402).sum := by decide
  have hdescent : baseEnd_1292402 < baseStart_1292402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292509 : List Nat := [1, 4, 3, 2, 1, 1, 1, 3, 5]
def baseStart_1292509 : Nat := 118140960795 + 1292509 * 2 ^ 59
def prefixEnd_1292509 : Nat := 4983230072969 + 3 ^ 40 * 1292509 * 2
def baseEnd_1292509 : Nat := 294968163227639460574829

theorem tailTrace_1292509 : CollatzResearch.WordTrace tailWord_1292509 prefixEnd_1292509 294968163227639460574829 := by
  unfold tailWord_1292509
  simp only [CollatzResearch.WordTrace]
  refine ⟨47141676074468110808064581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31427784049645407205376387 47141676074468110808064581)
  ·
    refine ⟨8839064263962770776512109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47141676074468110808064581 8839064263962770776512109)
    ·
      refine ⟨3314649098986039041192041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8839064263962770776512109 3314649098986039041192041)
      ·
        refine ⟨2485986824239529280894031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3314649098986039041192041 2485986824239529280894031)
        ·
          refine ⟨3728980236359293921341047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2485986824239529280894031 3728980236359293921341047)
          ·
            refine ⟨5593470354538940882011571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3728980236359293921341047 5593470354538940882011571)
            ·
              refine ⟨8390205531808411323017357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5593470354538940882011571 8390205531808411323017357)
              ·
                refine ⟨3146327074428154246131509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8390205531808411323017357 3146327074428154246131509)
                ·
                  refine ⟨294968163227639460574829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3146327074428154246131509 294968163227639460574829)
                  ·
                    rfl

theorem cell21_1292509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_1292509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1292509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1292509 prefixEnd_1292509 := by exact prefixLift 1292509
  have htrace : WordTrace (prefixWord ++ tailWord_1292509) baseStart_1292509 baseEnd_1292509 := by
    simpa [prefixWord, tailWord_1292509, baseEnd_1292509] using wordTrace_append hprefix tailTrace_1292509
  have hstable : (prefixWord ++ tailWord_1292509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292509).length < 2 ^ (prefixWord ++ tailWord_1292509).sum := by decide
  have hdescent : baseEnd_1292509 < baseStart_1292509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292574 : List Nat := [4, 3, 2, 1, 1, 1, 4, 1, 4]
def baseStart_1292574 : Nat := 118140960795 + 1292574 * 2 ^ 59
def prefixEnd_1292574 : Nat := 4983230072969 + 3 ^ 40 * 1292574 * 2
def baseEnd_1292574 : Nat := 294982997113213791991363

theorem tailTrace_1292574 : CollatzResearch.WordTrace tailWord_1292574 prefixEnd_1292574 294982997113213791991363 := by
  unfold tailWord_1292574
  simp only [CollatzResearch.WordTrace]
  refine ⟨5893005852404078363647597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31429364546155084606120517 5893005852404078363647597)
  ·
    refine ⟨2209877194651529386367849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5893005852404078363647597 2209877194651529386367849)
    ·
      refine ⟨1657407895988647039775887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2209877194651529386367849 1657407895988647039775887)
      ·
        refine ⟨2486111843982970559663831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1657407895988647039775887 2486111843982970559663831)
        ·
          refine ⟨3729167765974455839495747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2486111843982970559663831 3729167765974455839495747)
          ·
            refine ⟨5593751648961683759243621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3729167765974455839495747 5593751648961683759243621)
            ·
              refine ⟨1048828434180315704858179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5593751648961683759243621 1048828434180315704858179)
              ·
                refine ⟨1573242651270473557287269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1048828434180315704858179 1573242651270473557287269)
                ·
                  refine ⟨294982997113213791991363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1573242651270473557287269 294982997113213791991363)
                  ·
                    rfl

theorem cell21_1292574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_1292574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1292574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1292574 prefixEnd_1292574 := by exact prefixLift 1292574
  have htrace : WordTrace (prefixWord ++ tailWord_1292574) baseStart_1292574 baseEnd_1292574 := by
    simpa [prefixWord, tailWord_1292574, baseEnd_1292574] using wordTrace_append hprefix tailTrace_1292574
  have hstable : (prefixWord ++ tailWord_1292574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292574).length < 2 ^ (prefixWord ++ tailWord_1292574).sum := by decide
  have hdescent : baseEnd_1292574 < baseStart_1292574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292644 : List Nat := [2, 3, 1, 1, 3, 1, 3, 2, 5]
def baseStart_1292644 : Nat := 118140960795 + 1292644 * 2 ^ 59
def prefixEnd_1292644 : Nat := 4983230072969 + 3 ^ 40 * 1292644 * 2
def baseEnd_1292644 : Nat := 294998972066909225824553

theorem tailTrace_1292644 : CollatzResearch.WordTrace tailWord_1292644 prefixEnd_1292644 294998972066909225824553 := by
  unfold tailWord_1292644
  simp only [CollatzResearch.WordTrace]
  refine ⟨23573299964489514432114493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31431066619319352576152657 23573299964489514432114493)
  ·
    refine ⟨8839987486683567912042935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23573299964489514432114493 8839987486683567912042935)
    ·
      refine ⟨13259981230025351868064403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8839987486683567912042935 13259981230025351868064403)
      ·
        refine ⟨19889971845038027802096605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13259981230025351868064403 19889971845038027802096605)
        ·
          refine ⟨7458739441889260425786227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19889971845038027802096605 7458739441889260425786227)
          ·
            refine ⟨11188109162833890638679341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7458739441889260425786227 11188109162833890638679341)
            ·
              refine ⟨4195540936062708989504753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11188109162833890638679341 4195540936062708989504753)
              ·
                refine ⟨3146655702047031742128565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4195540936062708989504753 3146655702047031742128565)
                ·
                  refine ⟨294998972066909225824553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3146655702047031742128565 294998972066909225824553)
                  ·
                    rfl

theorem cell21_1292644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_1292644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1292644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1292644 prefixEnd_1292644 := by exact prefixLift 1292644
  have htrace : WordTrace (prefixWord ++ tailWord_1292644) baseStart_1292644 baseEnd_1292644 := by
    simpa [prefixWord, tailWord_1292644, baseEnd_1292644] using wordTrace_append hprefix tailTrace_1292644
  have hstable : (prefixWord ++ tailWord_1292644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292644).length < 2 ^ (prefixWord ++ tailWord_1292644).sum := by decide
  have hdescent : baseEnd_1292644 < baseStart_1292644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292675 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 6]
def baseStart_1292675 : Nat := 118140960795 + 1292675 * 2 ^ 59
def prefixEnd_1292675 : Nat := 4983230072969 + 3 ^ 40 * 1292675 * 2
def baseEnd_1292675 : Nat := 295006046689260060807823

theorem tailTrace_1292675 : CollatzResearch.WordTrace tailWord_1292675 prefixEnd_1292675 295006046689260060807823 := by
  unfold tailWord_1292675
  simp only [CollatzResearch.WordTrace]
  refine ⟨47147730591866721158607479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31431820394577814105738319 47147730591866721158607479)
  ·
    refine ⟨70721595887800081737911219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47147730591866721158607479 70721595887800081737911219)
    ·
      refine ⟨106082393831700122606866829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70721595887800081737911219 106082393831700122606866829)
      ·
        refine ⟨39780897686887545977575061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106082393831700122606866829 39780897686887545977575061)
        ·
          refine ⟨1864729579072853717698831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39780897686887545977575061 1864729579072853717698831)
          ·
            refine ⟨2797094368609280576548247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1864729579072853717698831 2797094368609280576548247)
            ·
              refine ⟨4195641552913920864822371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2797094368609280576548247 4195641552913920864822371)
              ·
                refine ⟨6293462329370881297233557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4195641552913920864822371 6293462329370881297233557)
                ·
                  refine ⟨295006046689260060807823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6293462329370881297233557 295006046689260060807823)
                  ·
                    rfl

theorem cell21_1292675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 6].length) (baseStart_1292675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1292675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1292675 prefixEnd_1292675 := by exact prefixLift 1292675
  have htrace : WordTrace (prefixWord ++ tailWord_1292675) baseStart_1292675 baseEnd_1292675 := by
    simpa [prefixWord, tailWord_1292675, baseEnd_1292675] using wordTrace_append hprefix tailTrace_1292675
  have hstable : (prefixWord ++ tailWord_1292675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292675).length < 2 ^ (prefixWord ++ tailWord_1292675).sum := by decide
  have hdescent : baseEnd_1292675 < baseStart_1292675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292765 : List Nat := [1, 4, 3, 1, 1, 1, 1, 9]
def baseStart_1292765 : Nat := 118140960795 + 1292765 * 2 ^ 59
def prefixEnd_1292765 : Nat := 4983230072969 + 3 ^ 40 * 1292765 * 2
def baseEnd_1292765 : Nat := 98342195305146634769213

theorem tailTrace_1292765 : CollatzResearch.WordTrace tailWord_1292765 prefixEnd_1292765 98342195305146634769213 := by
  unfold tailWord_1292765
  simp only [CollatzResearch.WordTrace]
  refine ⟨47151013161540666529383749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31434008774360444352922499 47151013161540666529383749)
  ·
    refine ⟨8840814967788874974259453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47151013161540666529383749 8840814967788874974259453)
    ·
      refine ⟨3315305612920828115347295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8840814967788874974259453 3315305612920828115347295)
      ·
        refine ⟨4972958419381242173020943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3315305612920828115347295 4972958419381242173020943)
        ·
          refine ⟨7459437629071863259531415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4972958419381242173020943 7459437629071863259531415)
          ·
            refine ⟨11189156443607794889297123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7459437629071863259531415 11189156443607794889297123)
            ·
              refine ⟨16783734665411692333945685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11189156443607794889297123 16783734665411692333945685)
              ·
                refine ⟨98342195305146634769213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16783734665411692333945685 98342195305146634769213)
                ·
                  rfl

theorem cell21_1292765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 9].length) (baseStart_1292765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1292765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1292765 prefixEnd_1292765 := by exact prefixLift 1292765
  have htrace : WordTrace (prefixWord ++ tailWord_1292765) baseStart_1292765 baseEnd_1292765 := by
    simpa [prefixWord, tailWord_1292765, baseEnd_1292765] using wordTrace_append hprefix tailTrace_1292765
  have hstable : (prefixWord ++ tailWord_1292765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292765).length < 2 ^ (prefixWord ++ tailWord_1292765).sum := by decide
  have hdescent : baseEnd_1292765 < baseStart_1292765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292906 : List Nat := [3, 1, 3, 2, 1, 1, 5, 2, 3]
def baseStart_1292906 : Nat := 118140960795 + 1292906 * 2 ^ 59
def prefixEnd_1292906 : Nat := 4983230072969 + 3 ^ 40 * 1292906 * 2
def baseEnd_1292906 : Nat := 295058764036454992457351

theorem tailTrace_1292906 : CollatzResearch.WordTrace tailWord_1292906 prefixEnd_1292906 295058764036454992457351 := by
  unfold tailWord_1292906
  simp only [CollatzResearch.WordTrace]
  refine ⟨11789038963507461902566643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31437437236019898406844381 11789038963507461902566643)
  ·
    refine ⟨17683558445261192853849965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11789038963507461902566643 17683558445261192853849965)
    ·
      refine ⟨6631334416972947320193737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17683558445261192853849965 6631334416972947320193737)
      ·
        refine ⟨4973500812729710490145303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6631334416972947320193737 4973500812729710490145303)
        ·
          refine ⟨7460251219094565735217955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4973500812729710490145303 7460251219094565735217955)
          ·
            refine ⟨11190376828641848602826933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7460251219094565735217955 11190376828641848602826933)
            ·
              refine ⟨1049097827685173306515025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11190376828641848602826933 1049097827685173306515025)
              ·
                refine ⟨786823370763879979886269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1049097827685173306515025 786823370763879979886269)
                ·
                  refine ⟨295058764036454992457351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 786823370763879979886269 295058764036454992457351)
                  ·
                    rfl

theorem cell21_1292906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 3].length) (baseStart_1292906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1292906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1292906 prefixEnd_1292906 := by exact prefixLift 1292906
  have htrace : WordTrace (prefixWord ++ tailWord_1292906) baseStart_1292906 baseEnd_1292906 := by
    simpa [prefixWord, tailWord_1292906, baseEnd_1292906] using wordTrace_append hprefix tailTrace_1292906
  have hstable : (prefixWord ++ tailWord_1292906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292906).length < 2 ^ (prefixWord ++ tailWord_1292906).sum := by decide
  have hdescent : baseEnd_1292906 < baseStart_1292906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292931 : List Nat := [1, 1, 1, 3, 3, 1, 2, 4, 5]
def baseStart_1292931 : Nat := 118140960795 + 1292931 * 2 ^ 59
def prefixEnd_1292931 : Nat := 4983230072969 + 3 ^ 40 * 1292931 * 2
def baseEnd_1292931 : Nat := 295064469377060504540633

theorem tailTrace_1292931 : CollatzResearch.WordTrace tailWord_1292931 prefixEnd_1292931 295064469377060504540633 := by
  unfold tailWord_1292931
  simp only [CollatzResearch.WordTrace]
  refine ⟨47157067678939276879926647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31438045119292851253284431 47157067678939276879926647)
  ·
    refine ⟨70735601518408915319889971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47157067678939276879926647 70735601518408915319889971)
    ·
      refine ⟨106103402277613372979834957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70735601518408915319889971 106103402277613372979834957)
      ·
        refine ⟨39788775854105014867438109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106103402277613372979834957 39788775854105014867438109)
        ·
          refine ⟨14920790945289380575289291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39788775854105014867438109 14920790945289380575289291)
          ·
            refine ⟨22381186417934070862933937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14920790945289380575289291 22381186417934070862933937)
            ·
              refine ⟨16785889813450553147200453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22381186417934070862933937 16785889813450553147200453)
              ·
                refine ⟨3147354340021978715100085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16785889813450553147200453 3147354340021978715100085)
                ·
                  refine ⟨295064469377060504540633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3147354340021978715100085 295064469377060504540633)
                  ·
                    rfl

theorem cell21_1292931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 5].length) (baseStart_1292931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1292931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1292931 prefixEnd_1292931 := by exact prefixLift 1292931
  have htrace : WordTrace (prefixWord ++ tailWord_1292931) baseStart_1292931 baseEnd_1292931 := by
    simpa [prefixWord, tailWord_1292931, baseEnd_1292931] using wordTrace_append hprefix tailTrace_1292931
  have hstable : (prefixWord ++ tailWord_1292931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292931).length < 2 ^ (prefixWord ++ tailWord_1292931).sum := by decide
  have hdescent : baseEnd_1292931 < baseStart_1292931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1292982 : List Nat := [5, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_1292982 : Nat := 118140960795 + 1292982 * 2 ^ 59
def prefixEnd_1292982 : Nat := 4983230072969 + 3 ^ 40 * 1292982 * 2
def baseEnd_1292982 : Nat := 295076108271895749190529

theorem tailTrace_1292982 : CollatzResearch.WordTrace tailWord_1292982 prefixEnd_1292982 295076108271895749190529 := by
  unfold tailWord_1292982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2947432987609657036877075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31439285201169675060022133 2947432987609657036877075)
  ·
    refine ⟨4421149481414485555315613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2947432987609657036877075 4421149481414485555315613)
    ·
      refine ⟨1657931055530432083243355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4421149481414485555315613 1657931055530432083243355)
      ·
        refine ⟨2486896583295648124865033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1657931055530432083243355 2486896583295648124865033)
        ·
          refine ⟨1865172437471736093648775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2486896583295648124865033 1865172437471736093648775)
          ·
            refine ⟨2797758656207604140473163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1865172437471736093648775 2797758656207604140473163)
            ·
              refine ⟨4196637984311406210709745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2797758656207604140473163 4196637984311406210709745)
              ·
                refine ⟨3147478488233554658032309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4196637984311406210709745 3147478488233554658032309)
                ·
                  refine ⟨295076108271895749190529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3147478488233554658032309 295076108271895749190529)
                  ·
                    rfl

theorem cell21_1292982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_1292982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1292982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1292982 prefixEnd_1292982 := by exact prefixLift 1292982
  have htrace : WordTrace (prefixWord ++ tailWord_1292982) baseStart_1292982 baseEnd_1292982 := by
    simpa [prefixWord, tailWord_1292982, baseEnd_1292982] using wordTrace_append hprefix tailTrace_1292982
  have hstable : (prefixWord ++ tailWord_1292982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1292982).length < 2 ^ (prefixWord ++ tailWord_1292982).sum := by decide
  have hdescent : baseEnd_1292982 < baseStart_1292982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1292982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293013 : List Nat := [1, 3, 2, 5, 1, 2, 1, 2, 4]
def baseStart_1293013 : Nat := 118140960795 + 1293013 * 2 ^ 59
def prefixEnd_1293013 : Nat := 4983230072969 + 3 ^ 40 * 1293013 * 2
def baseEnd_1293013 : Nat := 295083182894246584173799

theorem tailTrace_1293013 : CollatzResearch.WordTrace tailWord_1293013 prefixEnd_1293013 295083182894246584173799 := by
  unfold tailWord_1293013
  simp only [CollatzResearch.WordTrace]
  refine ⟨47160058464642204884411693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31440038976428136589607795 47160058464642204884411693)
  ·
    refine ⟨17685021924240826831654385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47160058464642204884411693 17685021924240826831654385)
    ·
      refine ⟨13263766443180620123740789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17685021924240826831654385 13263766443180620123740789)
      ·
        refine ⟨1243478104048183136600699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13263766443180620123740789 1243478104048183136600699)
        ·
          refine ⟨1865217156072274704901049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1243478104048183136600699 1865217156072274704901049)
          ·
            refine ⟨1398912867054206028675787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1865217156072274704901049 1398912867054206028675787)
            ·
              refine ⟨2098369300581309043013681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1398912867054206028675787 2098369300581309043013681)
              ·
                refine ⟨1573776975435981782260261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2098369300581309043013681 1573776975435981782260261)
                ·
                  refine ⟨295083182894246584173799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1573776975435981782260261 295083182894246584173799)
                  ·
                    rfl

theorem cell21_1293013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_1293013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1293013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1293013 prefixEnd_1293013 := by exact prefixLift 1293013
  have htrace : WordTrace (prefixWord ++ tailWord_1293013) baseStart_1293013 baseEnd_1293013 := by
    simpa [prefixWord, tailWord_1293013, baseEnd_1293013] using wordTrace_append hprefix tailTrace_1293013
  have hstable : (prefixWord ++ tailWord_1293013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293013).length < 2 ^ (prefixWord ++ tailWord_1293013).sum := by decide
  have hdescent : baseEnd_1293013 < baseStart_1293013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293058 : List Nat := [3, 4, 1, 1, 1, 2, 3, 3, 3]
def baseStart_1293058 : Nat := 118140960795 + 1293058 * 2 ^ 59
def prefixEnd_1293058 : Nat := 4983230072969 + 3 ^ 40 * 1293058 * 2
def baseEnd_1293058 : Nat := 295093452507336505923707

theorem tailTrace_1293058 : CollatzResearch.WordTrace tailWord_1293058 prefixEnd_1293058 295093452507336505923707 := by
  unfold tailWord_1293058
  simp only [CollatzResearch.WordTrace]
  refine ⟨11790424937369794392449957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31441133166319451713199885 11790424937369794392449957)
  ·
    refine ⟨2210704675756836448584367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11790424937369794392449957 2210704675756836448584367)
    ·
      refine ⟨3316057013635254672876551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2210704675756836448584367 3316057013635254672876551)
      ·
        refine ⟨4974085520452882009314827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3316057013635254672876551 4974085520452882009314827)
        ·
          refine ⟨7461128280679323013972241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4974085520452882009314827 7461128280679323013972241)
          ·
            refine ⟨5595846210509492260479181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7461128280679323013972241 5595846210509492260479181)
            ·
              refine ⟨2098442328941059597679693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5595846210509492260479181 2098442328941059597679693)
              ·
                refine ⟨786915873352897349129885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2098442328941059597679693 786915873352897349129885)
                ·
                  refine ⟨295093452507336505923707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 786915873352897349129885 295093452507336505923707)
                  ·
                    rfl

theorem cell21_1293058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_1293058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1293058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1293058 prefixEnd_1293058 := by exact prefixLift 1293058
  have htrace : WordTrace (prefixWord ++ tailWord_1293058) baseStart_1293058 baseEnd_1293058 := by
    simpa [prefixWord, tailWord_1293058, baseEnd_1293058] using wordTrace_append hprefix tailTrace_1293058
  have hstable : (prefixWord ++ tailWord_1293058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293058).length < 2 ^ (prefixWord ++ tailWord_1293058).sum := by decide
  have hdescent : baseEnd_1293058 < baseStart_1293058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293145 : List Nat := [1, 2, 1, 2, 2, 6, 1, 6]
def baseStart_1293145 : Nat := 118140960795 + 1293145 * 2 ^ 59
def prefixEnd_1293145 : Nat := 4983230072969 + 3 ^ 40 * 1293145 * 2
def baseEnd_1293145 : Nat := 98371102364214562657843

theorem tailTrace_1293145 : CollatzResearch.WordTrace tailWord_1293145 prefixEnd_1293145 98371102364214562657843 := by
  unfold tailWord_1293145
  simp only [CollatzResearch.WordTrace]
  refine ⟨47164872900163991428216889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31443248600109327618811259 47164872900163991428216889)
  ·
    refine ⟨35373654675122993571162667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47164872900163991428216889 35373654675122993571162667)
    ·
      refine ⟨53060482012684490356744001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35373654675122993571162667 53060482012684490356744001)
      ·
        refine ⟨39795361509513367767558001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53060482012684490356744001 39795361509513367767558001)
        ·
          refine ⟨29846521132135025825668501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39795361509513367767558001 29846521132135025825668501)
          ·
            refine ⟨1399055678068829335578211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29846521132135025825668501 1399055678068829335578211)
            ·
              refine ⟨2098583517103244003367317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1399055678068829335578211 2098583517103244003367317)
              ·
                refine ⟨98371102364214562657843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2098583517103244003367317 98371102364214562657843)
                ·
                  rfl

theorem cell21_1293145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 6].length) (baseStart_1293145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1293145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1293145 prefixEnd_1293145 := by exact prefixLift 1293145
  have htrace : WordTrace (prefixWord ++ tailWord_1293145) baseStart_1293145 baseEnd_1293145 := by
    simpa [prefixWord, tailWord_1293145, baseEnd_1293145] using wordTrace_append hprefix tailTrace_1293145
  have hstable : (prefixWord ++ tailWord_1293145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293145).length < 2 ^ (prefixWord ++ tailWord_1293145).sum := by decide
  have hdescent : baseEnd_1293145 < baseStart_1293145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293159 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 7]
def baseStart_1293159 : Nat := 118140960795 + 1293159 * 2 ^ 59
def prefixEnd_1293159 : Nat := 4983230072969 + 3 ^ 40 * 1293159 * 2
def baseEnd_1293159 : Nat := 295116502083382774740167

theorem tailTrace_1293159 : CollatzResearch.WordTrace tailWord_1293159 prefixEnd_1293159 295116502083382774740167 := by
  unfold tailWord_1293159
  simp only [CollatzResearch.WordTrace]
  refine ⟨47165383522113271819226531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31443589014742181212817687 47165383522113271819226531)
  ·
    refine ⟨70748075283169907728839797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47165383522113271819226531 70748075283169907728839797)
    ·
      refine ⟨6632632057797178849578731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70748075283169907728839797 6632632057797178849578731)
      ·
        refine ⟨9948948086695768274368097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6632632057797178849578731 9948948086695768274368097)
        ·
          refine ⟨7461711065021826205776073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9948948086695768274368097 7461711065021826205776073)
          ·
            refine ⟨5596283298766369654332055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7461711065021826205776073 5596283298766369654332055)
            ·
              refine ⟨8394424948149554481498083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5596283298766369654332055 8394424948149554481498083)
              ·
                refine ⟨12591637422224331722247125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8394424948149554481498083 12591637422224331722247125)
                ·
                  refine ⟨295116502083382774740167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12591637422224331722247125 295116502083382774740167)
                  ·
                    rfl

theorem cell21_1293159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 7].length) (baseStart_1293159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1293159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1293159 prefixEnd_1293159 := by exact prefixLift 1293159
  have htrace : WordTrace (prefixWord ++ tailWord_1293159) baseStart_1293159 baseEnd_1293159 := by
    simpa [prefixWord, tailWord_1293159, baseEnd_1293159] using wordTrace_append hprefix tailTrace_1293159
  have hstable : (prefixWord ++ tailWord_1293159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293159).length < 2 ^ (prefixWord ++ tailWord_1293159).sum := by decide
  have hdescent : baseEnd_1293159 < baseStart_1293159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293182 : List Nat := [4, 2, 3, 1, 3, 1, 1, 2, 4]
def baseStart_1293182 : Nat := 118140960795 + 1293182 * 2 ^ 59
def prefixEnd_1293182 : Nat := 4983230072969 + 3 ^ 40 * 1293182 * 2
def baseEnd_1293182 : Nat := 295121750996739845856787

theorem tailTrace_1293182 : CollatzResearch.WordTrace tailWord_1293182 prefixEnd_1293182 295121750996739845856787 := by
  unfold tailWord_1293182
  simp only [CollatzResearch.WordTrace]
  refine ⟨5895777800128743343414225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31444148267353297831542533 5895777800128743343414225)
  ·
    refine ⟨4421833350096557507560669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5895777800128743343414225 4421833350096557507560669)
    ·
      refine ⟨1658187506286209065335251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4421833350096557507560669 1658187506286209065335251)
      ·
        refine ⟨2487281259429313598002877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1658187506286209065335251 2487281259429313598002877)
        ·
          refine ⟨932730472285992599251079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2487281259429313598002877 932730472285992599251079)
          ·
            refine ⟨1399095708428988898876619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 932730472285992599251079 1399095708428988898876619)
            ·
              refine ⟨2098643562643483348314929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1399095708428988898876619 2098643562643483348314929)
              ·
                refine ⟨1573982671982612511236197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2098643562643483348314929 1573982671982612511236197)
                ·
                  refine ⟨295121750996739845856787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1573982671982612511236197 295121750996739845856787)
                  ·
                    rfl

theorem cell21_1293182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_1293182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1293182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1293182 prefixEnd_1293182 := by exact prefixLift 1293182
  have htrace : WordTrace (prefixWord ++ tailWord_1293182) baseStart_1293182 baseEnd_1293182 := by
    simpa [prefixWord, tailWord_1293182, baseEnd_1293182] using wordTrace_append hprefix tailTrace_1293182
  have hstable : (prefixWord ++ tailWord_1293182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293182).length < 2 ^ (prefixWord ++ tailWord_1293182).sum := by decide
  have hdescent : baseEnd_1293182 < baseStart_1293182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293207 : List Nat := [1, 1, 3, 3, 1, 2, 5, 1, 4]
def baseStart_1293207 : Nat := 118140960795 + 1293207 * 2 ^ 59
def prefixEnd_1293207 : Nat := 4983230072969 + 3 ^ 40 * 1293207 * 2
def baseEnd_1293207 : Nat := 295127456337345357940069

theorem tailTrace_1293207 : CollatzResearch.WordTrace tailWord_1293207 prefixEnd_1293207 295127456337345357940069 := by
  unfold tailWord_1293207
  simp only [CollatzResearch.WordTrace]
  refine ⟨47167134225939376016973875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31444756150626250677982583 47167134225939376016973875)
  ·
    refine ⟨70750701338909064025460813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47167134225939376016973875 70750701338909064025460813)
    ·
      refine ⟨26531513002090899009547805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70750701338909064025460813 26531513002090899009547805)
      ·
        refine ⟨9949317375784087128580427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26531513002090899009547805 9949317375784087128580427)
        ·
          refine ⟨14923976063676130692870641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9949317375784087128580427 14923976063676130692870641)
          ·
            refine ⟨11192982047757098019652981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14923976063676130692870641 11192982047757098019652981)
            ·
              refine ⟨1049342066977227939342467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11192982047757098019652981 1049342066977227939342467)
              ·
                refine ⟨1574013100465841909013701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1049342066977227939342467 1574013100465841909013701)
                ·
                  refine ⟨295127456337345357940069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1574013100465841909013701 295127456337345357940069)
                  ·
                    rfl

theorem cell21_1293207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 4].length) (baseStart_1293207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1293207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1293207 prefixEnd_1293207 := by exact prefixLift 1293207
  have htrace : WordTrace (prefixWord ++ tailWord_1293207) baseStart_1293207 baseEnd_1293207 := by
    simpa [prefixWord, tailWord_1293207, baseEnd_1293207] using wordTrace_append hprefix tailTrace_1293207
  have hstable : (prefixWord ++ tailWord_1293207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293207).length < 2 ^ (prefixWord ++ tailWord_1293207).sum := by decide
  have hdescent : baseEnd_1293207 < baseStart_1293207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293345 : List Nat := [1, 2, 3, 2, 3, 2, 2, 3, 3]
def baseStart_1293345 : Nat := 118140960795 + 1293345 * 2 ^ 59
def prefixEnd_1293345 : Nat := 4983230072969 + 3 ^ 40 * 1293345 * 2
def baseEnd_1293345 : Nat := 295158949817487784639787

theorem tailTrace_1293345 : CollatzResearch.WordTrace tailWord_1293345 prefixEnd_1293345 295158949817487784639787 := by
  unfold tailWord_1293345
  simp only [CollatzResearch.WordTrace]
  refine ⟨47172167499439425585497489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31448111666292950390331659 47172167499439425585497489)
  ·
    refine ⟨35379125624579569189123117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47172167499439425585497489 35379125624579569189123117)
    ·
      refine ⟨13267172109217338445921169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35379125624579569189123117 13267172109217338445921169)
      ·
        refine ⟨9950379081913003834440877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13267172109217338445921169 9950379081913003834440877)
        ·
          refine ⟨3731392155717376437915329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9950379081913003834440877 3731392155717376437915329)
          ·
            refine ⟨2798544116788032328436497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3731392155717376437915329 2798544116788032328436497)
            ·
              refine ⟨2098908087591024246327373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2798544116788032328436497 2098908087591024246327373)
              ·
                refine ⟨787090532846634092372765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2098908087591024246327373 787090532846634092372765)
                ·
                  refine ⟨295158949817487784639787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 787090532846634092372765 295158949817487784639787)
                  ·
                    rfl

theorem cell21_1293345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 3].length) (baseStart_1293345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1293345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1293345 prefixEnd_1293345 := by exact prefixLift 1293345
  have htrace : WordTrace (prefixWord ++ tailWord_1293345) baseStart_1293345 baseEnd_1293345 := by
    simpa [prefixWord, tailWord_1293345, baseEnd_1293345] using wordTrace_append hprefix tailTrace_1293345
  have hstable : (prefixWord ++ tailWord_1293345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293345).length < 2 ^ (prefixWord ++ tailWord_1293345).sum := by decide
  have hdescent : baseEnd_1293345 < baseStart_1293345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293418 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 6]
def baseStart_1293418 : Nat := 118140960795 + 1293418 * 2 ^ 59
def prefixEnd_1293418 : Nat := 4983230072969 + 3 ^ 40 * 1293418 * 2
def baseEnd_1293418 : Nat := 295175609412055879922971

theorem tailTrace_1293418 : CollatzResearch.WordTrace tailWord_1293418 prefixEnd_1293418 295175609412055879922971 := by
  unfold tailWord_1293418
  simp only [CollatzResearch.WordTrace]
  refine ⟨11793707507043739763226227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31449886685449972701936605 11793707507043739763226227)
  ·
    refine ⟨17690561260565609644839341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11793707507043739763226227 17690561260565609644839341)
    ·
      refine ⟨6633960472712103616814753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17690561260565609644839341 6633960472712103616814753)
      ·
        refine ⟨4975470354534077712611065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6633960472712103616814753 4975470354534077712611065)
        ·
          refine ⟨3731602765900558284458299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4975470354534077712611065 3731602765900558284458299)
          ·
            refine ⟨5597404148850837426687449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3731602765900558284458299 5597404148850837426687449)
            ·
              refine ⟨4198053111638128070015587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5597404148850837426687449 4198053111638128070015587)
              ·
                refine ⟨6297079667457192105023381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4198053111638128070015587 6297079667457192105023381)
                ·
                  refine ⟨295175609412055879922971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6297079667457192105023381 295175609412055879922971)
                  ·
                    rfl

theorem cell21_1293418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_1293418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1293418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1293418 prefixEnd_1293418 := by exact prefixLift 1293418
  have htrace : WordTrace (prefixWord ++ tailWord_1293418) baseStart_1293418 baseEnd_1293418 := by
    simpa [prefixWord, tailWord_1293418, baseEnd_1293418] using wordTrace_append hprefix tailTrace_1293418
  have hstable : (prefixWord ++ tailWord_1293418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293418).length < 2 ^ (prefixWord ++ tailWord_1293418).sum := by decide
  have hdescent : baseEnd_1293418 < baseStart_1293418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293528 : List Nat := [2, 1, 2, 2, 6, 1, 1, 2, 4]
def baseStart_1293528 : Nat := 118140960795 + 1293528 * 2 ^ 59
def prefixEnd_1293528 : Nat := 4983230072969 + 3 ^ 40 * 1293528 * 2
def baseEnd_1293528 : Nat := 295200712910720133089413

theorem tailTrace_1293528 : CollatzResearch.WordTrace tailWord_1293528 prefixEnd_1293528 295200712910720133089413 := by
  unfold tailWord_1293528
  simp only [CollatzResearch.WordTrace]
  refine ⟨23589421028888223919704619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31452561371850965226272825 23589421028888223919704619)
  ·
    refine ⟨35384131543332335879556929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23589421028888223919704619 35384131543332335879556929)
    ·
      refine ⟨26538098657499251909667697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35384131543332335879556929 26538098657499251909667697)
      ·
        refine ⟨19903573993124438932250773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26538098657499251909667697 19903573993124438932250773)
        ·
          refine ⟨932980030927708074949255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19903573993124438932250773 932980030927708074949255)
          ·
            refine ⟨1399470046391562112423883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 932980030927708074949255 1399470046391562112423883)
            ·
              refine ⟨2099205069587343168635825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1399470046391562112423883 2099205069587343168635825)
              ·
                refine ⟨1574403802190507376476869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2099205069587343168635825 1574403802190507376476869)
                ·
                  refine ⟨295200712910720133089413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1574403802190507376476869 295200712910720133089413)
                  ·
                    rfl

theorem cell21_1293528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 4].length) (baseStart_1293528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1293528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1293528 prefixEnd_1293528 := by exact prefixLift 1293528
  have htrace : WordTrace (prefixWord ++ tailWord_1293528) baseStart_1293528 baseEnd_1293528 := by
    simpa [prefixWord, tailWord_1293528, baseEnd_1293528] using wordTrace_append hprefix tailTrace_1293528
  have hstable : (prefixWord ++ tailWord_1293528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293528).length < 2 ^ (prefixWord ++ tailWord_1293528).sum := by decide
  have hdescent : baseEnd_1293528 < baseStart_1293528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293646 : List Nat := [4, 1, 1, 1, 1, 1, 6, 2, 4]
def baseStart_1293646 : Nat := 118140960795 + 1293646 * 2 ^ 59
def prefixEnd_1293646 : Nat := 4983230072969 + 3 ^ 40 * 1293646 * 2
def baseEnd_1293646 : Nat := 295227642118378150122505

theorem tailTrace_1293646 : CollatzResearch.WordTrace tailWord_1293646 prefixEnd_1293646 295227642118378150122505 := by
  unfold tailWord_1293646
  simp only [CollatzResearch.WordTrace]
  refine ⟨5897893233918619249025599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31455430580899302661469861 5897893233918619249025599)
  ·
    refine ⟨8846839850877928873538399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5897893233918619249025599 8846839850877928873538399)
    ·
      refine ⟨13270259776316893310307599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8846839850877928873538399 13270259776316893310307599)
      ·
        refine ⟨19905389664475339965461399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13270259776316893310307599 19905389664475339965461399)
        ·
          refine ⟨29858084496713009948192099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19905389664475339965461399 29858084496713009948192099)
          ·
            refine ⟨44787126745069514922288149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29858084496713009948192099 44787126745069514922288149)
            ·
              refine ⟨2099396566175133511982257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44787126745069514922288149 2099396566175133511982257)
              ·
                refine ⟨1574547424631350133986693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2099396566175133511982257 1574547424631350133986693)
                ·
                  refine ⟨295227642118378150122505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1574547424631350133986693 295227642118378150122505)
                  ·
                    rfl

theorem cell21_1293646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_1293646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1293646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1293646 prefixEnd_1293646 := by exact prefixLift 1293646
  have htrace : WordTrace (prefixWord ++ tailWord_1293646) baseStart_1293646 baseEnd_1293646 := by
    simpa [prefixWord, tailWord_1293646, baseEnd_1293646] using wordTrace_append hprefix tailTrace_1293646
  have hstable : (prefixWord ++ tailWord_1293646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293646).length < 2 ^ (prefixWord ++ tailWord_1293646).sum := by decide
  have hdescent : baseEnd_1293646 < baseStart_1293646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293677 : List Nat := [1, 5, 1, 1, 1, 4, 3, 5]
def baseStart_1293677 : Nat := 118140960795 + 1293677 * 2 ^ 59
def prefixEnd_1293677 : Nat := 4983230072969 + 3 ^ 40 * 1293677 * 2
def baseEnd_1293677 : Nat := 98411572246909661701925

theorem tailTrace_1293677 : CollatzResearch.WordTrace tailWord_1293677 prefixEnd_1293677 98411572246909661701925 := by
  unfold tailWord_1293677
  simp only [CollatzResearch.WordTrace]
  refine ⟨47184276534236646286583285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31456184356157764191055523 47184276534236646286583285)
  ·
    refine ⟨4423525925084685589367183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47184276534236646286583285 4423525925084685589367183)
    ·
      refine ⟨6635288887627028384050775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4423525925084685589367183 6635288887627028384050775)
      ·
        refine ⟨9952933331440542576076163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6635288887627028384050775 9952933331440542576076163)
        ·
          refine ⟨14929399997160813864114245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9952933331440542576076163 14929399997160813864114245)
          ·
            refine ⟨2799262499467652599521421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14929399997160813864114245 2799262499467652599521421)
            ·
              refine ⟨1049723437300369724820533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2799262499467652599521421 1049723437300369724820533)
              ·
                refine ⟨98411572246909661701925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1049723437300369724820533 98411572246909661701925)
                ·
                  rfl

theorem cell21_1293677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 5].length) (baseStart_1293677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1293677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1293677 prefixEnd_1293677 := by exact prefixLift 1293677
  have htrace : WordTrace (prefixWord ++ tailWord_1293677) baseStart_1293677 baseEnd_1293677 := by
    simpa [prefixWord, tailWord_1293677, baseEnd_1293677] using wordTrace_append hprefix tailTrace_1293677
  have hstable : (prefixWord ++ tailWord_1293677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293677).length < 2 ^ (prefixWord ++ tailWord_1293677).sum := by decide
  have hdescent : baseEnd_1293677 < baseStart_1293677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293694 : List Nat := [4, 2, 3, 2, 1, 1, 8]
def baseStart_1293694 : Nat := 118140960795 + 1293694 * 2 ^ 59
def prefixEnd_1293694 : Nat := 4983230072969 + 3 ^ 40 * 1293694 * 2
def baseEnd_1293694 : Nat := 32804288485815637035823

theorem tailTrace_1293694 : CollatzResearch.WordTrace tailWord_1293694 prefixEnd_1293694 32804288485815637035823 := by
  unfold tailWord_1293694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5898112071896882273744017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31456597716783372126634757 5898112071896882273744017)
  ·
    refine ⟨4423584053922661705308013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5898112071896882273744017 4423584053922661705308013)
    ·
      refine ⟨1658844020220998139490505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4423584053922661705308013 1658844020220998139490505)
      ·
        refine ⟨1244133015165748604617879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1658844020220998139490505 1244133015165748604617879)
        ·
          refine ⟨1866199522748622906926819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1244133015165748604617879 1866199522748622906926819)
          ·
            refine ⟨2799299284122934360390229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1866199522748622906926819 2799299284122934360390229)
            ·
              refine ⟨32804288485815637035823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2799299284122934360390229 32804288485815637035823)
              ·
                rfl

theorem cell21_1293694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 8].length) (baseStart_1293694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1293694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1293694 prefixEnd_1293694 := by exact prefixLift 1293694
  have htrace : WordTrace (prefixWord ++ tailWord_1293694) baseStart_1293694 baseEnd_1293694 := by
    simpa [prefixWord, tailWord_1293694, baseEnd_1293694] using wordTrace_append hprefix tailTrace_1293694
  have hstable : (prefixWord ++ tailWord_1293694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293694).length < 2 ^ (prefixWord ++ tailWord_1293694).sum := by decide
  have hdescent : baseEnd_1293694 < baseStart_1293694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293719 : List Nat := [1, 1, 3, 3, 1, 1, 1, 10]
def baseStart_1293719 : Nat := 118140960795 + 1293719 * 2 ^ 59
def prefixEnd_1293719 : Nat := 4983230072969 + 3 ^ 40 * 1293719 * 2
def baseEnd_1293719 : Nat := 98414767237648748468563

theorem tailTrace_1293719 : CollatzResearch.WordTrace tailWord_1293719 prefixEnd_1293719 98414767237648748468563 := by
  unfold tailWord_1293719
  simp only [CollatzResearch.WordTrace]
  refine ⟨47185808400084487459612211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31457205600056324973074807 47185808400084487459612211)
  ·
    refine ⟨70778712600126731189418317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47185808400084487459612211 70778712600126731189418317)
    ·
      refine ⟨26542017225047524196031869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70778712600126731189418317 26542017225047524196031869)
      ·
        refine ⟨9953256459392821573511951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26542017225047524196031869 9953256459392821573511951)
        ·
          refine ⟨14929884689089232360267927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9953256459392821573511951 14929884689089232360267927)
          ·
            refine ⟨22394827033633848540401891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14929884689089232360267927 22394827033633848540401891)
            ·
              refine ⟨33592240550450772810602837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22394827033633848540401891 33592240550450772810602837)
              ·
                refine ⟨98414767237648748468563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33592240550450772810602837 98414767237648748468563)
                ·
                  rfl

theorem cell21_1293719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 10].length) (baseStart_1293719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1293719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1293719 prefixEnd_1293719 := by exact prefixLift 1293719
  have htrace : WordTrace (prefixWord ++ tailWord_1293719) baseStart_1293719 baseEnd_1293719 := by
    simpa [prefixWord, tailWord_1293719, baseEnd_1293719] using wordTrace_append hprefix tailTrace_1293719
  have hstable : (prefixWord ++ tailWord_1293719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293719).length < 2 ^ (prefixWord ++ tailWord_1293719).sum := by decide
  have hdescent : baseEnd_1293719 < baseStart_1293719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293753 : List Nat := [1, 2, 1, 4, 5, 1, 7]
def baseStart_1293753 : Nat := 118140960795 + 1293753 * 2 ^ 59
def prefixEnd_1293753 : Nat := 4983230072969 + 3 ^ 40 * 1293753 * 2
def baseEnd_1293753 : Nat := 32805784552907749093217

theorem tailTrace_1293753 : CollatzResearch.WordTrace tailWord_1293753 prefixEnd_1293753 32805784552907749093217 := by
  unfold tailWord_1293753
  simp only [CollatzResearch.WordTrace]
  refine ⟨47187048481961311266349913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31458032321307540844233275 47187048481961311266349913)
  ·
    refine ⟨35390286361470983449762435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47187048481961311266349913 35390286361470983449762435)
    ·
      refine ⟨53085429542206475174643653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35390286361470983449762435 53085429542206475174643653)
      ·
        refine ⟨9953518039163714095245685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53085429542206475174643653 9953518039163714095245685)
        ·
          refine ⟨933142316171598196429283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9953518039163714095245685 933142316171598196429283)
          ·
            refine ⟨1399713474257397294643925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933142316171598196429283 1399713474257397294643925)
            ·
              refine ⟨32805784552907749093217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1399713474257397294643925 32805784552907749093217)
              ·
                rfl

theorem cell21_1293753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 7].length) (baseStart_1293753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1293753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1293753 prefixEnd_1293753 := by exact prefixLift 1293753
  have htrace : WordTrace (prefixWord ++ tailWord_1293753) baseStart_1293753 baseEnd_1293753 := by
    simpa [prefixWord, tailWord_1293753, baseEnd_1293753] using wordTrace_append hprefix tailTrace_1293753
  have hstable : (prefixWord ++ tailWord_1293753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293753).length < 2 ^ (prefixWord ++ tailWord_1293753).sum := by decide
  have hdescent : baseEnd_1293753 < baseStart_1293753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293947 : List Nat := [1, 1, 1, 1, 1, 4, 6, 6]
def baseStart_1293947 : Nat := 118140960795 + 1293947 * 2 ^ 59
def prefixEnd_1293947 : Nat := 4983230072969 + 3 ^ 40 * 1293947 * 2
def baseEnd_1293947 : Nat := 98432111473089505201741

theorem tailTrace_1293947 : CollatzResearch.WordTrace tailWord_1293947 prefixEnd_1293947 98432111473089505201741 := by
  unfold tailWord_1293947
  simp only [CollatzResearch.WordTrace]
  refine ⟨47194124243258482398912095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31462749495505654932608063 47194124243258482398912095)
  ·
    refine ⟨70791186364887723598368143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47194124243258482398912095 70791186364887723598368143)
    ·
      refine ⟨106186779547331585397552215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70791186364887723598368143 106186779547331585397552215)
      ·
        refine ⟨159280169320997378096328323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106186779547331585397552215 159280169320997378096328323)
        ·
          refine ⟨238920253981496067144492485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159280169320997378096328323 238920253981496067144492485)
          ·
            refine ⟨44797547621530512589592341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 238920253981496067144492485 44797547621530512589592341)
            ·
              refine ⟨2099885044759242777637141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44797547621530512589592341 2099885044759242777637141)
              ·
                refine ⟨98432111473089505201741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2099885044759242777637141 98432111473089505201741)
                ·
                  rfl

theorem cell21_1293947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 6].length) (baseStart_1293947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1293947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1293947 prefixEnd_1293947 := by exact prefixLift 1293947
  have htrace : WordTrace (prefixWord ++ tailWord_1293947) baseStart_1293947 baseEnd_1293947 := by
    simpa [prefixWord, tailWord_1293947, baseEnd_1293947] using wordTrace_append hprefix tailTrace_1293947
  have hstable : (prefixWord ++ tailWord_1293947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293947).length < 2 ^ (prefixWord ++ tailWord_1293947).sum := by decide
  have hdescent : baseEnd_1293947 < baseStart_1293947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1293998 : List Nat := [4, 1, 4, 1, 2, 2, 1, 6]
def baseStart_1293998 : Nat := 118140960795 + 1293998 * 2 ^ 59
def prefixEnd_1293998 : Nat := 4983230072969 + 3 ^ 40 * 1293998 * 2
def baseEnd_1293998 : Nat := 98435991104701253418373

theorem tailTrace_1293998 : CollatzResearch.WordTrace tailWord_1293998 prefixEnd_1293998 98435991104701253418373 := by
  unfold tailWord_1293998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5899498045759214763627331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31463989577382478739345765 5899498045759214763627331)
  ·
    refine ⟨8849247068638822145440997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5899498045759214763627331 8849247068638822145440997)
    ·
      refine ⟨1659233825369779152270187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8849247068638822145440997 1659233825369779152270187)
      ·
        refine ⟨2488850738054668728405281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1659233825369779152270187 2488850738054668728405281)
        ·
          refine ⟨1866638053541001546303961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2488850738054668728405281 1866638053541001546303961)
          ·
            refine ⟨1399978540155751159727971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1866638053541001546303961 1399978540155751159727971)
            ·
              refine ⟨2099967810233626739591957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1399978540155751159727971 2099967810233626739591957)
              ·
                refine ⟨98435991104701253418373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2099967810233626739591957 98435991104701253418373)
                ·
                  rfl

theorem cell21_1293998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_1293998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1293998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1293998 prefixEnd_1293998 := by exact prefixLift 1293998
  have htrace : WordTrace (prefixWord ++ tailWord_1293998) baseStart_1293998 baseEnd_1293998 := by
    simpa [prefixWord, tailWord_1293998, baseEnd_1293998] using wordTrace_append hprefix tailTrace_1293998
  have hstable : (prefixWord ++ tailWord_1293998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1293998).length < 2 ^ (prefixWord ++ tailWord_1293998).sum := by decide
  have hdescent : baseEnd_1293998 < baseStart_1293998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1293998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294009 : List Nat := [1, 2, 1, 4, 1, 1, 4, 3, 4]
def baseStart_1294009 : Nat := 118140960795 + 1294009 * 2 ^ 59
def prefixEnd_1294009 : Nat := 4983230072969 + 3 ^ 40 * 1294009 * 2
def baseEnd_1294009 : Nat := 295310483663970185571763

theorem tailTrace_1294009 : CollatzResearch.WordTrace tailWord_1294009 prefixEnd_1294009 295310483663970185571763 := by
  unfold tailWord_1294009
  simp only [CollatzResearch.WordTrace]
  refine ⟨47196385569033866987669081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31464257046022577991779387 47196385569033866987669081)
  ·
    refine ⟨35397289176775400240751811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47196385569033866987669081 35397289176775400240751811)
    ·
      refine ⟨53095933765163100361127717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35397289176775400240751811 53095933765163100361127717)
      ·
        refine ⟨9955487580968081317711447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53095933765163100361127717 9955487580968081317711447)
        ·
          refine ⟨14933231371452121976567171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9955487580968081317711447 14933231371452121976567171)
          ·
            refine ⟨22399847057178182964850757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14933231371452121976567171 22399847057178182964850757)
            ·
              refine ⟨4199971323220909305909517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22399847057178182964850757 4199971323220909305909517)
              ·
                refine ⟨1574989246207840989716069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4199971323220909305909517 1574989246207840989716069)
                ·
                  refine ⟨295310483663970185571763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1574989246207840989716069 295310483663970185571763)
                  ·
                    rfl

theorem cell21_1294009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 4].length) (baseStart_1294009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1294009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1294009 prefixEnd_1294009 := by exact prefixLift 1294009
  have htrace : WordTrace (prefixWord ++ tailWord_1294009) baseStart_1294009 baseEnd_1294009 := by
    simpa [prefixWord, tailWord_1294009, baseEnd_1294009] using wordTrace_append hprefix tailTrace_1294009
  have hstable : (prefixWord ++ tailWord_1294009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294009).length < 2 ^ (prefixWord ++ tailWord_1294009).sum := by decide
  have hdescent : baseEnd_1294009 < baseStart_1294009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294029 : List Nat := [1, 6, 2, 1, 1, 1, 1, 5, 3]
def baseStart_1294029 : Nat := 118140960795 + 1294029 * 2 ^ 59
def prefixEnd_1294029 : Nat := 4983230072969 + 3 ^ 40 * 1294029 * 2
def baseEnd_1294029 : Nat := 295315047936454595238389

theorem tailTrace_1294029 : CollatzResearch.WordTrace tailWord_1294029 prefixEnd_1294029 295315047936454595238389 := by
  unfold tailWord_1294029
  simp only [CollatzResearch.WordTrace]
  refine ⟨47197115028961410403397141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31464743352640940268931427 47197115028961410403397141)
  ·
    refine ⟨2212364766982566112659241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47197115028961410403397141 2212364766982566112659241)
    ·
      refine ⟨1659273575236924584494431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2212364766982566112659241 1659273575236924584494431)
      ·
        refine ⟨2488910362855386876741647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1659273575236924584494431 2488910362855386876741647)
        ·
          refine ⟨3733365544283080315112471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2488910362855386876741647 3733365544283080315112471)
          ·
            refine ⟨5600048316424620472668707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3733365544283080315112471 5600048316424620472668707)
            ·
              refine ⟨8400072474636930709003061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5600048316424620472668707 8400072474636930709003061)
              ·
                refine ⟨787506794497212253969037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8400072474636930709003061 787506794497212253969037)
                ·
                  refine ⟨295315047936454595238389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 787506794497212253969037 295315047936454595238389)
                  ·
                    rfl

theorem cell21_1294029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_1294029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1294029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1294029 prefixEnd_1294029 := by exact prefixLift 1294029
  have htrace : WordTrace (prefixWord ++ tailWord_1294029) baseStart_1294029 baseEnd_1294029 := by
    simpa [prefixWord, tailWord_1294029, baseEnd_1294029] using wordTrace_append hprefix tailTrace_1294029
  have hstable : (prefixWord ++ tailWord_1294029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294029).length < 2 ^ (prefixWord ++ tailWord_1294029).sum := by decide
  have hdescent : baseEnd_1294029 < baseStart_1294029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294116 : List Nat := [2, 3, 1, 3, 2, 2, 2, 6]
def baseStart_1294116 : Nat := 118140960795 + 1294116 * 2 ^ 59
def prefixEnd_1294116 : Nat := 4983230072969 + 3 ^ 40 * 1294116 * 2
def baseEnd_1294116 : Nat := 98444967507253925762737

theorem tailTrace_1294116 : CollatzResearch.WordTrace tailWord_1294116 prefixEnd_1294116 98444967507253925762737 := by
  unfold tailWord_1294116
  simp only [CollatzResearch.WordTrace]
  refine ⟨23600144089823112130907101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31466858786430816174542801 23600144089823112130907101)
  ·
    refine ⟨8850054033683667049090163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23600144089823112130907101 8850054033683667049090163)
    ·
      refine ⟨13275081050525500573635245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8850054033683667049090163 13275081050525500573635245)
      ·
        refine ⟨4978155393947062715113217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13275081050525500573635245 4978155393947062715113217)
        ·
          refine ⟨3733616545460297036334913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4978155393947062715113217 3733616545460297036334913)
          ·
            refine ⟨2800212409095222777251185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3733616545460297036334913 2800212409095222777251185)
            ·
              refine ⟨2100159306821417082938389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2800212409095222777251185 2100159306821417082938389)
              ·
                refine ⟨98444967507253925762737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2100159306821417082938389 98444967507253925762737)
                ·
                  rfl

theorem cell21_1294116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 6].length) (baseStart_1294116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1294116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1294116 prefixEnd_1294116 := by exact prefixLift 1294116
  have htrace : WordTrace (prefixWord ++ tailWord_1294116) baseStart_1294116 baseEnd_1294116 := by
    simpa [prefixWord, tailWord_1294116, baseEnd_1294116] using wordTrace_append hprefix tailTrace_1294116
  have hstable : (prefixWord ++ tailWord_1294116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294116).length < 2 ^ (prefixWord ++ tailWord_1294116).sum := by decide
  have hdescent : baseEnd_1294116 < baseStart_1294116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294161 : List Nat := [1, 2, 2, 1, 5, 1, 1, 4, 4]
def baseStart_1294161 : Nat := 118140960795 + 1294161 * 2 ^ 59
def prefixEnd_1294161 : Nat := 4983230072969 + 3 ^ 40 * 1294161 * 2
def baseEnd_1294161 : Nat := 295345172134851699038119

theorem tailTrace_1294161 : CollatzResearch.WordTrace tailWord_1294161 prefixEnd_1294161 295345172134851699038119 := by
  unfold tailWord_1294161
  simp only [CollatzResearch.WordTrace]
  refine ⟨47201929464483196947202337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31467952976322131298134891 47201929464483196947202337)
  ·
    refine ⟨35401447098362397710401753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47201929464483196947202337 35401447098362397710401753)
    ·
      refine ⟨26551085323771798282801315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35401447098362397710401753 26551085323771798282801315)
      ·
        refine ⟨39826627985657697424201973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26551085323771798282801315 39826627985657697424201973)
        ·
          refine ⟨3733746373655409133518935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39826627985657697424201973 3733746373655409133518935)
          ·
            refine ⟨5600619560483113700278403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3733746373655409133518935 5600619560483113700278403)
            ·
              refine ⟨8400929340724670550417605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5600619560483113700278403 8400929340724670550417605)
              ·
                refine ⟨1575174251385875728203301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8400929340724670550417605 1575174251385875728203301)
                ·
                  refine ⟨295345172134851699038119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1575174251385875728203301 295345172134851699038119)
                  ·
                    rfl

theorem cell21_1294161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 4].length) (baseStart_1294161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1294161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1294161 prefixEnd_1294161 := by exact prefixLift 1294161
  have htrace : WordTrace (prefixWord ++ tailWord_1294161) baseStart_1294161 baseEnd_1294161 := by
    simpa [prefixWord, tailWord_1294161, baseEnd_1294161] using wordTrace_append hprefix tailTrace_1294161
  have hstable : (prefixWord ++ tailWord_1294161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294161).length < 2 ^ (prefixWord ++ tailWord_1294161).sum := by decide
  have hdescent : baseEnd_1294161 < baseStart_1294161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294164 : List Nat := [2, 4, 1, 1, 3, 2, 1, 4, 3]
def baseStart_1294164 : Nat := 118140960795 + 1294164 * 2 ^ 59
def prefixEnd_1294164 : Nat := 4983230072969 + 3 ^ 40 * 1294164 * 2
def baseEnd_1294164 : Nat := 295345856775724360488113

theorem tailTrace_1294164 : CollatzResearch.WordTrace tailWord_1294164 prefixEnd_1294164 295345856775724360488113 := by
  unfold tailWord_1294164
  simp only [CollatzResearch.WordTrace]
  refine ⟨23601019441736164229780773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31468025922314885639707697 23601019441736164229780773)
  ·
    refine ⟨4425191145325530793083895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23601019441736164229780773 4425191145325530793083895)
    ·
      refine ⟨6637786717988296189625843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4425191145325530793083895 6637786717988296189625843)
      ·
        refine ⟨9956680076982444284438765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6637786717988296189625843 9956680076982444284438765)
        ·
          refine ⟨3733755028868416606664537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9956680076982444284438765 3733755028868416606664537)
          ·
            refine ⟨2800316271651312454998403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3733755028868416606664537 2800316271651312454998403)
            ·
              refine ⟨4200474407476968682497605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2800316271651312454998403 4200474407476968682497605)
              ·
                refine ⟨787588951401931627968301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4200474407476968682497605 787588951401931627968301)
                ·
                  refine ⟨295345856775724360488113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 787588951401931627968301 295345856775724360488113)
                  ·
                    rfl

theorem cell21_1294164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_1294164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1294164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1294164 prefixEnd_1294164 := by exact prefixLift 1294164
  have htrace : WordTrace (prefixWord ++ tailWord_1294164) baseStart_1294164 baseEnd_1294164 := by
    simpa [prefixWord, tailWord_1294164, baseEnd_1294164] using wordTrace_append hprefix tailTrace_1294164
  have hstable : (prefixWord ++ tailWord_1294164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294164).length < 2 ^ (prefixWord ++ tailWord_1294164).sum := by decide
  have hdescent : baseEnd_1294164 < baseStart_1294164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294175 : List Nat := [1, 1, 2, 3, 1, 4, 3, 6]
def baseStart_1294175 : Nat := 118140960795 + 1294175 * 2 ^ 59
def prefixEnd_1294175 : Nat := 4983230072969 + 3 ^ 40 * 1294175 * 2
def baseEnd_1294175 : Nat := 98449455708530261934919

theorem tailTrace_1294175 : CollatzResearch.WordTrace tailWord_1294175 prefixEnd_1294175 98449455708530261934919 := by
  unfold tailWord_1294175
  simp only [CollatzResearch.WordTrace]
  refine ⟨47202440086432477338211979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31468293390954984892141319 47202440086432477338211979)
  ·
    refine ⟨70803660129648716007317969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47202440086432477338211979 70803660129648716007317969)
    ·
      refine ⟨53102745097236537005488477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70803660129648716007317969 53102745097236537005488477)
      ·
        refine ⟨19913529411463701377058179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53102745097236537005488477 19913529411463701377058179)
        ·
          refine ⟨29870294117195552065587269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19913529411463701377058179 29870294117195552065587269)
          ·
            refine ⟨5600680146974166012297613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29870294117195552065587269 5600680146974166012297613)
            ·
              refine ⟨2100255055115312254611605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5600680146974166012297613 2100255055115312254611605)
              ·
                refine ⟨98449455708530261934919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2100255055115312254611605 98449455708530261934919)
                ·
                  rfl

theorem cell21_1294175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 6].length) (baseStart_1294175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1294175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1294175 prefixEnd_1294175 := by exact prefixLift 1294175
  have htrace : WordTrace (prefixWord ++ tailWord_1294175) baseStart_1294175 baseEnd_1294175 := by
    simpa [prefixWord, tailWord_1294175, baseEnd_1294175] using wordTrace_append hprefix tailTrace_1294175
  have hstable : (prefixWord ++ tailWord_1294175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294175).length < 2 ^ (prefixWord ++ tailWord_1294175).sum := by decide
  have hdescent : baseEnd_1294175 < baseStart_1294175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294178 : List Nat := [3, 3, 2, 1, 2, 1, 2, 3, 4]
def baseStart_1294178 : Nat := 118140960795 + 1294178 * 2 ^ 59
def prefixEnd_1294178 : Nat := 4983230072969 + 3 ^ 40 * 1294178 * 2
def baseEnd_1294178 : Nat := 295349051766463447254751

theorem tailTrace_1294178 : CollatzResearch.WordTrace tailWord_1294178 prefixEnd_1294178 295349051766463447254751 := by
  unfold tailWord_1294178
  simp only [CollatzResearch.WordTrace]
  refine ⟨11800637376355402212642797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31468366336947739233714125 11800637376355402212642797)
  ·
    refine ⟨4425239016133275829741049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11800637376355402212642797 4425239016133275829741049)
    ·
      refine ⟨3318929262099956872305787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4425239016133275829741049 3318929262099956872305787)
      ·
        refine ⟨4978393893149935308458681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3318929262099956872305787 4978393893149935308458681)
        ·
          refine ⟨3733795419862451481344011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4978393893149935308458681 3733795419862451481344011)
          ·
            refine ⟨5600693129793677222016017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3733795419862451481344011 5600693129793677222016017)
            ·
              refine ⟨4200519847345257916512013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5600693129793677222016017 4200519847345257916512013)
              ·
                refine ⟨1575194942754471718692005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4200519847345257916512013 1575194942754471718692005)
                ·
                  refine ⟨295349051766463447254751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1575194942754471718692005 295349051766463447254751)
                  ·
                    rfl

theorem cell21_1294178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_1294178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1294178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1294178 prefixEnd_1294178 := by exact prefixLift 1294178
  have htrace : WordTrace (prefixWord ++ tailWord_1294178) baseStart_1294178 baseEnd_1294178 := by
    simpa [prefixWord, tailWord_1294178, baseEnd_1294178] using wordTrace_append hprefix tailTrace_1294178
  have hstable : (prefixWord ++ tailWord_1294178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294178).length < 2 ^ (prefixWord ++ tailWord_1294178).sum := by decide
  have hdescent : baseEnd_1294178 < baseStart_1294178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294282 : List Nat := [3, 1, 2, 1, 2, 1, 5, 1, 5]
def baseStart_1294282 : Nat := 118140960795 + 1294282 * 2 ^ 59
def prefixEnd_1294282 : Nat := 4983230072969 + 3 ^ 40 * 1294282 * 2
def baseEnd_1294282 : Nat := 295372785983382377521205

theorem tailTrace_1294282 : CollatzResearch.WordTrace tailWord_1294282 prefixEnd_1294282 295372785983382377521205 := by
  unfold tailWord_1294282
  simp only [CollatzResearch.WordTrace]
  refine ⟨11801585674261208653089275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31470895131363223074904733 11801585674261208653089275)
  ·
    refine ⟨17702378511391812979633913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11801585674261208653089275 17702378511391812979633913)
    ·
      refine ⟨13276783883543859734725435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17702378511391812979633913 13276783883543859734725435)
      ·
        refine ⟨19915175825315789602088153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13276783883543859734725435 19915175825315789602088153)
        ·
          refine ⟨14936381868986842201566115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19915175825315789602088153 14936381868986842201566115)
          ·
            refine ⟨22404572803480263302349173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14936381868986842201566115 22404572803480263302349173)
            ·
              refine ⟨2100428700326274684595235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22404572803480263302349173 2100428700326274684595235)
              ·
                refine ⟨3150643050489412026892853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2100428700326274684595235 3150643050489412026892853)
                ·
                  refine ⟨295372785983382377521205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3150643050489412026892853 295372785983382377521205)
                  ·
                    rfl

theorem cell21_1294282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_1294282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1294282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1294282 prefixEnd_1294282 := by exact prefixLift 1294282
  have htrace : WordTrace (prefixWord ++ tailWord_1294282) baseStart_1294282 baseEnd_1294282 := by
    simpa [prefixWord, tailWord_1294282, baseEnd_1294282] using wordTrace_append hprefix tailTrace_1294282
  have hstable : (prefixWord ++ tailWord_1294282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294282).length < 2 ^ (prefixWord ++ tailWord_1294282).sum := by decide
  have hdescent : baseEnd_1294282 < baseStart_1294282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294389 : List Nat := [1, 3, 3, 1, 1, 1, 5, 2, 4]
def baseStart_1294389 : Nat := 118140960795 + 1294389 * 2 ^ 59
def prefixEnd_1294389 : Nat := 4983230072969 + 3 ^ 40 * 1294389 * 2
def baseEnd_1294389 : Nat := 295397204841173969237653

theorem tailTrace_1294389 : CollatzResearch.WordTrace tailWord_1294389 prefixEnd_1294389 295397204841173969237653 := by
  unfold tailWord_1294389
  simp only [CollatzResearch.WordTrace]
  refine ⟨47210245307657191886502221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31473496871771461257668147 47210245307657191886502221)
  ·
    refine ⟨17703841990371446957438333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47210245307657191886502221 17703841990371446957438333)
    ·
      refine ⟨6638940746389292609039375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17703841990371446957438333 6638940746389292609039375)
      ·
        refine ⟨9958411119583938913559063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6638940746389292609039375 9958411119583938913559063)
        ·
          refine ⟨14937616679375908370338595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9958411119583938913559063 14937616679375908370338595)
          ·
            refine ⟨22406425019063862555507893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14937616679375908370338595 22406425019063862555507893)
            ·
              refine ⟨2100602345537237114578865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22406425019063862555507893 2100602345537237114578865)
              ·
                refine ⟨1575451759152927835934149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2100602345537237114578865 1575451759152927835934149)
                ·
                  refine ⟨295397204841173969237653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1575451759152927835934149 295397204841173969237653)
                  ·
                    rfl

theorem cell21_1294389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_1294389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1294389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1294389 prefixEnd_1294389 := by exact prefixLift 1294389
  have htrace : WordTrace (prefixWord ++ tailWord_1294389) baseStart_1294389 baseEnd_1294389 := by
    simpa [prefixWord, tailWord_1294389, baseEnd_1294389] using wordTrace_append hprefix tailTrace_1294389
  have hstable : (prefixWord ++ tailWord_1294389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294389).length < 2 ^ (prefixWord ++ tailWord_1294389).sum := by decide
  have hdescent : baseEnd_1294389 < baseStart_1294389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294448 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 6]
def baseStart_1294448 : Nat := 118140960795 + 1294448 * 2 ^ 59
def prefixEnd_1294448 : Nat := 4983230072969 + 3 ^ 40 * 1294448 * 2
def baseEnd_1294448 : Nat := 295410669445002977754199

theorem tailTrace_1294448 : CollatzResearch.WordTrace tailWord_1294448 prefixEnd_1294448 295410669445002977754199 := by
  unfold tailWord_1294448
  simp only [CollatzResearch.WordTrace]
  refine ⟨23606198607221722481449999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31474931476295629975266665 23606198607221722481449999)
  ·
    refine ⟨35409297910832583722174999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23606198607221722481449999 35409297910832583722174999)
    ·
      refine ⟨53113946866248875583262499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35409297910832583722174999 53113946866248875583262499)
      ·
        refine ⟨79670920299373313374893749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53113946866248875583262499 79670920299373313374893749)
        ·
          refine ⟨7469148778066248128896289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79670920299373313374893749 7469148778066248128896289)
          ·
            refine ⟨5601861583549686096672217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7469148778066248128896289 5601861583549686096672217)
            ·
              refine ⟨4201396187662264572504163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5601861583549686096672217 4201396187662264572504163)
              ·
                refine ⟨6302094281493396858756245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4201396187662264572504163 6302094281493396858756245)
                ·
                  refine ⟨295410669445002977754199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6302094281493396858756245 295410669445002977754199)
                  ·
                    rfl

theorem cell21_1294448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_1294448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1294448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1294448 prefixEnd_1294448 := by exact prefixLift 1294448
  have htrace : WordTrace (prefixWord ++ tailWord_1294448) baseStart_1294448 baseEnd_1294448 := by
    simpa [prefixWord, tailWord_1294448, baseEnd_1294448] using wordTrace_append hprefix tailTrace_1294448
  have hstable : (prefixWord ++ tailWord_1294448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294448).length < 2 ^ (prefixWord ++ tailWord_1294448).sum := by decide
  have hdescent : baseEnd_1294448 < baseStart_1294448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294507 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 12]
def baseStart_1294507 : Nat := 118140960795 + 1294507 * 2 ^ 59
def prefixEnd_1294507 : Nat := 4983230072969 + 3 ^ 40 * 1294507 * 2
def baseEnd_1294507 : Nat := 295424134048831986270745

theorem tailTrace_1294507 : CollatzResearch.WordTrace tailWord_1294507 prefixEnd_1294507 295424134048831986270745 := by
  unfold tailWord_1294507
  simp only [CollatzResearch.WordTrace]
  refine ⟨47214549121229698039297775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31476366080819798692865183 47214549121229698039297775)
  ·
    refine ⟨70821823681844547058946663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47214549121229698039297775 70821823681844547058946663)
    ·
      refine ⟨106232735522766820588419995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70821823681844547058946663 106232735522766820588419995)
      ·
        refine ⟨159349103284150230882629993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106232735522766820588419995 159349103284150230882629993)
        ·
          refine ⟨119511827463112673161972495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159349103284150230882629993 119511827463112673161972495)
          ·
            refine ⟨179267741194669009742958743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119511827463112673161972495 179267741194669009742958743)
            ·
              refine ⟨268901611792003514614438115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179267741194669009742958743 268901611792003514614438115)
              ·
                refine ⟨403352417688005271921657173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268901611792003514614438115 403352417688005271921657173)
                ·
                  refine ⟨295424134048831986270745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 403352417688005271921657173 295424134048831986270745)
                  ·
                    rfl

theorem cell21_1294507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 12].length) (baseStart_1294507 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1294507 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1294507 prefixEnd_1294507 := by exact prefixLift 1294507
  have htrace : WordTrace (prefixWord ++ tailWord_1294507) baseStart_1294507 baseEnd_1294507 := by
    simpa [prefixWord, tailWord_1294507, baseEnd_1294507] using wordTrace_append hprefix tailTrace_1294507
  have hstable : (prefixWord ++ tailWord_1294507).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294507).length < 2 ^ (prefixWord ++ tailWord_1294507).sum := by decide
  have hdescent : baseEnd_1294507 < baseStart_1294507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294513 : List Nat := [1, 2, 2, 5, 3, 1, 1, 6]
def baseStart_1294513 : Nat := 118140960795 + 1294513 * 2 ^ 59
def prefixEnd_1294513 : Nat := 4983230072969 + 3 ^ 40 * 1294513 * 2
def baseEnd_1294513 : Nat := 98475167776859103056911

theorem tailTrace_1294513 : CollatzResearch.WordTrace tailWord_1294513 prefixEnd_1294513 98475167776859103056911 := by
  unfold tailWord_1294513
  simp only [CollatzResearch.WordTrace]
  refine ⟨47214767959207961064016193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31476511972805307376010795 47214767959207961064016193)
  ·
    refine ⟨35411075969405970798012145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47214767959207961064016193 35411075969405970798012145)
    ·
      refine ⟨26558306977054478098509109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35411075969405970798012145 26558306977054478098509109)
      ·
        refine ⟨2489841279098857321735229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26558306977054478098509109 2489841279098857321735229)
        ·
          refine ⟨933690479662071495650711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2489841279098857321735229 933690479662071495650711)
          ·
            refine ⟨1400535719493107243476067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933690479662071495650711 1400535719493107243476067)
            ·
              refine ⟨2100803579239660865214101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1400535719493107243476067 2100803579239660865214101)
              ·
                refine ⟨98475167776859103056911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2100803579239660865214101 98475167776859103056911)
                ·
                  rfl

theorem cell21_1294513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 6].length) (baseStart_1294513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1294513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1294513 prefixEnd_1294513 := by exact prefixLift 1294513
  have htrace : WordTrace (prefixWord ++ tailWord_1294513) baseStart_1294513 baseEnd_1294513 := by
    simpa [prefixWord, tailWord_1294513, baseEnd_1294513] using wordTrace_append hprefix tailTrace_1294513
  have hstable : (prefixWord ++ tailWord_1294513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294513).length < 2 ^ (prefixWord ++ tailWord_1294513).sum := by decide
  have hdescent : baseEnd_1294513 < baseStart_1294513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294530 : List Nat := [3, 5, 1, 1, 1, 2, 3, 5]
def baseStart_1294530 : Nat := 118140960795 + 1294530 * 2 ^ 59
def prefixEnd_1294530 : Nat := 4983230072969 + 3 ^ 40 * 1294530 * 2
def baseEnd_1294530 : Nat := 98476460987396352462455

theorem tailTrace_1294530 : CollatzResearch.WordTrace tailWord_1294530 prefixEnd_1294530 98476460987396352462455 := by
  unfold tailWord_1294530
  simp only [CollatzResearch.WordTrace]
  refine ⟨11803847000036593241846261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31476925333430915311590029 11803847000036593241846261)
  ·
    refine ⟨1106610656253430616423087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11803847000036593241846261 1106610656253430616423087)
    ·
      refine ⟨1659915984380145924634631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1106610656253430616423087 1659915984380145924634631)
      ·
        refine ⟨2489873976570218886951947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1659915984380145924634631 2489873976570218886951947)
        ·
          refine ⟨3734810964855328330427921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2489873976570218886951947 3734810964855328330427921)
          ·
            refine ⟨2801108223641496247820941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3734810964855328330427921 2801108223641496247820941)
            ·
              refine ⟨1050415583865561092932853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2801108223641496247820941 1050415583865561092932853)
              ·
                refine ⟨98476460987396352462455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1050415583865561092932853 98476460987396352462455)
                ·
                  rfl

theorem cell21_1294530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_1294530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1294530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1294530 prefixEnd_1294530 := by exact prefixLift 1294530
  have htrace : WordTrace (prefixWord ++ tailWord_1294530) baseStart_1294530 baseEnd_1294530 := by
    simpa [prefixWord, tailWord_1294530, baseEnd_1294530] using wordTrace_append hprefix tailTrace_1294530
  have hstable : (prefixWord ++ tailWord_1294530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294530).length < 2 ^ (prefixWord ++ tailWord_1294530).sum := by decide
  have hdescent : baseEnd_1294530 < baseStart_1294530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294583 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 10]
def baseStart_1294583 : Nat := 118140960795 + 1294583 * 2 ^ 59
def prefixEnd_1294583 : Nat := 4983230072969 + 3 ^ 40 * 1294583 * 2
def baseEnd_1294583 : Nat := 295441478284272743003923

theorem tailTrace_1294583 : CollatzResearch.WordTrace tailWord_1294583 prefixEnd_1294583 295441478284272743003923 := by
  unfold tailWord_1294583
  simp only [CollatzResearch.WordTrace]
  refine ⟨47217321068954363019064403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31478214045969575346042935 47217321068954363019064403)
  ·
    refine ⟨70825981603431544528596605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47217321068954363019064403 70825981603431544528596605)
    ·
      refine ⟨26559743101286829198223727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70825981603431544528596605 26559743101286829198223727)
      ·
        refine ⟨39839614651930243797335591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26559743101286829198223727 39839614651930243797335591)
        ·
          refine ⟨59759421977895365696003387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39839614651930243797335591 59759421977895365696003387)
          ·
            refine ⟨89639132966843048544005081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59759421977895365696003387 89639132966843048544005081)
            ·
              refine ⟨67229349725132286408003811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89639132966843048544005081 67229349725132286408003811)
              ·
                refine ⟨100844024587698429612005717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67229349725132286408003811 100844024587698429612005717)
                ·
                  refine ⟨295441478284272743003923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 100844024587698429612005717 295441478284272743003923)
                  ·
                    rfl

theorem cell21_1294583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 10].length) (baseStart_1294583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1294583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1294583 prefixEnd_1294583 := by exact prefixLift 1294583
  have htrace : WordTrace (prefixWord ++ tailWord_1294583) baseStart_1294583 baseEnd_1294583 := by
    simpa [prefixWord, tailWord_1294583, baseEnd_1294583] using wordTrace_append hprefix tailTrace_1294583
  have hstable : (prefixWord ++ tailWord_1294583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294583).length < 2 ^ (prefixWord ++ tailWord_1294583).sum := by decide
  have hdescent : baseEnd_1294583 < baseStart_1294583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294600 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 6]
def baseStart_1294600 : Nat := 118140960795 + 1294600 * 2 ^ 59
def prefixEnd_1294600 : Nat := 4983230072969 + 3 ^ 40 * 1294600 * 2
def baseEnd_1294600 : Nat := 295445357915884491220555

theorem tailTrace_1294600 : CollatzResearch.WordTrace tailWord_1294600 prefixEnd_1294600 295445357915884491220555 := by
  unfold tailWord_1294600
  simp only [CollatzResearch.WordTrace]
  refine ⟨23608970554946387461216627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31478627406595183281622169 23608970554946387461216627)
  ·
    refine ⟨35413455832419581191824941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23608970554946387461216627 35413455832419581191824941)
    ·
      refine ⟨13280045937157342946934353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35413455832419581191824941 13280045937157342946934353)
      ·
        refine ⟨9960034452868007210200765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13280045937157342946934353 9960034452868007210200765)
        ·
          refine ⟨3735012919825502703825287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9960034452868007210200765 3735012919825502703825287)
          ·
            refine ⟨5602519379738254055737931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3735012919825502703825287 5602519379738254055737931)
            ·
              refine ⟨8403779069607381083606897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5602519379738254055737931 8403779069607381083606897)
              ·
                refine ⟨6302834302205535812705173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8403779069607381083606897 6302834302205535812705173)
                ·
                  refine ⟨295445357915884491220555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6302834302205535812705173 295445357915884491220555)
                  ·
                    rfl

theorem cell21_1294600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_1294600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1294600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1294600 prefixEnd_1294600 := by exact prefixLift 1294600
  have htrace : WordTrace (prefixWord ++ tailWord_1294600) baseStart_1294600 baseEnd_1294600 := by
    simpa [prefixWord, tailWord_1294600, baseEnd_1294600] using wordTrace_append hprefix tailTrace_1294600
  have hstable : (prefixWord ++ tailWord_1294600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294600).length < 2 ^ (prefixWord ++ tailWord_1294600).sum := by decide
  have hdescent : baseEnd_1294600 < baseStart_1294600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294634 : List Nat := [3, 1, 4, 2, 2, 1, 1, 3, 4]
def baseStart_1294634 : Nat := 118140960795 + 1294634 * 2 ^ 59
def prefixEnd_1294634 : Nat := 4983230072969 + 3 ^ 40 * 1294634 * 2
def baseEnd_1294634 : Nat := 295453117179107987653819

theorem tailTrace_1294634 : CollatzResearch.WordTrace tailWord_1294634 prefixEnd_1294634 295453117179107987653819 := by
  unfold tailWord_1294634
  simp only [CollatzResearch.WordTrace]
  refine ⟨11804795297942399682292739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31479454127846399152780637 11804795297942399682292739)
  ·
    refine ⟨17707192946913599523439109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11804795297942399682292739 17707192946913599523439109)
    ·
      refine ⟨3320098677546299910644833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17707192946913599523439109 3320098677546299910644833)
      ·
        refine ⟨2490074008159724932983625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3320098677546299910644833 2490074008159724932983625)
        ·
          refine ⟨1867555506119793699737719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2490074008159724932983625 1867555506119793699737719)
          ·
            refine ⟨2801333259179690549606579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1867555506119793699737719 2801333259179690549606579)
            ·
              refine ⟨4201999888769535824409869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2801333259179690549606579 4201999888769535824409869)
              ·
                refine ⟨1575749958288575934153701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4201999888769535824409869 1575749958288575934153701)
                ·
                  refine ⟨295453117179107987653819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1575749958288575934153701 295453117179107987653819)
                  ·
                    rfl

theorem cell21_1294634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_1294634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1294634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1294634 prefixEnd_1294634 := by exact prefixLift 1294634
  have htrace : WordTrace (prefixWord ++ tailWord_1294634) baseStart_1294634 baseEnd_1294634 := by
    simpa [prefixWord, tailWord_1294634, baseEnd_1294634] using wordTrace_append hprefix tailTrace_1294634
  have hstable : (prefixWord ++ tailWord_1294634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294634).length < 2 ^ (prefixWord ++ tailWord_1294634).sum := by decide
  have hdescent : baseEnd_1294634 < baseStart_1294634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294645 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 7]
def baseStart_1294645 : Nat := 118140960795 + 1294645 * 2 ^ 59
def prefixEnd_1294645 : Nat := 4983230072969 + 3 ^ 40 * 1294645 * 2
def baseEnd_1294645 : Nat := 295455627528974412970463

theorem tailTrace_1294645 : CollatzResearch.WordTrace tailWord_1294645 prefixEnd_1294645 295455627528974412970463 := by
  unfold tailWord_1294645
  simp only [CollatzResearch.WordTrace]
  refine ⟨47219582394729747607821389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31479721596486498405214259 47219582394729747607821389)
  ·
    refine ⟨17707343398023655352933021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47219582394729747607821389 17707343398023655352933021)
    ·
      refine ⟨6640253774258870757349883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17707343398023655352933021 6640253774258870757349883)
      ·
        refine ⟨9960380661388306136024825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6640253774258870757349883 9960380661388306136024825)
        ·
          refine ⟨7470285496041229602018619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9960380661388306136024825 7470285496041229602018619)
          ·
            refine ⟨11205428244061844403027929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7470285496041229602018619 11205428244061844403027929)
            ·
              refine ⟨8404071183046383302270947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11205428244061844403027929 8404071183046383302270947)
              ·
                refine ⟨12606106774569574953406421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8404071183046383302270947 12606106774569574953406421)
                ·
                  refine ⟨295455627528974412970463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12606106774569574953406421 295455627528974412970463)
                  ·
                    rfl

theorem cell21_1294645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_1294645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1294645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1294645 prefixEnd_1294645 := by exact prefixLift 1294645
  have htrace : WordTrace (prefixWord ++ tailWord_1294645) baseStart_1294645 baseEnd_1294645 := by
    simpa [prefixWord, tailWord_1294645, baseEnd_1294645] using wordTrace_append hprefix tailTrace_1294645
  have hstable : (prefixWord ++ tailWord_1294645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294645).length < 2 ^ (prefixWord ++ tailWord_1294645).sum := by decide
  have hdescent : baseEnd_1294645 < baseStart_1294645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294659 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 8]
def baseStart_1294659 : Nat := 118140960795 + 1294659 * 2 ^ 59
def prefixEnd_1294659 : Nat := 4983230072969 + 3 ^ 40 * 1294659 * 2
def baseEnd_1294659 : Nat := 295458822519713499737101

theorem tailTrace_1294659 : CollatzResearch.WordTrace tailWord_1294659 prefixEnd_1294659 295458822519713499737101 := by
  unfold tailWord_1294659
  simp only [CollatzResearch.WordTrace]
  refine ⟨47220093016679027998831031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31480062011119351999220687 47220093016679027998831031)
  ·
    refine ⟨70830139525018541998246547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47220093016679027998831031 70830139525018541998246547)
    ·
      refine ⟨106245209287527812997369821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70830139525018541998246547 106245209287527812997369821)
      ·
        refine ⟨39841953482822929874013683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106245209287527812997369821 39841953482822929874013683)
        ·
          refine ⟨59762930224234394811020525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39841953482822929874013683 59762930224234394811020525)
          ·
            refine ⟨22411098834087898054132697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59762930224234394811020525 22411098834087898054132697)
            ·
              refine ⟨16808324125565923540599523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22411098834087898054132697 16808324125565923540599523)
              ·
                refine ⟨25212486188348885310899285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16808324125565923540599523 25212486188348885310899285)
                ·
                  refine ⟨295458822519713499737101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25212486188348885310899285 295458822519713499737101)
                  ·
                    rfl

theorem cell21_1294659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 8].length) (baseStart_1294659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1294659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1294659 prefixEnd_1294659 := by exact prefixLift 1294659
  have htrace : WordTrace (prefixWord ++ tailWord_1294659) baseStart_1294659 baseEnd_1294659 := by
    simpa [prefixWord, tailWord_1294659, baseEnd_1294659] using wordTrace_append hprefix tailTrace_1294659
  have hstable : (prefixWord ++ tailWord_1294659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294659).length < 2 ^ (prefixWord ++ tailWord_1294659).sum := by decide
  have hdescent : baseEnd_1294659 < baseStart_1294659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294859 : List Nat := [1, 1, 1, 1, 7, 3, 1, 6]
def baseStart_1294859 : Nat := 118140960795 + 1294859 * 2 ^ 59
def prefixEnd_1294859 : Nat := 4983230072969 + 3 ^ 40 * 1294859 * 2
def baseEnd_1294859 : Nat := 98501488414852532134453

theorem tailTrace_1294859 : CollatzResearch.WordTrace tailWord_1294859 prefixEnd_1294859 98501488414852532134453 := by
  unfold tailWord_1294859
  simp only [CollatzResearch.WordTrace]
  refine ⟨47227387615954462156111631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31484925077302974770741087 47227387615954462156111631)
  ·
    refine ⟨70841081423931693234167447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47227387615954462156111631 70841081423931693234167447)
    ·
      refine ⟨106261622135897539851251171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70841081423931693234167447 106261622135897539851251171)
      ·
        refine ⟨159392433203846309776876757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106261622135897539851251171 159392433203846309776876757)
        ·
          refine ⟨3735760153215147885395549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 159392433203846309776876757 3735760153215147885395549)
          ·
            refine ⟨1400910057455680457023331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3735760153215147885395549 1400910057455680457023331)
            ·
              refine ⟨2101365086183520685534997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1400910057455680457023331 2101365086183520685534997)
              ·
                refine ⟨98501488414852532134453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2101365086183520685534997 98501488414852532134453)
                ·
                  rfl

theorem cell21_1294859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 6].length) (baseStart_1294859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1294859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1294859 prefixEnd_1294859 := by exact prefixLift 1294859
  have htrace : WordTrace (prefixWord ++ tailWord_1294859) baseStart_1294859 baseEnd_1294859 := by
    simpa [prefixWord, tailWord_1294859, baseEnd_1294859] using wordTrace_append hprefix tailTrace_1294859
  have hstable : (prefixWord ++ tailWord_1294859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294859).length < 2 ^ (prefixWord ++ tailWord_1294859).sum := by decide
  have hdescent : baseEnd_1294859 < baseStart_1294859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294893 : List Nat := [1, 5, 4, 1, 1, 1, 8]
def baseStart_1294893 : Nat := 118140960795 + 1294893 * 2 ^ 59
def prefixEnd_1294893 : Nat := 4983230072969 + 3 ^ 40 * 1294893 * 2
def baseEnd_1294893 : Nat := 32834691611975676981847

theorem tailTrace_1294893 : CollatzResearch.WordTrace tailWord_1294893 prefixEnd_1294893 32834691611975676981847 := by
  unfold tailWord_1294893
  simp only [CollatzResearch.WordTrace]
  refine ⟨47228627697831285962849333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31485751798554190641899555 47228627697831285962849333)
  ·
    refine ⟨4427683846671683059017125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47228627697831285962849333 4427683846671683059017125)
    ·
      refine ⟨830190721250940573565711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4427683846671683059017125 830190721250940573565711)
      ·
        refine ⟨1245286081876410860348567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 830190721250940573565711 1245286081876410860348567)
        ·
          refine ⟨1867929122814616290522851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1245286081876410860348567 1867929122814616290522851)
          ·
            refine ⟨2801893684221924435784277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1867929122814616290522851 2801893684221924435784277)
            ·
              refine ⟨32834691611975676981847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2801893684221924435784277 32834691611975676981847)
              ·
                rfl

theorem cell21_1294893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 8].length) (baseStart_1294893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1294893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1294893 prefixEnd_1294893 := by exact prefixLift 1294893
  have htrace : WordTrace (prefixWord ++ tailWord_1294893) baseStart_1294893 baseEnd_1294893 := by
    simpa [prefixWord, tailWord_1294893, baseEnd_1294893] using wordTrace_append hprefix tailTrace_1294893
  have hstable : (prefixWord ++ tailWord_1294893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294893).length < 2 ^ (prefixWord ++ tailWord_1294893).sum := by decide
  have hdescent : baseEnd_1294893 < baseStart_1294893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1294952 : List Nat := [2, 1, 4, 3, 3, 1, 7]
def baseStart_1294952 : Nat := 118140960795 + 1294952 * 2 ^ 59
def prefixEnd_1294952 : Nat := 4983230072969 + 3 ^ 40 * 1294952 * 2
def baseEnd_1294952 : Nat := 32836187679067789039241

theorem tailTrace_1294952 : CollatzResearch.WordTrace tailWord_1294952 prefixEnd_1294952 32836187679067789039241 := by
  unfold tailWord_1294952
  simp only [CollatzResearch.WordTrace]
  refine ⟨23615389802308769519623555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31487186403078359359498073 23615389802308769519623555)
  ·
    refine ⟨35423084703463154279435333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23615389802308769519623555 35423084703463154279435333)
    ·
      refine ⟨6641828381899341427394125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35423084703463154279435333 6641828381899341427394125)
      ·
        refine ⟨2490685643212253035272797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6641828381899341427394125 2490685643212253035272797)
        ·
          refine ⟨934007116204594888227299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2490685643212253035272797 934007116204594888227299)
          ·
            refine ⟨1401010674306892332340949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934007116204594888227299 1401010674306892332340949)
            ·
              refine ⟨32836187679067789039241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1401010674306892332340949 32836187679067789039241)
              ·
                rfl

theorem cell21_1294952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 7].length) (baseStart_1294952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1294952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1294952 prefixEnd_1294952 := by exact prefixLift 1294952
  have htrace : WordTrace (prefixWord ++ tailWord_1294952) baseStart_1294952 baseEnd_1294952 := by
    simpa [prefixWord, tailWord_1294952, baseEnd_1294952] using wordTrace_append hprefix tailTrace_1294952
  have hstable : (prefixWord ++ tailWord_1294952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1294952).length < 2 ^ (prefixWord ++ tailWord_1294952).sum := by decide
  have hdescent : baseEnd_1294952 < baseStart_1294952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1294952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295073 : List Nat := [1, 2, 3, 1, 4, 3, 1, 2, 4]
def baseStart_1295073 : Nat := 118140960795 + 1295073 * 2 ^ 59
def prefixEnd_1295073 : Nat := 4983230072969 + 3 ^ 40 * 1295073 * 2
def baseEnd_1295073 : Nat := 295553302960140779836255

theorem tailTrace_1295073 : CollatzResearch.WordTrace tailWord_1295073 prefixEnd_1295073 295553302960140779836255 := by
  unfold tailWord_1295073
  simp only [CollatzResearch.WordTrace]
  refine ⟨47235192837179176704401873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31490128558119451136267915 47235192837179176704401873)
  ·
    refine ⟨35426394627884382528301405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47235192837179176704401873 35426394627884382528301405)
    ·
      refine ⟨13284897985456643448113027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35426394627884382528301405 13284897985456643448113027)
      ·
        refine ⟨19927346978184965172169541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13284897985456643448113027 19927346978184965172169541)
        ·
          refine ⟨3736377558409680969781789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19927346978184965172169541 3736377558409680969781789)
          ·
            refine ⟨1401141584403630363668171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3736377558409680969781789 1401141584403630363668171)
            ·
              refine ⟨2101712376605445545502257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1401141584403630363668171 2101712376605445545502257)
              ·
                refine ⟨1576284282454084159126693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2101712376605445545502257 1576284282454084159126693)
                ·
                  refine ⟨295553302960140779836255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1576284282454084159126693 295553302960140779836255)
                  ·
                    rfl

theorem cell21_1295073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 4].length) (baseStart_1295073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1295073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1295073 prefixEnd_1295073 := by exact prefixLift 1295073
  have htrace : WordTrace (prefixWord ++ tailWord_1295073) baseStart_1295073 baseEnd_1295073 := by
    simpa [prefixWord, tailWord_1295073, baseEnd_1295073] using wordTrace_append hprefix tailTrace_1295073
  have hstable : (prefixWord ++ tailWord_1295073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295073).length < 2 ^ (prefixWord ++ tailWord_1295073).sum := by decide
  have hdescent : baseEnd_1295073 < baseStart_1295073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295135 : List Nat := [1, 1, 2, 4, 2, 3, 3, 2, 3]
def baseStart_1295135 : Nat := 118140960795 + 1295135 * 2 ^ 59
def prefixEnd_1295135 : Nat := 4983230072969 + 3 ^ 40 * 1295135 * 2
def baseEnd_1295135 : Nat := 295567452204842449802795

theorem tailTrace_1295135 : CollatzResearch.WordTrace tailWord_1295135 prefixEnd_1295135 295567452204842449802795 := by
  unfold tailWord_1295135
  simp only [CollatzResearch.WordTrace]
  refine ⟨47237454162954561293158859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31491636108636374195439239 47237454162954561293158859)
  ·
    refine ⟨70856181244431841939738289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47237454162954561293158859 70856181244431841939738289)
    ·
      refine ⟨53142135933323881454803717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70856181244431841939738289 53142135933323881454803717)
      ·
        refine ⟨9964150487498227772775697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53142135933323881454803717 9964150487498227772775697)
        ·
          refine ⟨7473112865623670829581773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9964150487498227772775697 7473112865623670829581773)
          ·
            refine ⟨2802417324608876561093165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7473112865623670829581773 2802417324608876561093165)
            ·
              refine ⟨1050906496728328710409937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2802417324608876561093165 1050906496728328710409937)
              ·
                refine ⟨788179872546246532807453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1050906496728328710409937 788179872546246532807453)
                ·
                  refine ⟨295567452204842449802795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 788179872546246532807453 295567452204842449802795)
                  ·
                    rfl

theorem cell21_1295135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 3].length) (baseStart_1295135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1295135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1295135 prefixEnd_1295135 := by exact prefixLift 1295135
  have htrace : WordTrace (prefixWord ++ tailWord_1295135) baseStart_1295135 baseEnd_1295135 := by
    simpa [prefixWord, tailWord_1295135, baseEnd_1295135] using wordTrace_append hprefix tailTrace_1295135
  have hstable : (prefixWord ++ tailWord_1295135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295135).length < 2 ^ (prefixWord ++ tailWord_1295135).sum := by decide
  have hdescent : baseEnd_1295135 < baseStart_1295135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295160 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 7]
def baseStart_1295160 : Nat := 118140960795 + 1295160 * 2 ^ 59
def prefixEnd_1295160 : Nat := 4983230072969 + 3 ^ 40 * 1295160 * 2
def baseEnd_1295160 : Nat := 295573157545447961886077

theorem tailTrace_1295160 : CollatzResearch.WordTrace tailWord_1295160 prefixEnd_1295160 295573157545447961886077 := by
  unfold tailWord_1295160
  simp only [CollatzResearch.WordTrace]
  refine ⟨23619182993931995281409467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31492243991909327041879289 23619182993931995281409467)
  ·
    refine ⟨35428774490897992922114201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23619182993931995281409467 35428774490897992922114201)
    ·
      refine ⟨26571580868173494691585651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35428774490897992922114201 26571580868173494691585651)
      ·
        refine ⟨39857371302260242037378477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26571580868173494691585651 39857371302260242037378477)
        ·
          refine ⟨14946514238347590764016929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39857371302260242037378477 14946514238347590764016929)
          ·
            refine ⟨11209885678760693073012697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14946514238347590764016929 11209885678760693073012697)
            ·
              refine ⟨8407414259070519804759523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11209885678760693073012697 8407414259070519804759523)
              ·
                refine ⟨12611121388605779707139285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8407414259070519804759523 12611121388605779707139285)
                ·
                  refine ⟨295573157545447961886077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12611121388605779707139285 295573157545447961886077)
                  ·
                    rfl

theorem cell21_1295160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_1295160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1295160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1295160 prefixEnd_1295160 := by exact prefixLift 1295160
  have htrace : WordTrace (prefixWord ++ tailWord_1295160) baseStart_1295160 baseEnd_1295160 := by
    simpa [prefixWord, tailWord_1295160, baseEnd_1295160] using wordTrace_append hprefix tailTrace_1295160
  have hstable : (prefixWord ++ tailWord_1295160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295160).length < 2 ^ (prefixWord ++ tailWord_1295160).sum := by decide
  have hdescent : baseEnd_1295160 < baseStart_1295160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295194 : List Nat := [3, 1, 1, 2, 1, 5, 1, 4, 3]
def baseStart_1295194 : Nat := 118140960795 + 1295194 * 2 ^ 59
def prefixEnd_1295194 : Nat := 4983230072969 + 3 ^ 40 * 1295194 * 2
def baseEnd_1295194 : Nat := 295580916808671458319341

theorem tailTrace_1295194 : CollatzResearch.WordTrace tailWord_1295194 prefixEnd_1295194 295580916808671458319341 := by
  unfold tailWord_1295194
  simp only [CollatzResearch.WordTrace]
  refine ⟨11809901517435203592389159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31493070713160542913037757 11809901517435203592389159)
  ·
    refine ⟨17714852276152805388583739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11809901517435203592389159 17714852276152805388583739)
    ·
      refine ⟨26572278414229208082875609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17714852276152805388583739 26572278414229208082875609)
      ·
        refine ⟨19929208810671906062156707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26572278414229208082875609 19929208810671906062156707)
        ·
          refine ⟨29893813216007859093235061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19929208810671906062156707 29893813216007859093235061)
          ·
            refine ⟨2802544989000736789990787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29893813216007859093235061 2802544989000736789990787)
            ·
              refine ⟨4203817483501105184986181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2802544989000736789990787 4203817483501105184986181)
              ·
                refine ⟨788215778156457222184909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4203817483501105184986181 788215778156457222184909)
                ·
                  refine ⟨295580916808671458319341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 788215778156457222184909 295580916808671458319341)
                  ·
                    rfl

theorem cell21_1295194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 3].length) (baseStart_1295194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1295194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1295194 prefixEnd_1295194 := by exact prefixLift 1295194
  have htrace : WordTrace (prefixWord ++ tailWord_1295194) baseStart_1295194 baseEnd_1295194 := by
    simpa [prefixWord, tailWord_1295194, baseEnd_1295194] using wordTrace_append hprefix tailTrace_1295194
  have hstable : (prefixWord ++ tailWord_1295194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295194).length < 2 ^ (prefixWord ++ tailWord_1295194).sum := by decide
  have hdescent : baseEnd_1295194 < baseStart_1295194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295208 : List Nat := [2, 1, 4, 2, 1, 2, 2, 3, 4]
def baseStart_1295208 : Nat := 118140960795 + 1295208 * 2 ^ 59
def prefixEnd_1295208 : Nat := 4983230072969 + 3 ^ 40 * 1295208 * 2
def baseEnd_1295208 : Nat := 295584111799410545085979

theorem tailTrace_1295208 : CollatzResearch.WordTrace tailWord_1295208 prefixEnd_1295208 295584111799410545085979 := by
  unfold tailWord_1295208
  simp only [CollatzResearch.WordTrace]
  refine ⟨23620058345845047380283139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31493411127793396507044185 23620058345845047380283139)
  ·
    refine ⟨35430087518767571070424709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23620058345845047380283139 35430087518767571070424709)
    ·
      refine ⟨6643141409768919575704633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35430087518767571070424709 6643141409768919575704633)
      ·
        refine ⟨4982356057326689681778475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6643141409768919575704633 4982356057326689681778475)
        ·
          refine ⟨7473534085990034522667713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4982356057326689681778475 7473534085990034522667713)
          ·
            refine ⟨5605150564492525892000785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7473534085990034522667713 5605150564492525892000785)
            ·
              refine ⟨4203862923369394419000589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5605150564492525892000785 4203862923369394419000589)
              ·
                refine ⟨1576448596263522907125221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4203862923369394419000589 1576448596263522907125221)
                ·
                  refine ⟨295584111799410545085979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1576448596263522907125221 295584111799410545085979)
                  ·
                    rfl

theorem cell21_1295208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 4].length) (baseStart_1295208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1295208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1295208 prefixEnd_1295208 := by exact prefixLift 1295208
  have htrace : WordTrace (prefixWord ++ tailWord_1295208) baseStart_1295208 baseEnd_1295208 := by
    simpa [prefixWord, tailWord_1295208, baseEnd_1295208] using wordTrace_append hprefix tailTrace_1295208
  have hstable : (prefixWord ++ tailWord_1295208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295208).length < 2 ^ (prefixWord ++ tailWord_1295208).sum := by decide
  have hdescent : baseEnd_1295208 < baseStart_1295208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295236 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 9]
def baseStart_1295236 : Nat := 118140960795 + 1295236 * 2 ^ 59
def prefixEnd_1295236 : Nat := 4983230072969 + 3 ^ 40 * 1295236 * 2
def baseEnd_1295236 : Nat := 295590501780888718619255

theorem tailTrace_1295236 : CollatzResearch.WordTrace tailWord_1295236 prefixEnd_1295236 295590501780888718619255 := by
  unfold tailWord_1295236
  simp only [CollatzResearch.WordTrace]
  refine ⟨23620568967794327771292781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31494091957059103695057041 23620568967794327771292781)
  ·
    refine ⟨8857713362922872914234793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23620568967794327771292781 8857713362922872914234793)
    ·
      refine ⟨6643285022192154685676095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8857713362922872914234793 6643285022192154685676095)
      ·
        refine ⟨9964927533288232028514143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6643285022192154685676095 9964927533288232028514143)
        ·
          refine ⟨14947391299932348042771215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9964927533288232028514143 14947391299932348042771215)
          ·
            refine ⟨22421086949898522064156823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14947391299932348042771215 22421086949898522064156823)
            ·
              refine ⟨33631630424847783096235235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22421086949898522064156823 33631630424847783096235235)
              ·
                refine ⟨50447445637271674644352853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33631630424847783096235235 50447445637271674644352853)
                ·
                  refine ⟨295590501780888718619255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50447445637271674644352853 295590501780888718619255)
                  ·
                    rfl

theorem cell21_1295236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_1295236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1295236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1295236 prefixEnd_1295236 := by exact prefixLift 1295236
  have htrace : WordTrace (prefixWord ++ tailWord_1295236) baseStart_1295236 baseEnd_1295236 := by
    simpa [prefixWord, tailWord_1295236, baseEnd_1295236] using wordTrace_append hprefix tailTrace_1295236
  have hstable : (prefixWord ++ tailWord_1295236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295236).length < 2 ^ (prefixWord ++ tailWord_1295236).sum := by decide
  have hdescent : baseEnd_1295236 < baseStart_1295236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295253 : List Nat := [1, 3, 2, 1, 1, 5, 2, 1, 5]
def baseStart_1295253 : Nat := 118140960795 + 1295253 * 2 ^ 59
def prefixEnd_1295253 : Nat := 4983230072969 + 3 ^ 40 * 1295253 * 2
def baseEnd_1295253 : Nat := 295594381412500466835887

theorem tailTrace_1295253 : CollatzResearch.WordTrace tailWord_1295253 prefixEnd_1295253 295594381412500466835887 := by
  unfold tailWord_1295253
  simp only [CollatzResearch.WordTrace]
  refine ⟨47241757976527067445954413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31494505317684711630636275 47241757976527067445954413)
  ·
    refine ⟨17715659241197650292232905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47241757976527067445954413 17715659241197650292232905)
    ·
      refine ⟨13286744430898237719174679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17715659241197650292232905 13286744430898237719174679)
      ·
        refine ⟨19930116646347356578762019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13286744430898237719174679 19930116646347356578762019)
        ·
          refine ⟨29895174969521034868143029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19930116646347356578762019 29895174969521034868143029)
          ·
            refine ⟨2802672653392597018888409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29895174969521034868143029 2802672653392597018888409)
            ·
              refine ⟨2102004490044447764166307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2802672653392597018888409 2102004490044447764166307)
              ·
                refine ⟨3153006735066671646249461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102004490044447764166307 3153006735066671646249461)
                ·
                  refine ⟨295594381412500466835887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3153006735066671646249461 295594381412500466835887)
                  ·
                    rfl

theorem cell21_1295253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_1295253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1295253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1295253 prefixEnd_1295253 := by exact prefixLift 1295253
  have htrace : WordTrace (prefixWord ++ tailWord_1295253) baseStart_1295253 baseEnd_1295253 := by
    simpa [prefixWord, tailWord_1295253, baseEnd_1295253] using wordTrace_append hprefix tailTrace_1295253
  have hstable : (prefixWord ++ tailWord_1295253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295253).length < 2 ^ (prefixWord ++ tailWord_1295253).sum := by decide
  have hdescent : baseEnd_1295253 < baseStart_1295253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295267 : List Nat := [1, 1, 1, 4, 1, 2, 2, 5, 4]
def baseStart_1295267 : Nat := 118140960795 + 1295267 * 2 ^ 59
def prefixEnd_1295267 : Nat := 4983230072969 + 3 ^ 40 * 1295267 * 2
def baseEnd_1295267 : Nat := 295597576403239553602525

theorem tailTrace_1295267 : CollatzResearch.WordTrace tailWord_1295267 prefixEnd_1295267 295597576403239553602525 := by
  unfold tailWord_1295267
  simp only [CollatzResearch.WordTrace]
  refine ⟨47242268598476347836964055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31494845732317565224642703 47242268598476347836964055)
  ·
    refine ⟨70863402897714521755446083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47242268598476347836964055 70863402897714521755446083)
    ·
      refine ⟨106295104346571782633169125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70863402897714521755446083 106295104346571782633169125)
      ·
        refine ⟨19930332064982209243719211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106295104346571782633169125 19930332064982209243719211)
        ·
          refine ⟨29895498097473313865578817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19930332064982209243719211 29895498097473313865578817)
          ·
            refine ⟨22421623573104985399184113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29895498097473313865578817 22421623573104985399184113)
            ·
              refine ⟨16816217679828739049388085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22421623573104985399184113 16816217679828739049388085)
              ·
                refine ⟨1576520407483944285880133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16816217679828739049388085 1576520407483944285880133)
                ·
                  refine ⟨295597576403239553602525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1576520407483944285880133 295597576403239553602525)
                  ·
                    rfl

theorem cell21_1295267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5, 4].length) (baseStart_1295267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1295267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1295267 prefixEnd_1295267 := by exact prefixLift 1295267
  have htrace : WordTrace (prefixWord ++ tailWord_1295267) baseStart_1295267 baseEnd_1295267 := by
    simpa [prefixWord, tailWord_1295267, baseEnd_1295267] using wordTrace_append hprefix tailTrace_1295267
  have hstable : (prefixWord ++ tailWord_1295267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295267).length < 2 ^ (prefixWord ++ tailWord_1295267).sum := by decide
  have hdescent : baseEnd_1295267 < baseStart_1295267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295318 : List Nat := [5, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_1295318 : Nat := 118140960795 + 1295318 * 2 ^ 59
def prefixEnd_1295318 : Nat := 4983230072969 + 3 ^ 40 * 1295318 * 2
def baseEnd_1295318 : Nat := 295609215298074798252421

theorem tailTrace_1295318 : CollatzResearch.WordTrace tailWord_1295318 prefixEnd_1295318 295609215298074798252421 := by
  unfold tailWord_1295318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2952758045080723971691913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31496085814194389031380405 2952758045080723971691913)
  ·
    refine ⟨2214568533810542978768935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2952758045080723971691913 2214568533810542978768935)
    ·
      refine ⟨3321852800715814468153403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2214568533810542978768935 3321852800715814468153403)
      ·
        refine ⟨4982779201073721702230105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3321852800715814468153403 4982779201073721702230105)
        ·
          refine ⟨3737084400805291276672579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4982779201073721702230105 3737084400805291276672579)
          ·
            refine ⟨5605626601207936915008869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3737084400805291276672579 5605626601207936915008869)
            ·
              refine ⟨1051054987726488171564163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5605626601207936915008869 1051054987726488171564163)
              ·
                refine ⟨1576582481589732257346245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051054987726488171564163 1576582481589732257346245)
                ·
                  refine ⟨295609215298074798252421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1576582481589732257346245 295609215298074798252421)
                  ·
                    rfl

theorem cell21_1295318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_1295318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1295318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1295318 prefixEnd_1295318 := by exact prefixLift 1295318
  have htrace : WordTrace (prefixWord ++ tailWord_1295318) baseStart_1295318 baseEnd_1295318 := by
    simpa [prefixWord, tailWord_1295318, baseEnd_1295318] using wordTrace_append hprefix tailTrace_1295318
  have hstable : (prefixWord ++ tailWord_1295318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295318).length < 2 ^ (prefixWord ++ tailWord_1295318).sum := by decide
  have hdescent : baseEnd_1295318 < baseStart_1295318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295374 : List Nat := [4, 1, 1, 2, 2, 2, 3, 6]
def baseStart_1295374 : Nat := 118140960795 + 1295374 * 2 ^ 59
def prefixEnd_1295374 : Nat := 4983230072969 + 3 ^ 40 * 1295374 * 2
def baseEnd_1295374 : Nat := 98540665087010381772991

theorem tailTrace_1295374 : CollatzResearch.WordTrace tailWord_1295374 prefixEnd_1295374 98540665087010381772991 := by
  unfold tailWord_1295374
  simp only [CollatzResearch.WordTrace]
  refine ⟨5905771401136088138888647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31497447472725803407406117 5905771401136088138888647)
  ·
    refine ⟨8858657101704132208332971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5905771401136088138888647 8858657101704132208332971)
    ·
      refine ⟨13287985652556198312499457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8858657101704132208332971 13287985652556198312499457)
      ·
        refine ⟨9965989239417148734374593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13287985652556198312499457 9965989239417148734374593)
        ·
          refine ⟨7474491929562861550780945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9965989239417148734374593 7474491929562861550780945)
          ·
            refine ⟨5605868947172146163085709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7474491929562861550780945 5605868947172146163085709)
            ·
              refine ⟨2102200855189554811157141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5605868947172146163085709 2102200855189554811157141)
              ·
                refine ⟨98540665087010381772991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2102200855189554811157141 98540665087010381772991)
                ·
                  rfl

theorem cell21_1295374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_1295374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1295374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1295374 prefixEnd_1295374 := by exact prefixLift 1295374
  have htrace : WordTrace (prefixWord ++ tailWord_1295374) baseStart_1295374 baseEnd_1295374 := by
    simpa [prefixWord, tailWord_1295374, baseEnd_1295374] using wordTrace_append hprefix tailTrace_1295374
  have hstable : (prefixWord ++ tailWord_1295374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295374).length < 2 ^ (prefixWord ++ tailWord_1295374).sum := by decide
  have hdescent : baseEnd_1295374 < baseStart_1295374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295422 : List Nat := [4, 2, 1, 3, 1, 2, 2, 1, 5]
def baseStart_1295422 : Nat := 118140960795 + 1295422 * 2 ^ 59
def prefixEnd_1295422 : Nat := 4983230072969 + 3 ^ 40 * 1295422 * 2
def baseEnd_1295422 : Nat := 295632949514993728518875

theorem tailTrace_1295422 : CollatzResearch.WordTrace tailWord_1295422 prefixEnd_1295422 295632949514993728518875 := by
  unfold tailWord_1295422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5905990239114351163607065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31498614608609872872571013 5905990239114351163607065)
  ·
    refine ⟨4429492679335763372705299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5905990239114351163607065 4429492679335763372705299)
    ·
      refine ⟨6644239019003645059057949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4429492679335763372705299 6644239019003645059057949)
      ·
        refine ⟨2491589632126366897146731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6644239019003645059057949 2491589632126366897146731)
        ·
          refine ⟨3737384448189550345720097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2491589632126366897146731 3737384448189550345720097)
          ·
            refine ⟨2803038336142162759290073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3737384448189550345720097 2803038336142162759290073)
            ·
              refine ⟨2102278752106622069467555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2803038336142162759290073 2102278752106622069467555)
              ·
                refine ⟨3153418128159933104201333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102278752106622069467555 3153418128159933104201333)
                ·
                  refine ⟨295632949514993728518875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3153418128159933104201333 295632949514993728518875)
                  ·
                    rfl

theorem cell21_1295422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_1295422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1295422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1295422 prefixEnd_1295422 := by exact prefixLift 1295422
  have htrace : WordTrace (prefixWord ++ tailWord_1295422) baseStart_1295422 baseEnd_1295422 := by
    simpa [prefixWord, tailWord_1295422, baseEnd_1295422] using wordTrace_append hprefix tailTrace_1295422
  have hstable : (prefixWord ++ tailWord_1295422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295422).length < 2 ^ (prefixWord ++ tailWord_1295422).sum := by decide
  have hdescent : baseEnd_1295422 < baseStart_1295422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295585 : List Nat := [1, 2, 3, 1, 3, 3, 8]
def baseStart_1295585 : Nat := 118140960795 + 1295585 * 2 ^ 59
def prefixEnd_1295585 : Nat := 4983230072969 + 3 ^ 40 * 1295585 * 2
def baseEnd_1295585 : Nat := 32852238703971296366875

theorem tailTrace_1295585 : CollatzResearch.WordTrace tailWord_1295585 prefixEnd_1295585 32852238703971296366875 := by
  unfold tailWord_1295585
  simp only [CollatzResearch.WordTrace]
  refine ⟨47253867011324288147040209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31502578007549525431360139 47253867011324288147040209)
  ·
    refine ⟨35440400258493216110280157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47253867011324288147040209 35440400258493216110280157)
    ·
      refine ⟨13290150096934956041355059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35440400258493216110280157 13290150096934956041355059)
      ·
        refine ⟨19935225145402434062032589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13290150096934956041355059 19935225145402434062032589)
        ·
          refine ⟨7475709429525912773262221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19935225145402434062032589 7475709429525912773262221)
          ·
            refine ⟨2803391036072217289973333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7475709429525912773262221 2803391036072217289973333)
            ·
              refine ⟨32852238703971296366875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2803391036072217289973333 32852238703971296366875)
              ·
                rfl

theorem cell21_1295585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 8].length) (baseStart_1295585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1295585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1295585 prefixEnd_1295585 := by exact prefixLift 1295585
  have htrace : WordTrace (prefixWord ++ tailWord_1295585) baseStart_1295585 baseEnd_1295585 := by
    simpa [prefixWord, tailWord_1295585, baseEnd_1295585] using wordTrace_append hprefix tailTrace_1295585
  have hstable : (prefixWord ++ tailWord_1295585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295585).length < 2 ^ (prefixWord ++ tailWord_1295585).sum := by decide
  have hdescent : baseEnd_1295585 < baseStart_1295585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295650 : List Nat := [3, 3, 1, 1, 4, 2, 1, 1, 5]
def baseStart_1295650 : Nat := 118140960795 + 1295650 * 2 ^ 59
def prefixEnd_1295650 : Nat := 4983230072969 + 3 ^ 40 * 1295650 * 2
def baseEnd_1295650 : Nat := 295684982221315998718409

theorem tailTrace_1295650 : CollatzResearch.WordTrace tailWord_1295650 prefixEnd_1295650 295684982221315998718409 := by
  unfold tailWord_1295650
  simp only [CollatzResearch.WordTrace]
  refine ⟨11814059439022201062039101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31504158504059202832104269 11814059439022201062039101)
  ·
    refine ⟨4430272289633325398264663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11814059439022201062039101 4430272289633325398264663)
    ·
      refine ⟨6645408434449988097396995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4430272289633325398264663 6645408434449988097396995)
      ·
        refine ⟨9968112651674982146095493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6645408434449988097396995 9968112651674982146095493)
        ·
          refine ⟨1869021122189059152392905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9968112651674982146095493 1869021122189059152392905)
          ·
            refine ⟨1401765841641794364294679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1869021122189059152392905 1401765841641794364294679)
            ·
              refine ⟨2102648762462691546442019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1401765841641794364294679 2102648762462691546442019)
              ·
                refine ⟨3153973143694037319663029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102648762462691546442019 3153973143694037319663029)
                ·
                  refine ⟨295684982221315998718409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3153973143694037319663029 295684982221315998718409)
                  ·
                    rfl

theorem cell21_1295650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_1295650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1295650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1295650 prefixEnd_1295650 := by exact prefixLift 1295650
  have htrace : WordTrace (prefixWord ++ tailWord_1295650) baseStart_1295650 baseEnd_1295650 := by
    simpa [prefixWord, tailWord_1295650, baseEnd_1295650] using wordTrace_append hprefix tailTrace_1295650
  have hstable : (prefixWord ++ tailWord_1295650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295650).length < 2 ^ (prefixWord ++ tailWord_1295650).sum := by decide
  have hdescent : baseEnd_1295650 < baseStart_1295650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295706 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 6]
def baseStart_1295706 : Nat := 118140960795 + 1295706 * 2 ^ 59
def prefixEnd_1295706 : Nat := 4983230072969 + 3 ^ 40 * 1295706 * 2
def baseEnd_1295706 : Nat := 295697762184272345784961

theorem tailTrace_1295706 : CollatzResearch.WordTrace tailWord_1295706 prefixEnd_1295706 295697762184272345784961 := by
  unfold tailWord_1295706
  simp only [CollatzResearch.WordTrace]
  refine ⟨11814570060971481453048743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31505520162590617208129981 11814570060971481453048743)
  ·
    refine ⟨17721855091457222179573115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11814570060971481453048743 17721855091457222179573115)
    ·
      refine ⟨26582782637185833269359673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17721855091457222179573115 26582782637185833269359673)
      ·
        refine ⟨19937086977889374952019755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26582782637185833269359673 19937086977889374952019755)
        ·
          refine ⟨29905630466834062428029633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19937086977889374952019755 29905630466834062428029633)
          ·
            refine ⟨22429222850125546821022225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29905630466834062428029633 22429222850125546821022225)
            ·
              refine ⟨16821917137594160115766669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22429222850125546821022225 16821917137594160115766669)
              ·
                refine ⟨6308218926597810043412501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16821917137594160115766669 6308218926597810043412501)
                ·
                  refine ⟨295697762184272345784961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6308218926597810043412501 295697762184272345784961)
                  ·
                    rfl

theorem cell21_1295706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_1295706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1295706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1295706 prefixEnd_1295706 := by exact prefixLift 1295706
  have htrace : WordTrace (prefixWord ++ tailWord_1295706) baseStart_1295706 baseEnd_1295706 := by
    simpa [prefixWord, tailWord_1295706, baseEnd_1295706] using wordTrace_append hprefix tailTrace_1295706
  have hstable : (prefixWord ++ tailWord_1295706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295706).length < 2 ^ (prefixWord ++ tailWord_1295706).sum := by decide
  have hdescent : baseEnd_1295706 < baseStart_1295706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295726 : List Nat := [4, 1, 2, 4, 1, 1, 1, 2, 5]
def baseStart_1295726 : Nat := 118140960795 + 1295726 * 2 ^ 59
def prefixEnd_1295726 : Nat := 4983230072969 + 3 ^ 40 * 1295726 * 2
def baseEnd_1295726 : Nat := 295702326456756755451587

theorem tailTrace_1295726 : CollatzResearch.WordTrace tailWord_1295726 prefixEnd_1295726 295702326456756755451587 := by
  unfold tailWord_1295726
  simp only [CollatzResearch.WordTrace]
  refine ⟨5907376212976683653490379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31506006469208979485282021 5907376212976683653490379)
  ·
    refine ⟨8861064319465025480235569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5907376212976683653490379 8861064319465025480235569)
    ·
      refine ⟨6645798239598769110176677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8861064319465025480235569 6645798239598769110176677)
      ·
        refine ⟨1246087169924769208158127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6645798239598769110176677 1246087169924769208158127)
        ·
          refine ⟨1869130754887153812237191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246087169924769208158127 1869130754887153812237191)
          ·
            refine ⟨2803696132330730718355787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869130754887153812237191 2803696132330730718355787)
            ·
              refine ⟨4205544198496096077533681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2803696132330730718355787 4205544198496096077533681)
              ·
                refine ⟨3154158148872072058150261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4205544198496096077533681 3154158148872072058150261)
                ·
                  refine ⟨295702326456756755451587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3154158148872072058150261 295702326456756755451587)
                  ·
                    rfl

theorem cell21_1295726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_1295726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1295726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1295726 prefixEnd_1295726 := by exact prefixLift 1295726
  have htrace : WordTrace (prefixWord ++ tailWord_1295726) baseStart_1295726 baseEnd_1295726 := by
    simpa [prefixWord, tailWord_1295726, baseEnd_1295726] using wordTrace_append hprefix tailTrace_1295726
  have hstable : (prefixWord ++ tailWord_1295726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295726).length < 2 ^ (prefixWord ++ tailWord_1295726).sum := by decide
  have hdescent : baseEnd_1295726 < baseStart_1295726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295774 : List Nat := [4, 3, 1, 2, 2, 1, 3, 1, 4]
def baseStart_1295774 : Nat := 118140960795 + 1295774 * 2 ^ 59
def prefixEnd_1295774 : Nat := 4983230072969 + 3 ^ 40 * 1295774 * 2
def baseEnd_1295774 : Nat := 295713280710719338651489

theorem tailTrace_1295774 : CollatzResearch.WordTrace tailWord_1295774 prefixEnd_1295774 295713280710719338651489 := by
  unfold tailWord_1295774
  simp only [CollatzResearch.WordTrace]
  refine ⟨5907595050954946678208797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31507173605093048950446917 5907595050954946678208797)
  ·
    refine ⟨2215348144108105004328299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5907595050954946678208797 2215348144108105004328299)
    ·
      refine ⟨3323022216162157506492449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2215348144108105004328299 3323022216162157506492449)
      ·
        refine ⟨2492266662121618129869337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3323022216162157506492449 2492266662121618129869337)
        ·
          refine ⟨1869199996591213597402003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2492266662121618129869337 1869199996591213597402003)
          ·
            refine ⟨2803799994886820396103005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869199996591213597402003 2803799994886820396103005)
            ·
              refine ⟨1051424998082557648538627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2803799994886820396103005 1051424998082557648538627)
              ·
                refine ⟨1577137497123836472807941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051424998082557648538627 1577137497123836472807941)
                ·
                  refine ⟨295713280710719338651489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1577137497123836472807941 295713280710719338651489)
                  ·
                    rfl

theorem cell21_1295774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_1295774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1295774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1295774 prefixEnd_1295774 := by exact prefixLift 1295774
  have htrace : WordTrace (prefixWord ++ tailWord_1295774) baseStart_1295774 baseEnd_1295774 := by
    simpa [prefixWord, tailWord_1295774, baseEnd_1295774] using wordTrace_append hprefix tailTrace_1295774
  have hstable : (prefixWord ++ tailWord_1295774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295774).length < 2 ^ (prefixWord ++ tailWord_1295774).sum := by decide
  have hdescent : baseEnd_1295774 < baseStart_1295774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295830 : List Nat := [5, 2, 1, 1, 1, 2, 1, 8]
def baseStart_1295830 : Nat := 118140960795 + 1295830 * 2 ^ 59
def prefixEnd_1295830 : Nat := 4983230072969 + 3 ^ 40 * 1295830 * 2
def baseEnd_1295830 : Nat := 98575353557891895239347

theorem tailTrace_1295830 : CollatzResearch.WordTrace tailWord_1295830 prefixEnd_1295830 98575353557891895239347 := by
  unfold tailWord_1295830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2953925180964793436856809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31508535263624463326472629 2953925180964793436856809)
  ·
    refine ⟨2215443885723595077642607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2953925180964793436856809 2215443885723595077642607)
    ·
      refine ⟨3323165828585392616463911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2215443885723595077642607 3323165828585392616463911)
      ·
        refine ⟨4984748742878088924695867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3323165828585392616463911 4984748742878088924695867)
        ·
          refine ⟨7477123114317133387043801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4984748742878088924695867 7477123114317133387043801)
          ·
            refine ⟨5607842335737850040282851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7477123114317133387043801 5607842335737850040282851)
            ·
              refine ⟨8411763503606775060424277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5607842335737850040282851 8411763503606775060424277)
              ·
                refine ⟨98575353557891895239347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8411763503606775060424277 98575353557891895239347)
                ·
                  rfl

theorem cell21_1295830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_1295830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1295830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1295830 prefixEnd_1295830 := by exact prefixLift 1295830
  have htrace : WordTrace (prefixWord ++ tailWord_1295830) baseStart_1295830 baseEnd_1295830 := by
    simpa [prefixWord, tailWord_1295830, baseEnd_1295830] using wordTrace_append hprefix tailTrace_1295830
  have hstable : (prefixWord ++ tailWord_1295830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295830).length < 2 ^ (prefixWord ++ tailWord_1295830).sum := by decide
  have hdescent : baseEnd_1295830 < baseStart_1295830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295903 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 7]
def baseStart_1295903 : Nat := 118140960795 + 1295903 * 2 ^ 59
def prefixEnd_1295903 : Nat := 4983230072969 + 3 ^ 40 * 1295903 * 2
def baseEnd_1295903 : Nat := 295742720268243781001225

theorem tailTrace_1295903 : CollatzResearch.WordTrace tailWord_1295903 prefixEnd_1295903 295742720268243781001225 := by
  unfold tailWord_1295903
  simp only [CollatzResearch.WordTrace]
  refine ⟨47265465424172228457116363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31510310282781485638077575 47265465424172228457116363)
  ·
    refine ⟨70898198136258342685674545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47265465424172228457116363 70898198136258342685674545)
    ·
      refine ⟨53173648602193757014255909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70898198136258342685674545 53173648602193757014255909)
      ·
        refine ⟨9970059112911329440172983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53173648602193757014255909 9970059112911329440172983)
        ·
          refine ⟨14955088669366994160259475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9970059112911329440172983 14955088669366994160259475)
          ·
            refine ⟨22432633004050491240389213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14955088669366994160259475 22432633004050491240389213)
            ·
              refine ⟨8412237376518934215145955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22432633004050491240389213 8412237376518934215145955)
              ·
                refine ⟨12618356064778401322718933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8412237376518934215145955 12618356064778401322718933)
                ·
                  refine ⟨295742720268243781001225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12618356064778401322718933 295742720268243781001225)
                  ·
                    rfl

theorem cell21_1295903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 7].length) (baseStart_1295903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1295903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1295903 prefixEnd_1295903 := by exact prefixLift 1295903
  have htrace : WordTrace (prefixWord ++ tailWord_1295903) baseStart_1295903 baseEnd_1295903 := by
    simpa [prefixWord, tailWord_1295903, baseEnd_1295903] using wordTrace_append hprefix tailTrace_1295903
  have hstable : (prefixWord ++ tailWord_1295903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295903).length < 2 ^ (prefixWord ++ tailWord_1295903).sum := by decide
  have hdescent : baseEnd_1295903 < baseStart_1295903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295926 : List Nat := [5, 1, 2, 1, 4, 1, 1, 2, 4]
def baseStart_1295926 : Nat := 118140960795 + 1295926 * 2 ^ 59
def prefixEnd_1295926 : Nat := 4983230072969 + 3 ^ 40 * 1295926 * 2
def baseEnd_1295926 : Nat := 295747969181600852117845

theorem tailTrace_1295926 : CollatzResearch.WordTrace tailWord_1295926 prefixEnd_1295926 295747969181600852117845 := by
  unfold tailWord_1295926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2954144018943056461575227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31510869535392602256802421 2954144018943056461575227)
  ·
    refine ⟨4431216028414584692362841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2954144018943056461575227 4431216028414584692362841)
    ·
      refine ⟨3323412021310938519272131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4431216028414584692362841 3323412021310938519272131)
      ·
        refine ⟨4985118031966407778908197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3323412021310938519272131 4985118031966407778908197)
        ·
          refine ⟨934709630993701458545287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4985118031966407778908197 934709630993701458545287)
          ·
            refine ⟨1402064446490552187817931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 934709630993701458545287 1402064446490552187817931)
            ·
              refine ⟨2103096669735828281726897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1402064446490552187817931 2103096669735828281726897)
              ·
                refine ⟨1577322502301871211295173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2103096669735828281726897 1577322502301871211295173)
                ·
                  refine ⟨295747969181600852117845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1577322502301871211295173 295747969181600852117845)
                  ·
                    rfl

theorem cell21_1295926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_1295926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1295926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1295926 prefixEnd_1295926 := by exact prefixLift 1295926
  have htrace : WordTrace (prefixWord ++ tailWord_1295926) baseStart_1295926 baseEnd_1295926 := by
    simpa [prefixWord, tailWord_1295926, baseEnd_1295926] using wordTrace_append hprefix tailTrace_1295926
  have hstable : (prefixWord ++ tailWord_1295926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295926).length < 2 ^ (prefixWord ++ tailWord_1295926).sum := by decide
  have hdescent : baseEnd_1295926 < baseStart_1295926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295937 : List Nat := [1, 2, 5, 1, 1, 1, 1, 6, 3]
def baseStart_1295937 : Nat := 118140960795 + 1295937 * 2 ^ 59
def prefixEnd_1295937 : Nat := 4983230072969 + 3 ^ 40 * 1295937 * 2
def baseEnd_1295937 : Nat := 295750479531467277434489

theorem tailTrace_1295937 : CollatzResearch.WordTrace tailWord_1295937 prefixEnd_1295937 295750479531467277434489 := by
  unfold tailWord_1295937
  simp only [CollatzResearch.WordTrace]
  refine ⟨47266705506049052263854065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31511137004032701509236043 47266705506049052263854065)
  ·
    refine ⟨35450029129536789197890549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47266705506049052263854065 35450029129536789197890549)
    ·
      refine ⟨3323440230894073987302239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35450029129536789197890549 3323440230894073987302239)
      ·
        refine ⟨4985160346341110980953359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3323440230894073987302239 4985160346341110980953359)
        ·
          refine ⟨7477740519511666471430039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4985160346341110980953359 7477740519511666471430039)
          ·
            refine ⟨11216610779267499707145059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7477740519511666471430039 11216610779267499707145059)
            ·
              refine ⟨16824916168901249560717589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11216610779267499707145059 16824916168901249560717589)
              ·
                refine ⟨788667945417246073158637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16824916168901249560717589 788667945417246073158637)
                ·
                  refine ⟨295750479531467277434489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 788667945417246073158637 295750479531467277434489)
                  ·
                    rfl

theorem cell21_1295937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 3].length) (baseStart_1295937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1295937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1295937 prefixEnd_1295937 := by exact prefixLift 1295937
  have htrace : WordTrace (prefixWord ++ tailWord_1295937) baseStart_1295937 baseEnd_1295937 := by
    simpa [prefixWord, tailWord_1295937, baseEnd_1295937] using wordTrace_append hprefix tailTrace_1295937
  have hstable : (prefixWord ++ tailWord_1295937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295937).length < 2 ^ (prefixWord ++ tailWord_1295937).sum := by decide
  have hdescent : baseEnd_1295937 < baseStart_1295937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1295982 : List Nat := [4, 1, 2, 2, 3, 2, 7]
def baseStart_1295982 : Nat := 118140960795 + 1295982 * 2 ^ 59
def prefixEnd_1295982 : Nat := 4983230072969 + 3 ^ 40 * 1295982 * 2
def baseEnd_1295982 : Nat := 32862305460506355464933

theorem tailTrace_1295982 : CollatzResearch.WordTrace tailWord_1295982 prefixEnd_1295982 32862305460506355464933 := by
  unfold tailWord_1295982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5908543348860753118655275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31512231193924016632828133 5908543348860753118655275)
  ·
    refine ⟨8862815023291129677982913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5908543348860753118655275 8862815023291129677982913)
    ·
      refine ⟨6647111267468347258487185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8862815023291129677982913 6647111267468347258487185)
      ·
        refine ⟨4985333450601260443865389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6647111267468347258487185 4985333450601260443865389)
        ·
          refine ⟨1869500043975472666449521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4985333450601260443865389 1869500043975472666449521)
          ·
            refine ⟨1402125032981604499837141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1869500043975472666449521 1402125032981604499837141)
            ·
              refine ⟨32862305460506355464933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1402125032981604499837141 32862305460506355464933)
              ·
                rfl

theorem cell21_1295982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 7].length) (baseStart_1295982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1295982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1295982 prefixEnd_1295982 := by exact prefixLift 1295982
  have htrace : WordTrace (prefixWord ++ tailWord_1295982) baseStart_1295982 baseEnd_1295982 := by
    simpa [prefixWord, tailWord_1295982, baseEnd_1295982] using wordTrace_append hprefix tailTrace_1295982
  have hstable : (prefixWord ++ tailWord_1295982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1295982).length < 2 ^ (prefixWord ++ tailWord_1295982).sum := by decide
  have hdescent : baseEnd_1295982 < baseStart_1295982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1295982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296089 : List Nat := [1, 2, 1, 2, 3, 4, 2, 3, 3]
def baseStart_1296089 : Nat := 118140960795 + 1296089 * 2 ^ 59
def prefixEnd_1296089 : Nat := 4983230072969 + 3 ^ 40 * 1296089 * 2
def baseEnd_1296089 : Nat := 295785168002348790900845

theorem tailTrace_1296089 : CollatzResearch.WordTrace tailWord_1296089 prefixEnd_1296089 295785168002348790900845 := by
  unfold tailWord_1296089
  simp only [CollatzResearch.WordTrace]
  refine ⟨47272249401498382223387321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31514832934332254815591547 47272249401498382223387321)
  ·
    refine ⟨35454187051123786667540491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47272249401498382223387321 35454187051123786667540491)
    ·
      refine ⟨53181280576685680001310737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35454187051123786667540491 53181280576685680001310737)
      ·
        refine ⟨39885960432514260000983053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53181280576685680001310737 39885960432514260000983053)
        ·
          refine ⟨14957235162192847500368645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39885960432514260000983053 14957235162192847500368645)
          ·
            refine ⟨2804481592911158906319121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14957235162192847500368645 2804481592911158906319121)
            ·
              refine ⟨2103361194683369179739341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2804481592911158906319121 2103361194683369179739341)
              ·
                refine ⟨788760448006263442402253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2103361194683369179739341 788760448006263442402253)
                ·
                  refine ⟨295785168002348790900845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 788760448006263442402253 295785168002348790900845)
                  ·
                    rfl

theorem cell21_1296089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 3, 3].length) (baseStart_1296089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1296089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1296089 prefixEnd_1296089 := by exact prefixLift 1296089
  have htrace : WordTrace (prefixWord ++ tailWord_1296089) baseStart_1296089 baseEnd_1296089 := by
    simpa [prefixWord, tailWord_1296089, baseEnd_1296089] using wordTrace_append hprefix tailTrace_1296089
  have hstable : (prefixWord ++ tailWord_1296089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296089).length < 2 ^ (prefixWord ++ tailWord_1296089).sum := by decide
  have hdescent : baseEnd_1296089 < baseStart_1296089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296100 : List Nat := [2, 3, 1, 1, 1, 3, 10]
def baseStart_1296100 : Nat := 118140960795 + 1296100 * 2 ^ 59
def prefixEnd_1296100 : Nat := 4983230072969 + 3 ^ 40 * 1296100 * 2
def baseEnd_1296100 : Nat := 32865297594690579579721

theorem tailTrace_1296100 : CollatzResearch.WordTrace tailWord_1296100 prefixEnd_1296100 32865297594690579579721 := by
  unfold tailWord_1296100
  simp only [CollatzResearch.WordTrace]
  refine ⟨23636325302229265551018877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31515100402972354068025169 23636325302229265551018877)
  ·
    refine ⟨8863621988335974581632079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23636325302229265551018877 8863621988335974581632079)
    ·
      refine ⟨13295432982503961872448119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8863621988335974581632079 13295432982503961872448119)
      ·
        refine ⟨19943149473755942808672179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13295432982503961872448119 19943149473755942808672179)
        ·
          refine ⟨29914724210633914213008269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19943149473755942808672179 29914724210633914213008269)
          ·
            refine ⟨11218021578987717829878101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29914724210633914213008269 11218021578987717829878101)
            ·
              refine ⟨32865297594690579579721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11218021578987717829878101 32865297594690579579721)
              ·
                rfl

theorem cell21_1296100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 10].length) (baseStart_1296100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1296100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1296100 prefixEnd_1296100 := by exact prefixLift 1296100
  have htrace : WordTrace (prefixWord ++ tailWord_1296100) baseStart_1296100 baseEnd_1296100 := by
    simpa [prefixWord, tailWord_1296100, baseEnd_1296100] using wordTrace_append hprefix tailTrace_1296100
  have hstable : (prefixWord ++ tailWord_1296100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296100).length < 2 ^ (prefixWord ++ tailWord_1296100).sum := by decide
  have hdescent : baseEnd_1296100 < baseStart_1296100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296131 : List Nat := [1, 1, 1, 3, 2, 2, 4, 2, 5]
def baseStart_1296131 : Nat := 118140960795 + 1296131 * 2 ^ 59
def prefixEnd_1296131 : Nat := 4983230072969 + 3 ^ 40 * 1296131 * 2
def baseEnd_1296131 : Nat := 295794752974566051200759

theorem tailTrace_1296131 : CollatzResearch.WordTrace tailWord_1296131 prefixEnd_1296131 295794752974566051200759 := by
  unfold tailWord_1296131
  simp only [CollatzResearch.WordTrace]
  refine ⟨47273781267346223396416247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31515854178230815597610831 47273781267346223396416247)
  ·
    refine ⟨70910671901019335094624371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47273781267346223396416247 70910671901019335094624371)
    ·
      refine ⟨106366007851529002641936557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70910671901019335094624371 106366007851529002641936557)
      ·
        refine ⟨39887252944323375990726209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106366007851529002641936557 39887252944323375990726209)
        ·
          refine ⟨29915439708242531993044657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39887252944323375990726209 29915439708242531993044657)
          ·
            refine ⟨22436579781181898994783493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29915439708242531993044657 22436579781181898994783493)
            ·
              refine ⟨4206858708971606061521905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22436579781181898994783493 4206858708971606061521905)
              ·
                refine ⟨3155144031728704546141429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4206858708971606061521905 3155144031728704546141429)
                ·
                  refine ⟨295794752974566051200759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3155144031728704546141429 295794752974566051200759)
                  ·
                    rfl

theorem cell21_1296131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 5].length) (baseStart_1296131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1296131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1296131 prefixEnd_1296131 := by exact prefixLift 1296131
  have htrace : WordTrace (prefixWord ++ tailWord_1296131) baseStart_1296131 baseEnd_1296131 := by
    simpa [prefixWord, tailWord_1296131, baseEnd_1296131] using wordTrace_append hprefix tailTrace_1296131
  have hstable : (prefixWord ++ tailWord_1296131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296131).length < 2 ^ (prefixWord ++ tailWord_1296131).sum := by decide
  have hdescent : baseEnd_1296131 < baseStart_1296131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296162 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 6]
def baseStart_1296162 : Nat := 118140960795 + 1296162 * 2 ^ 59
def prefixEnd_1296162 : Nat := 4983230072969 + 3 ^ 40 * 1296162 * 2
def baseEnd_1296162 : Nat := 295801827596916886184029

theorem tailTrace_1296162 : CollatzResearch.WordTrace tailWord_1296162 prefixEnd_1296162 295801827596916886184029 := by
  unfold tailWord_1296162
  simp only [CollatzResearch.WordTrace]
  refine ⟨11818727982558478922698685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31516607953489277127196493 11818727982558478922698685)
  ·
    refine ⟨4432022993459429596012007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11818727982558478922698685 4432022993459429596012007)
    ·
      refine ⟨6648034490189144394018011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4432022993459429596012007 6648034490189144394018011)
      ·
        refine ⟨9972051735283716591027017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6648034490189144394018011 9972051735283716591027017)
        ·
          refine ⟨7479038801462787443270263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9972051735283716591027017 7479038801462787443270263)
          ·
            refine ⟨11218558202194181164905395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7479038801462787443270263 11218558202194181164905395)
            ·
              refine ⟨16827837303291271747358093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11218558202194181164905395 16827837303291271747358093)
              ·
                refine ⟨6310438988734226905259285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16827837303291271747358093 6310438988734226905259285)
                ·
                  refine ⟨295801827596916886184029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6310438988734226905259285 295801827596916886184029)
                  ·
                    rfl

theorem cell21_1296162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_1296162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1296162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1296162 prefixEnd_1296162 := by exact prefixLift 1296162
  have htrace : WordTrace (prefixWord ++ tailWord_1296162) baseStart_1296162 baseEnd_1296162 := by
    simpa [prefixWord, tailWord_1296162, baseEnd_1296162] using wordTrace_append hprefix tailTrace_1296162
  have hstable : (prefixWord ++ tailWord_1296162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296162).length < 2 ^ (prefixWord ++ tailWord_1296162).sum := by decide
  have hdescent : baseEnd_1296162 < baseStart_1296162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296179 : List Nat := [1, 1, 1, 2, 7, 1, 1, 3, 4]
def baseStart_1296179 : Nat := 118140960795 + 1296179 * 2 ^ 59
def prefixEnd_1296179 : Nat := 4983230072969 + 3 ^ 40 * 1296179 * 2
def baseEnd_1296179 : Nat := 295805707228528634400661

theorem tailTrace_1296179 : CollatzResearch.WordTrace tailWord_1296179 prefixEnd_1296179 295805707228528634400661 := by
  unfold tailWord_1296179
  simp only [CollatzResearch.WordTrace]
  refine ⟨47275531971172327594163591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31517021314114885062775727 47275531971172327594163591)
  ·
    refine ⟨70913297956758491391245387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47275531971172327594163591 70913297956758491391245387)
    ·
      refine ⟨106369946935137737086868081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70913297956758491391245387 106369946935137737086868081)
      ·
        refine ⟨79777460201353302815151061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106369946935137737086868081 79777460201353302815151061)
        ·
          refine ⟨1869784223469218034730103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 79777460201353302815151061 1869784223469218034730103)
          ·
            refine ⟨2804676335203827052095155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869784223469218034730103 2804676335203827052095155)
            ·
              refine ⟨4207014502805740578142733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2804676335203827052095155 4207014502805740578142733)
              ·
                refine ⟨1577630438552152716803525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4207014502805740578142733 1577630438552152716803525)
                ·
                  refine ⟨295805707228528634400661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1577630438552152716803525 295805707228528634400661)
                  ·
                    rfl

theorem cell21_1296179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 3, 4].length) (baseStart_1296179 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1296179 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1296179 prefixEnd_1296179 := by exact prefixLift 1296179
  have htrace : WordTrace (prefixWord ++ tailWord_1296179) baseStart_1296179 baseEnd_1296179 := by
    simpa [prefixWord, tailWord_1296179, baseEnd_1296179] using wordTrace_append hprefix tailTrace_1296179
  have hstable : (prefixWord ++ tailWord_1296179).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296179).length < 2 ^ (prefixWord ++ tailWord_1296179).sum := by decide
  have hdescent : baseEnd_1296179 < baseStart_1296179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296317 : List Nat := [1, 4, 1, 2, 3, 1, 3, 3, 3]
def baseStart_1296317 : Nat := 118140960795 + 1296317 * 2 ^ 59
def prefixEnd_1296317 : Nat := 4983230072969 + 3 ^ 40 * 1296317 * 2
def baseEnd_1296317 : Nat := 295837200708671061100379

theorem tailTrace_1296317 : CollatzResearch.WordTrace tailWord_1296317 prefixEnd_1296317 295837200708671061100379 := by
  unfold tailWord_1296317
  simp only [CollatzResearch.WordTrace]
  refine ⟨47280565244672377162687205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31520376829781584775124803 47280565244672377162687205)
  ·
    refine ⟨8865105983376070718003851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47280565244672377162687205 8865105983376070718003851)
    ·
      refine ⟨13297658975064106077005777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8865105983376070718003851 13297658975064106077005777)
      ·
        refine ⟨9973244231298079557754333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13297658975064106077005777 9973244231298079557754333)
        ·
          refine ⟨3739966586736779834157875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9973244231298079557754333 3739966586736779834157875)
          ·
            refine ⟨5609949880105169751236813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3739966586736779834157875 5609949880105169751236813)
            ·
              refine ⟨2103731205039438656713805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5609949880105169751236813 2103731205039438656713805)
              ·
                refine ⟨788899201889789496267677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2103731205039438656713805 788899201889789496267677)
                ·
                  refine ⟨295837200708671061100379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 788899201889789496267677 295837200708671061100379)
                  ·
                    rfl

theorem cell21_1296317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_1296317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1296317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1296317 prefixEnd_1296317 := by exact prefixLift 1296317
  have htrace : WordTrace (prefixWord ++ tailWord_1296317) baseStart_1296317 baseEnd_1296317 := by
    simpa [prefixWord, tailWord_1296317, baseEnd_1296317] using wordTrace_append hprefix tailTrace_1296317
  have hstable : (prefixWord ++ tailWord_1296317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296317).length < 2 ^ (prefixWord ++ tailWord_1296317).sum := by decide
  have hdescent : baseEnd_1296317 < baseStart_1296317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296328 : List Nat := [2, 1, 3, 1, 4, 1, 9]
def baseStart_1296328 : Nat := 118140960795 + 1296328 * 2 ^ 59
def prefixEnd_1296328 : Nat := 4983230072969 + 3 ^ 40 * 1296328 * 2
def baseEnd_1296328 : Nat := 32871079006504165157447

theorem tailTrace_1296328 : CollatzResearch.WordTrace tailWord_1296328 prefixEnd_1296328 32871079006504165157447 := by
  unfold tailWord_1296328
  simp only [CollatzResearch.WordTrace]
  refine ⟨23640483223816263020668819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31520644298421684027558425 23640483223816263020668819)
  ·
    refine ⟨35460724835724394531003229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23640483223816263020668819 35460724835724394531003229)
    ·
      refine ⟨13297771813396647949126211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35460724835724394531003229 13297771813396647949126211)
      ·
        refine ⟨19946657720094971923689317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13297771813396647949126211 19946657720094971923689317)
        ·
          refine ⟨3739998322517807235691747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19946657720094971923689317 3739998322517807235691747)
          ·
            refine ⟨5609997483776710853537621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3739998322517807235691747 5609997483776710853537621)
            ·
              refine ⟨32871079006504165157447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5609997483776710853537621 32871079006504165157447)
              ·
                rfl

theorem cell21_1296328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 9].length) (baseStart_1296328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1296328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1296328 prefixEnd_1296328 := by exact prefixLift 1296328
  have htrace : WordTrace (prefixWord ++ tailWord_1296328) baseStart_1296328 baseEnd_1296328 := by
    simpa [prefixWord, tailWord_1296328, baseEnd_1296328] using wordTrace_append hprefix tailTrace_1296328
  have hstable : (prefixWord ++ tailWord_1296328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296328).length < 2 ^ (prefixWord ++ tailWord_1296328).sum := by decide
  have hdescent : baseEnd_1296328 < baseStart_1296328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296345 : List Nat := [1, 2, 1, 2, 6, 1, 2, 6]
def baseStart_1296345 : Nat := 118140960795 + 1296345 * 2 ^ 59
def prefixEnd_1296345 : Nat := 4983230072969 + 3 ^ 40 * 1296345 * 2
def baseEnd_1296345 : Nat := 98614530230049744877885

theorem tailTrace_1296345 : CollatzResearch.WordTrace tailWord_1296345 prefixEnd_1296345 98614530230049744877885 := by
  unfold tailWord_1296345
  simp only [CollatzResearch.WordTrace]
  refine ⟨47281586488570937944706489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31521057659047291963137659 47281586488570937944706489)
  ·
    refine ⟨35461189866428203458529867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47281586488570937944706489 35461189866428203458529867)
    ·
      refine ⟨53191784799642305187794801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35461189866428203458529867 53191784799642305187794801)
      ·
        refine ⟨39893838599731728890846101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53191784799642305187794801 39893838599731728890846101)
        ·
          refine ⟨1870023684362424791758411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39893838599731728890846101 1870023684362424791758411)
          ·
            refine ⟨2805035526543637187637617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1870023684362424791758411 2805035526543637187637617)
            ·
              refine ⟨2103776644907727890728213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2805035526543637187637617 2103776644907727890728213)
              ·
                refine ⟨98614530230049744877885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2103776644907727890728213 98614530230049744877885)
                ·
                  rfl

theorem cell21_1296345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 6].length) (baseStart_1296345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1296345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1296345 prefixEnd_1296345 := by exact prefixLift 1296345
  have htrace : WordTrace (prefixWord ++ tailWord_1296345) baseStart_1296345 baseEnd_1296345 := by
    simpa [prefixWord, tailWord_1296345, baseEnd_1296345] using wordTrace_append hprefix tailTrace_1296345
  have hstable : (prefixWord ++ tailWord_1296345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296345).length < 2 ^ (prefixWord ++ tailWord_1296345).sum := by decide
  have hdescent : baseEnd_1296345 < baseStart_1296345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296421 : List Nat := [1, 3, 1, 2, 2, 4, 3, 5]
def baseStart_1296421 : Nat := 118140960795 + 1296421 * 2 ^ 59
def prefixEnd_1296421 : Nat := 4983230072969 + 3 ^ 40 * 1296421 * 2
def baseEnd_1296421 : Nat := 98620311641863330455611

theorem tailTrace_1296421 : CollatzResearch.WordTrace tailWord_1296421 prefixEnd_1296421 98620311641863330455611 := by
  unfold tailWord_1296421
  simp only [CollatzResearch.WordTrace]
  refine ⟨47284358436295602924473117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31522905624197068616315411 47284358436295602924473117)
  ·
    refine ⟨17731634413610851096677419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47284358436295602924473117 17731634413610851096677419)
    ·
      refine ⟨26597451620416276645016129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17731634413610851096677419 26597451620416276645016129)
      ·
        refine ⟨19948088715312207483762097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26597451620416276645016129 19948088715312207483762097)
        ·
          refine ⟨14961066536484155612821573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19948088715312207483762097 14961066536484155612821573)
          ·
            refine ⟨2805199975590779177404045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14961066536484155612821573 2805199975590779177404045)
            ·
              refine ⟨1051949990846542191526517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2805199975590779177404045 1051949990846542191526517)
              ·
                refine ⟨98620311641863330455611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1051949990846542191526517 98620311641863330455611)
                ·
                  rfl

theorem cell21_1296421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 5].length) (baseStart_1296421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1296421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1296421 prefixEnd_1296421 := by exact prefixLift 1296421
  have htrace : WordTrace (prefixWord ++ tailWord_1296421) baseStart_1296421 baseEnd_1296421 := by
    simpa [prefixWord, tailWord_1296421, baseEnd_1296421] using wordTrace_append hprefix tailTrace_1296421
  have hstable : (prefixWord ++ tailWord_1296421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296421).length < 2 ^ (prefixWord ++ tailWord_1296421).sum := by decide
  have hdescent : baseEnd_1296421 < baseStart_1296421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296480 : List Nat := [2, 1, 1, 3, 2, 4, 1, 7]
def baseStart_1296480 : Nat := 118140960795 + 1296480 * 2 ^ 59
def prefixEnd_1296480 : Nat := 4983230072969 + 3 ^ 40 * 1296480 * 2
def baseEnd_1296480 : Nat := 98624799843139666627793

theorem tailTrace_1296480 : CollatzResearch.WordTrace tailWord_1296480 prefixEnd_1296480 98624799843139666627793 := by
  unfold tailWord_1296480
  simp only [CollatzResearch.WordTrace]
  refine ⟨23643255171540928000435447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31524340228721237333913929 23643255171540928000435447)
  ·
    refine ⟨35464882757311392000653171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23643255171540928000435447 35464882757311392000653171)
    ·
      refine ⟨53197324135967088000979757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35464882757311392000653171 53197324135967088000979757)
      ·
        refine ⟨19948996550987658000367409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53197324135967088000979757 19948996550987658000367409)
        ·
          refine ⟨14961747413240743500275557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19948996550987658000367409 14961747413240743500275557)
          ·
            refine ⟨2805327639982639406301667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14961747413240743500275557 2805327639982639406301667)
            ·
              refine ⟨4207991459973959109452501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2805327639982639406301667 4207991459973959109452501)
              ·
                refine ⟨98624799843139666627793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4207991459973959109452501 98624799843139666627793)
                ·
                  rfl

theorem cell21_1296480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 7].length) (baseStart_1296480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1296480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1296480 prefixEnd_1296480 := by exact prefixLift 1296480
  have htrace : WordTrace (prefixWord ++ tailWord_1296480) baseStart_1296480 baseEnd_1296480 := by
    simpa [prefixWord, tailWord_1296480, baseEnd_1296480] using wordTrace_append hprefix tailTrace_1296480
  have hstable : (prefixWord ++ tailWord_1296480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296480).length < 2 ^ (prefixWord ++ tailWord_1296480).sum := by decide
  have hdescent : baseEnd_1296480 < baseStart_1296480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296539 : List Nat := [1, 1, 1, 1, 1, 1, 2, 13]
def baseStart_1296539 : Nat := 118140960795 + 1296539 * 2 ^ 59
def prefixEnd_1296539 : Nat := 4983230072969 + 3 ^ 40 * 1296539 * 2
def baseEnd_1296539 : Nat := 98629288044416002799975

theorem tailTrace_1296539 : CollatzResearch.WordTrace tailWord_1296539 prefixEnd_1296539 98629288044416002799975 := by
  unfold tailWord_1296539
  simp only [CollatzResearch.WordTrace]
  refine ⟨47288662249868109077268671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31525774833245406051512447 47288662249868109077268671)
  ·
    refine ⟨70932993374802163615903007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47288662249868109077268671 70932993374802163615903007)
    ·
      refine ⟨106399490062203245423854511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70932993374802163615903007 106399490062203245423854511)
      ·
        refine ⟨159599235093304868135781767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106399490062203245423854511 159599235093304868135781767)
        ·
          refine ⟨239398852639957302203672651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159599235093304868135781767 239398852639957302203672651)
          ·
            refine ⟨359098278959935953305508977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239398852639957302203672651 359098278959935953305508977)
            ·
              refine ⟨269323709219951964979131733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359098278959935953305508977 269323709219951964979131733)
              ·
                refine ⟨98629288044416002799975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 269323709219951964979131733 98629288044416002799975)
                ·
                  rfl

theorem cell21_1296539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 13].length) (baseStart_1296539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1296539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1296539 prefixEnd_1296539 := by exact prefixLift 1296539
  have htrace : WordTrace (prefixWord ++ tailWord_1296539) baseStart_1296539 baseEnd_1296539 := by
    simpa [prefixWord, tailWord_1296539, baseEnd_1296539] using wordTrace_append hprefix tailTrace_1296539
  have hstable : (prefixWord ++ tailWord_1296539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296539).length < 2 ^ (prefixWord ++ tailWord_1296539).sum := by decide
  have hdescent : baseEnd_1296539 < baseStart_1296539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296610 : List Nat := [3, 3, 4, 1, 1, 2, 1, 2, 4]
def baseStart_1296610 : Nat := 118140960795 + 1296610 * 2 ^ 59
def prefixEnd_1296610 : Nat := 4983230072969 + 3 ^ 40 * 1296610 * 2
def baseEnd_1296610 : Nat := 295904067300567662716447

theorem tailTrace_1296610 : CollatzResearch.WordTrace tailWord_1296610 prefixEnd_1296610 295904067300567662716447 := by
  unfold tailWord_1296610
  simp only [CollatzResearch.WordTrace]
  refine ⟨11822812958152722050775821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31527501221740592135402189 11822812958152722050775821)
  ·
    refine ⟨4433554859307270769040933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11822812958152722050775821 4433554859307270769040933)
    ·
      refine ⟨831291536120113269195175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4433554859307270769040933 831291536120113269195175)
      ·
        refine ⟨1246937304180169903792763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 831291536120113269195175 1246937304180169903792763)
        ·
          refine ⟨1870405956270254855689145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246937304180169903792763 1870405956270254855689145)
          ·
            refine ⟨1402804467202691141766859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1870405956270254855689145 1402804467202691141766859)
            ·
              refine ⟨2104206700804036712650289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1402804467202691141766859 2104206700804036712650289)
              ·
                refine ⟨1578155025603027534487717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2104206700804036712650289 1578155025603027534487717)
                ·
                  refine ⟨295904067300567662716447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1578155025603027534487717 295904067300567662716447)
                  ·
                    rfl

theorem cell21_1296610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_1296610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1296610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1296610 prefixEnd_1296610 := by exact prefixLift 1296610
  have htrace : WordTrace (prefixWord ++ tailWord_1296610) baseStart_1296610 baseEnd_1296610 := by
    simpa [prefixWord, tailWord_1296610, baseEnd_1296610] using wordTrace_append hprefix tailTrace_1296610
  have hstable : (prefixWord ++ tailWord_1296610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296610).length < 2 ^ (prefixWord ++ tailWord_1296610).sum := by decide
  have hdescent : baseEnd_1296610 < baseStart_1296610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296649 : List Nat := [1, 2, 1, 1, 3, 6, 2, 5]
def baseStart_1296649 : Nat := 118140960795 + 1296649 * 2 ^ 59
def prefixEnd_1296649 : Nat := 4983230072969 + 3 ^ 40 * 1296649 * 2
def baseEnd_1296649 : Nat := 98637655877304087188789

theorem tailTrace_1296649 : CollatzResearch.WordTrace tailWord_1296649 prefixEnd_1296649 98637655877304087188789 := by
  unfold tailWord_1296649
  simp only [CollatzResearch.WordTrace]
  refine ⟨47292674279469597863773001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31528449519646398575848667 47292674279469597863773001)
  ·
    refine ⟨35469505709602198397829751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47292674279469597863773001 35469505709602198397829751)
    ·
      refine ⟨53204258564403297596744627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35469505709602198397829751 53204258564403297596744627)
      ·
        refine ⟨79806387846604946395116941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53204258564403297596744627 79806387846604946395116941)
        ·
          refine ⟨29927395442476854898168853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79806387846604946395116941 29927395442476854898168853)
          ·
            refine ⟨1402846661366102573351665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29927395442476854898168853 1402846661366102573351665)
            ·
              refine ⟨1052134996024576930013749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1402846661366102573351665 1052134996024576930013749)
              ·
                refine ⟨98637655877304087188789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1052134996024576930013749 98637655877304087188789)
                ·
                  rfl

theorem cell21_1296649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 5].length) (baseStart_1296649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1296649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1296649 prefixEnd_1296649 := by exact prefixLift 1296649
  have htrace : WordTrace (prefixWord ++ tailWord_1296649) baseStart_1296649 baseEnd_1296649 := by
    simpa [prefixWord, tailWord_1296649, baseEnd_1296649] using wordTrace_append hprefix tailTrace_1296649
  have hstable : (prefixWord ++ tailWord_1296649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296649).length < 2 ^ (prefixWord ++ tailWord_1296649).sum := by decide
  have hdescent : baseEnd_1296649 < baseStart_1296649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296686 : List Nat := [4, 1, 3, 3, 2, 1, 2, 1, 4]
def baseStart_1296686 : Nat := 118140960795 + 1296686 * 2 ^ 59
def prefixEnd_1296686 : Nat := 4983230072969 + 3 ^ 40 * 1296686 * 2
def baseEnd_1296686 : Nat := 295921411536008419449625

theorem tailTrace_1296686 : CollatzResearch.WordTrace tailWord_1296686 prefixEnd_1296686 295921411536008419449625 := by
  unfold tailWord_1296686
  simp only [CollatzResearch.WordTrace]
  refine ⟨5911752972541944147858739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31529349186890368788579941 5911752972541944147858739)
  ·
    refine ⟨8867629458812916221788109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5911752972541944147858739 8867629458812916221788109)
    ·
      refine ⟨3325361047054843583170541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8867629458812916221788109 3325361047054843583170541)
      ·
        refine ⟨1247010392645566343688953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3325361047054843583170541 1247010392645566343688953)
        ·
          refine ⟨935257794484174757766715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1247010392645566343688953 935257794484174757766715)
          ·
            refine ⟨1402886691726262136650073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935257794484174757766715 1402886691726262136650073)
            ·
              refine ⟨1052165018794696602487555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1402886691726262136650073 1052165018794696602487555)
              ·
                refine ⟨1578247528192044903731333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052165018794696602487555 1578247528192044903731333)
                ·
                  refine ⟨295921411536008419449625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1578247528192044903731333 295921411536008419449625)
                  ·
                    rfl

theorem cell21_1296686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_1296686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1296686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1296686 prefixEnd_1296686 := by exact prefixLift 1296686
  have htrace : WordTrace (prefixWord ++ tailWord_1296686) baseStart_1296686 baseEnd_1296686 := by
    simpa [prefixWord, tailWord_1296686, baseEnd_1296686] using wordTrace_append hprefix tailTrace_1296686
  have hstable : (prefixWord ++ tailWord_1296686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296686).length < 2 ^ (prefixWord ++ tailWord_1296686).sum := by decide
  have hdescent : baseEnd_1296686 < baseStart_1296686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296829 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 6]
def baseStart_1296829 : Nat := 118140960795 + 1296829 * 2 ^ 59
def prefixEnd_1296829 : Nat := 4983230072969 + 3 ^ 40 * 1296829 * 2
def baseEnd_1296829 : Nat := 295954046084271948565999

theorem tailTrace_1296829 : CollatzResearch.WordTrace tailWord_1296829 prefixEnd_1296829 295954046084271948565999 := by
  unfold tailWord_1296829
  simp only [CollatzResearch.WordTrace]
  refine ⟨47299239418817488605325541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31532826279211659070217027 47299239418817488605325541)
  ·
    refine ⟨8868607391028279113498539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47299239418817488605325541 8868607391028279113498539)
    ·
      refine ⟨13302911086542418670247809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8868607391028279113498539 13302911086542418670247809)
      ·
        refine ⟨9977183314906814002685857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13302911086542418670247809 9977183314906814002685857)
        ·
          refine ⟨7482887486180110502014393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9977183314906814002685857 7482887486180110502014393)
          ·
            refine ⟨5612165614635082876510795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7482887486180110502014393 5612165614635082876510795)
            ·
              refine ⟨8418248421952624314766193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5612165614635082876510795 8418248421952624314766193)
              ·
                refine ⟨6313686316464468236074645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8418248421952624314766193 6313686316464468236074645)
                ·
                  refine ⟨295954046084271948565999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6313686316464468236074645 295954046084271948565999)
                  ·
                    rfl

theorem cell21_1296829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_1296829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1296829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1296829 prefixEnd_1296829 := by exact prefixLift 1296829
  have htrace : WordTrace (prefixWord ++ tailWord_1296829) baseStart_1296829 baseEnd_1296829 := by
    simpa [prefixWord, tailWord_1296829, baseEnd_1296829] using wordTrace_append hprefix tailTrace_1296829
  have hstable : (prefixWord ++ tailWord_1296829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296829).length < 2 ^ (prefixWord ++ tailWord_1296829).sum := by decide
  have hdescent : baseEnd_1296829 < baseStart_1296829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296863 : List Nat := [1, 1, 2, 3, 3, 4, 2, 1, 4]
def baseStart_1296863 : Nat := 118140960795 + 1296863 * 2 ^ 59
def prefixEnd_1296863 : Nat := 4983230072969 + 3 ^ 40 * 1296863 * 2
def baseEnd_1296863 : Nat := 295961805347495444999263

theorem tailTrace_1296863 : CollatzResearch.WordTrace tailWord_1296863 prefixEnd_1296863 295961805347495444999263 := by
  unfold tailWord_1296863
  simp only [CollatzResearch.WordTrace]
  refine ⟨47300479500694312412063243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31533653000462874941375495 47300479500694312412063243)
  ·
    refine ⟨70950719251041468618094865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47300479500694312412063243 70950719251041468618094865)
    ·
      refine ⟨53213039438281101463571149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70950719251041468618094865 53213039438281101463571149)
      ·
        refine ⟨19954889789355413048839181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53213039438281101463571149 19954889789355413048839181)
        ·
          refine ⟨7483083671008279893314693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19954889789355413048839181 7483083671008279893314693)
          ·
            refine ⟨1403078188314052479996505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7483083671008279893314693 1403078188314052479996505)
            ·
              refine ⟨1052308641235539359997379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1403078188314052479996505 1052308641235539359997379)
              ·
                refine ⟨1578462961853309039996069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052308641235539359997379 1578462961853309039996069)
                ·
                  refine ⟨295961805347495444999263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1578462961853309039996069 295961805347495444999263)
                  ·
                    rfl

theorem cell21_1296863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 4].length) (baseStart_1296863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1296863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1296863 prefixEnd_1296863 := by exact prefixLift 1296863
  have htrace : WordTrace (prefixWord ++ tailWord_1296863) baseStart_1296863 baseEnd_1296863 := by
    simpa [prefixWord, tailWord_1296863, baseEnd_1296863] using wordTrace_append hprefix tailTrace_1296863
  have hstable : (prefixWord ++ tailWord_1296863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296863).length < 2 ^ (prefixWord ++ tailWord_1296863).sum := by decide
  have hdescent : baseEnd_1296863 < baseStart_1296863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296908 : List Nat := [2, 2, 1, 2, 4, 2, 1, 4, 3]
def baseStart_1296908 : Nat := 118140960795 + 1296908 * 2 ^ 59
def prefixEnd_1296908 : Nat := 4983230072969 + 3 ^ 40 * 1296908 * 2
def baseEnd_1296908 : Nat := 295972074960585366749171

theorem tailTrace_1296908 : CollatzResearch.WordTrace tailWord_1296908 prefixEnd_1296908 295972074960585366749171 := by
  unfold tailWord_1296908
  simp only [CollatzResearch.WordTrace]
  refine ⟨23651060392765642548725689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31534747190354190064967585 23651060392765642548725689)
  ·
    refine ⟨17738295294574231911544267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23651060392765642548725689 17738295294574231911544267)
    ·
      refine ⟨26607442941861347867316401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17738295294574231911544267 26607442941861347867316401)
      ·
        refine ⟨19955582206396010900487301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26607442941861347867316401 19955582206396010900487301)
        ·
          refine ⟨3741671663699252043841369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19955582206396010900487301 3741671663699252043841369)
          ·
            refine ⟨2806253747774439032881027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3741671663699252043841369 2806253747774439032881027)
            ·
              refine ⟨4209380621661658549321541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2806253747774439032881027 4209380621661658549321541)
              ·
                refine ⟨789258866561560977997789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4209380621661658549321541 789258866561560977997789)
                ·
                  refine ⟨295972074960585366749171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 789258866561560977997789 295972074960585366749171)
                  ·
                    rfl

theorem cell21_1296908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 3].length) (baseStart_1296908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1296908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1296908 prefixEnd_1296908 := by exact prefixLift 1296908
  have htrace : WordTrace (prefixWord ++ tailWord_1296908) baseStart_1296908 baseEnd_1296908 := by
    simpa [prefixWord, tailWord_1296908, baseEnd_1296908] using wordTrace_append hprefix tailTrace_1296908
  have hstable : (prefixWord ++ tailWord_1296908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296908).length < 2 ^ (prefixWord ++ tailWord_1296908).sum := by decide
  have hdescent : baseEnd_1296908 < baseStart_1296908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296967 : List Nat := [1, 1, 4, 1, 4, 2, 2, 1, 5]
def baseStart_1296967 : Nat := 118140960795 + 1296967 * 2 ^ 59
def prefixEnd_1296967 : Nat := 4983230072969 + 3 ^ 40 * 1296967 * 2
def baseEnd_1296967 : Nat := 295985539564414375265717

theorem tailTrace_1296967 : CollatzResearch.WordTrace tailWord_1296967 prefixEnd_1296967 295985539564414375265717 := by
  unfold tailWord_1296967
  simp only [CollatzResearch.WordTrace]
  refine ⟨47304272692317538173849155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31536181794878358782566103 47304272692317538173849155)
  ·
    refine ⟨70956409038476307260773733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47304272692317538173849155 70956409038476307260773733)
    ·
      refine ⟨13304326694714307611395075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70956409038476307260773733 13304326694714307611395075)
      ·
        refine ⟨19956490042071461417092613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13304326694714307611395075 19956490042071461417092613)
        ·
          refine ⟨3741841882888399015704865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19956490042071461417092613 3741841882888399015704865)
          ·
            refine ⟨2806381412166299261778649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3741841882888399015704865 2806381412166299261778649)
            ·
              refine ⟨2104786059124724446333987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2806381412166299261778649 2104786059124724446333987)
              ·
                refine ⟨3157179088687086669500981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2104786059124724446333987 3157179088687086669500981)
                ·
                  refine ⟨295985539564414375265717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3157179088687086669500981 295985539564414375265717)
                  ·
                    rfl

theorem cell21_1296967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 5].length) (baseStart_1296967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1296967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1296967 prefixEnd_1296967 := by exact prefixLift 1296967
  have htrace : WordTrace (prefixWord ++ tailWord_1296967) baseStart_1296967 baseEnd_1296967 := by
    simpa [prefixWord, tailWord_1296967, baseEnd_1296967] using wordTrace_append hprefix tailTrace_1296967
  have hstable : (prefixWord ++ tailWord_1296967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296967).length < 2 ^ (prefixWord ++ tailWord_1296967).sum := by decide
  have hdescent : baseEnd_1296967 < baseStart_1296967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296981 : List Nat := [1, 3, 2, 2, 1, 1, 2, 5, 4]
def baseStart_1296981 : Nat := 118140960795 + 1296981 * 2 ^ 59
def prefixEnd_1296981 : Nat := 4983230072969 + 3 ^ 40 * 1296981 * 2
def baseEnd_1296981 : Nat := 295988734555153462032355

theorem tailTrace_1296981 : CollatzResearch.WordTrace tailWord_1296981 prefixEnd_1296981 295988734555153462032355 := by
  unfold tailWord_1296981
  simp only [CollatzResearch.WordTrace]
  refine ⟨47304783314266818564858797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31536522209511212376572531 47304783314266818564858797)
  ·
    refine ⟨17739293742850056961822049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47304783314266818564858797 17739293742850056961822049)
    ·
      refine ⟨13304470307137542721366537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17739293742850056961822049 13304470307137542721366537)
      ·
        refine ⟨9978352730353157041024903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13304470307137542721366537 9978352730353157041024903)
        ·
          refine ⟨14967529095529735561537355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9978352730353157041024903 14967529095529735561537355)
          ·
            refine ⟨22451293643294603342306033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14967529095529735561537355 22451293643294603342306033)
            ·
              refine ⟨16838470232470952506729525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22451293643294603342306033 16838470232470952506729525)
              ·
                refine ⟨1578606584294151797505893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16838470232470952506729525 1578606584294151797505893)
                ·
                  refine ⟨295988734555153462032355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1578606584294151797505893 295988734555153462032355)
                  ·
                    rfl

theorem cell21_1296981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_1296981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1296981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1296981 prefixEnd_1296981 := by exact prefixLift 1296981
  have htrace : WordTrace (prefixWord ++ tailWord_1296981) baseStart_1296981 baseEnd_1296981 := by
    simpa [prefixWord, tailWord_1296981, baseEnd_1296981] using wordTrace_append hprefix tailTrace_1296981
  have hstable : (prefixWord ++ tailWord_1296981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296981).length < 2 ^ (prefixWord ++ tailWord_1296981).sum := by decide
  have hdescent : baseEnd_1296981 < baseStart_1296981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296995 : List Nat := [1, 1, 1, 5, 1, 2, 3, 7]
def baseStart_1296995 : Nat := 118140960795 + 1296995 * 2 ^ 59
def prefixEnd_1296995 : Nat := 4983230072969 + 3 ^ 40 * 1296995 * 2
def baseEnd_1296995 : Nat := 98663976515297516266331

theorem tailTrace_1296995 : CollatzResearch.WordTrace tailWord_1296995 prefixEnd_1296995 98663976515297516266331 := by
  unfold tailWord_1296995
  simp only [CollatzResearch.WordTrace]
  refine ⟨47305293936216098955868439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31536862624144065970578959 47305293936216098955868439)
  ·
    refine ⟨70957940904324148433802659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47305293936216098955868439 70957940904324148433802659)
    ·
      refine ⟨106436911356486222650703989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70957940904324148433802659 106436911356486222650703989)
      ·
        refine ⟨9978460439670583373503499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106436911356486222650703989 9978460439670583373503499)
        ·
          refine ⟨14967690659505875060255249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9978460439670583373503499 14967690659505875060255249)
          ·
            refine ⟨11225767994629406295191437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14967690659505875060255249 11225767994629406295191437)
            ·
              refine ⟨4209662997986027360696789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11225767994629406295191437 4209662997986027360696789)
              ·
                refine ⟨98663976515297516266331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4209662997986027360696789 98663976515297516266331)
                ·
                  rfl

theorem cell21_1296995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 7].length) (baseStart_1296995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1296995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1296995 prefixEnd_1296995 := by exact prefixLift 1296995
  have htrace : WordTrace (prefixWord ++ tailWord_1296995) baseStart_1296995 baseEnd_1296995 := by
    simpa [prefixWord, tailWord_1296995, baseEnd_1296995] using wordTrace_append hprefix tailTrace_1296995
  have hstable : (prefixWord ++ tailWord_1296995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296995).length < 2 ^ (prefixWord ++ tailWord_1296995).sum := by decide
  have hdescent : baseEnd_1296995 < baseStart_1296995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297077 : List Nat := [1, 3, 3, 3, 1, 1, 4, 2, 3]
def baseStart_1297077 : Nat := 118140960795 + 1297077 * 2 ^ 59
def prefixEnd_1297077 : Nat := 4983230072969 + 3 ^ 40 * 1297077 * 2
def baseEnd_1297077 : Nat := 296010643063078628432159

theorem tailTrace_1297077 : CollatzResearch.WordTrace tailWord_1297077 prefixEnd_1297077 296010643063078628432159 := by
  unfold tailWord_1297077
  simp only [CollatzResearch.WordTrace]
  refine ⟨47308284721919026960353485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31538856481279351306902323 47308284721919026960353485)
  ·
    refine ⟨17740606770719635110132557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47308284721919026960353485 17740606770719635110132557)
    ·
      refine ⟨6652727539019863166299709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17740606770719635110132557 6652727539019863166299709)
      ·
        refine ⟨2494772827132448687362391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6652727539019863166299709 2494772827132448687362391)
        ·
          refine ⟨3742159240698673031043587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2494772827132448687362391 3742159240698673031043587)
          ·
            refine ⟨5613238861048009546565381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3742159240698673031043587 5613238861048009546565381)
            ·
              refine ⟨1052482286446501789981009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5613238861048009546565381 1052482286446501789981009)
              ·
                refine ⟨789361714834876342485757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1052482286446501789981009 789361714834876342485757)
                ·
                  refine ⟨296010643063078628432159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 789361714834876342485757 296010643063078628432159)
                  ·
                    rfl

theorem cell21_1297077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 3].length) (baseStart_1297077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1297077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1297077 prefixEnd_1297077 := by exact prefixLift 1297077
  have htrace : WordTrace (prefixWord ++ tailWord_1297077) baseStart_1297077 baseEnd_1297077 := by
    simpa [prefixWord, tailWord_1297077, baseEnd_1297077] using wordTrace_append hprefix tailTrace_1297077
  have hstable : (prefixWord ++ tailWord_1297077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297077).length < 2 ^ (prefixWord ++ tailWord_1297077).sum := by decide
  have hdescent : baseEnd_1297077 < baseStart_1297077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297088 : List Nat := [2, 1, 1, 2, 4, 4, 1, 6]
def baseStart_1297088 : Nat := 118140960795 + 1297088 * 2 ^ 59
def prefixEnd_1297088 : Nat := 4983230072969 + 3 ^ 40 * 1297088 * 2
def baseEnd_1297088 : Nat := 98671051137648351249601

theorem tailTrace_1297088 : CollatzResearch.WordTrace tailWord_1297088 prefixEnd_1297088 98671051137648351249601 := by
  unfold tailWord_1297088
  simp only [CollatzResearch.WordTrace]
  refine ⟨23654342962439587919501959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31539123949919450559335945 23654342962439587919501959)
  ·
    refine ⟨35481514443659381879252939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23654342962439587919501959 35481514443659381879252939)
    ·
      refine ⟨53222271665489072818879409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35481514443659381879252939 53222271665489072818879409)
      ·
        refine ⟨39916703749116804614159557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53222271665489072818879409 39916703749116804614159557)
        ·
          refine ⟨7484381952959400865154917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39916703749116804614159557 7484381952959400865154917)
          ·
            refine ⟨1403321616179887662216547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7484381952959400865154917 1403321616179887662216547)
            ·
              refine ⟨2104982424269831493324821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1403321616179887662216547 2104982424269831493324821)
              ·
                refine ⟨98671051137648351249601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2104982424269831493324821 98671051137648351249601)
                ·
                  rfl

theorem cell21_1297088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 6].length) (baseStart_1297088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1297088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1297088 prefixEnd_1297088 := by exact prefixLift 1297088
  have htrace : WordTrace (prefixWord ++ tailWord_1297088) baseStart_1297088 baseEnd_1297088 := by
    simpa [prefixWord, tailWord_1297088, baseEnd_1297088] using wordTrace_append hprefix tailTrace_1297088
  have hstable : (prefixWord ++ tailWord_1297088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297088).length < 2 ^ (prefixWord ++ tailWord_1297088).sum := by decide
  have hdescent : baseEnd_1297088 < baseStart_1297088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297102 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_1297102 : Nat := 118140960795 + 1297102 * 2 ^ 59
def prefixEnd_1297102 : Nat := 4983230072969 + 3 ^ 40 * 1297102 * 2
def baseEnd_1297102 : Nat := 296016348403684140515441

theorem tailTrace_1297102 : CollatzResearch.WordTrace tailWord_1297102 prefixEnd_1297102 296016348403684140515441 := by
  unfold tailWord_1297102
  simp only [CollatzResearch.WordTrace]
  refine ⟨5913649568353557028751695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31539464364552304153342373 5913649568353557028751695)
  ·
    refine ⟨8870474352530335543127543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5913649568353557028751695 8870474352530335543127543)
    ·
      refine ⟨13305711528795503314691315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8870474352530335543127543 13305711528795503314691315)
      ·
        refine ⟨19958567293193254972036973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13305711528795503314691315 19958567293193254972036973)
        ·
          refine ⟨7484462734947470614513865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19958567293193254972036973 7484462734947470614513865)
          ·
            refine ⟨5613347051210602960885399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7484462734947470614513865 5613347051210602960885399)
            ·
              refine ⟨8420020576815904441328099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5613347051210602960885399 8420020576815904441328099)
              ·
                refine ⟨12630030865223856661992149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8420020576815904441328099 12630030865223856661992149)
                ·
                  refine ⟨296016348403684140515441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12630030865223856661992149 296016348403684140515441)
                  ·
                    rfl

theorem cell21_1297102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_1297102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1297102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1297102 prefixEnd_1297102 := by exact prefixLift 1297102
  have htrace : WordTrace (prefixWord ++ tailWord_1297102) baseStart_1297102 baseEnd_1297102 := by
    simpa [prefixWord, tailWord_1297102, baseEnd_1297102] using wordTrace_append hprefix tailTrace_1297102
  have hstable : (prefixWord ++ tailWord_1297102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297102).length < 2 ^ (prefixWord ++ tailWord_1297102).sum := by decide
  have hdescent : baseEnd_1297102 < baseStart_1297102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297119 : List Nat := [1, 1, 2, 3, 2, 3, 1, 5, 3]
def baseStart_1297119 : Nat := 118140960795 + 1297119 * 2 ^ 59
def prefixEnd_1297119 : Nat := 4983230072969 + 3 ^ 40 * 1297119 * 2
def baseEnd_1297119 : Nat := 296020228035295888732073

theorem tailTrace_1297119 : CollatzResearch.WordTrace tailWord_1297119 prefixEnd_1297119 296020228035295888732073 := by
  unfold tailWord_1297119
  simp only [CollatzResearch.WordTrace]
  refine ⟨47309816587766868133382411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31539877725177912088921607 47309816587766868133382411)
  ·
    refine ⟨70964724881650302200073617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47309816587766868133382411 70964724881650302200073617)
    ·
      refine ⟨53223543661237726650055213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70964724881650302200073617 53223543661237726650055213)
      ·
        refine ⟨19958828872964147493770705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53223543661237726650055213 19958828872964147493770705)
        ·
          refine ⟨14969121654723110620328029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19958828872964147493770705 14969121654723110620328029)
          ·
            refine ⟨5613420620521166482623011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14969121654723110620328029 5613420620521166482623011)
            ·
              refine ⟨8420130930781749723934517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5613420620521166482623011 8420130930781749723934517)
              ·
                refine ⟨789387274760789036618861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8420130930781749723934517 789387274760789036618861)
                ·
                  refine ⟨296020228035295888732073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 789387274760789036618861 296020228035295888732073)
                  ·
                    rfl

theorem cell21_1297119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 3].length) (baseStart_1297119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1297119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1297119 prefixEnd_1297119 := by exact prefixLift 1297119
  have htrace : WordTrace (prefixWord ++ tailWord_1297119) baseStart_1297119 baseEnd_1297119 := by
    simpa [prefixWord, tailWord_1297119, baseEnd_1297119] using wordTrace_append hprefix tailTrace_1297119
  have hstable : (prefixWord ++ tailWord_1297119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297119).length < 2 ^ (prefixWord ++ tailWord_1297119).sum := by decide
  have hdescent : baseEnd_1297119 < baseStart_1297119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297133 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 6]
def baseStart_1297133 : Nat := 118140960795 + 1297133 * 2 ^ 59
def prefixEnd_1297133 : Nat := 4983230072969 + 3 ^ 40 * 1297133 * 2
def baseEnd_1297133 : Nat := 296023423026034975498711

theorem tailTrace_1297133 : CollatzResearch.WordTrace tailWord_1297133 prefixEnd_1297133 296023423026034975498711 := by
  unfold tailWord_1297133
  simp only [CollatzResearch.WordTrace]
  refine ⟨47310327209716148524392053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31540218139810765682928035 47310327209716148524392053)
  ·
    refine ⟨4435343175910888924161755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47310327209716148524392053 4435343175910888924161755)
    ·
      refine ⟨6653014763866333386242633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4435343175910888924161755 6653014763866333386242633)
      ·
        refine ⟨4989761072899750039681975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6653014763866333386242633 4989761072899750039681975)
        ·
          refine ⟨7484641609349625059522963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4989761072899750039681975 7484641609349625059522963)
          ·
            refine ⟨11226962414024437589284445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7484641609349625059522963 11226962414024437589284445)
            ·
              refine ⟨4210110905259164095981667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11226962414024437589284445 4210110905259164095981667)
              ·
                refine ⟨6315166357888746143972501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4210110905259164095981667 6315166357888746143972501)
                ·
                  refine ⟨296023423026034975498711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6315166357888746143972501 296023423026034975498711)
                  ·
                    rfl

theorem cell21_1297133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_1297133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1297133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1297133 prefixEnd_1297133 := by exact prefixLift 1297133
  have htrace : WordTrace (prefixWord ++ tailWord_1297133) baseStart_1297133 baseEnd_1297133 := by
    simpa [prefixWord, tailWord_1297133, baseEnd_1297133] using wordTrace_append hprefix tailTrace_1297133
  have hstable : (prefixWord ++ tailWord_1297133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297133).length < 2 ^ (prefixWord ++ tailWord_1297133).sum := by decide
  have hdescent : baseEnd_1297133 < baseStart_1297133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297170 : List Nat := [3, 2, 4, 1, 2, 2, 1, 3, 3]
def baseStart_1297170 : Nat := 118140960795 + 1297170 * 2 ^ 59
def prefixEnd_1297170 : Nat := 4983230072969 + 3 ^ 40 * 1297170 * 2
def baseEnd_1297170 : Nat := 296031866930131133381969

theorem tailTrace_1297170 : CollatzResearch.WordTrace tailWord_1297170 prefixEnd_1297170 296031866930131133381969 := by
  unfold tailWord_1297170
  simp only [CollatzResearch.WordTrace]
  refine ⟨11827919177645525960872241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31541117807054735895659309 11827919177645525960872241)
  ·
    refine ⟨8870939383234144470654181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11827919177645525960872241 8870939383234144470654181)
    ·
      refine ⟨1663301134356402088247659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8870939383234144470654181 1663301134356402088247659)
      ·
        refine ⟨2494951701534603132371489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1663301134356402088247659 2494951701534603132371489)
        ·
          refine ⟨1871213776150952349278617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2494951701534603132371489 1871213776150952349278617)
          ·
            refine ⟨1403410332113214261958963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1871213776150952349278617 1403410332113214261958963)
            ·
              refine ⟨2105115498169821392938445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1403410332113214261958963 2105115498169821392938445)
              ·
                refine ⟨789418311813683022351917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2105115498169821392938445 789418311813683022351917)
                ·
                  refine ⟨296031866930131133381969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 789418311813683022351917 296031866930131133381969)
                  ·
                    rfl

theorem cell21_1297170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_1297170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1297170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1297170 prefixEnd_1297170 := by exact prefixLift 1297170
  have htrace : WordTrace (prefixWord ++ tailWord_1297170) baseStart_1297170 baseEnd_1297170 := by
    simpa [prefixWord, tailWord_1297170, baseEnd_1297170] using wordTrace_append hprefix tailTrace_1297170
  have hstable : (prefixWord ++ tailWord_1297170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297170).length < 2 ^ (prefixWord ++ tailWord_1297170).sum := by decide
  have hdescent : baseEnd_1297170 < baseStart_1297170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297181 : List Nat := [1, 4, 2, 4, 1, 2, 7]
def baseStart_1297181 : Nat := 118140960795 + 1297181 * 2 ^ 59
def prefixEnd_1297181 : Nat := 4983230072969 + 3 ^ 40 * 1297181 * 2
def baseEnd_1297181 : Nat := 32892708586666395410957

theorem tailTrace_1297181 : CollatzResearch.WordTrace tailWord_1297181 prefixEnd_1297181 32892708586666395410957 := by
  unfold tailWord_1297181
  simp only [CollatzResearch.WordTrace]
  refine ⟨47312077913542252722139397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31541385275694835148092931 47312077913542252722139397)
  ·
    refine ⟨8871014608789172385401137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47312077913542252722139397 8871014608789172385401137)
    ·
      refine ⟨6653260956591879289050853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8871014608789172385401137 6653260956591879289050853)
      ·
        refine ⟨1247486429360977366697035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6653260956591879289050853 1247486429360977366697035)
        ·
          refine ⟨1871229644041466050045553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1247486429360977366697035 1871229644041466050045553)
          ·
            refine ⟨1403422233031099537534165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1871229644041466050045553 1403422233031099537534165)
            ·
              refine ⟨32892708586666395410957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1403422233031099537534165 32892708586666395410957)
              ·
                rfl

theorem cell21_1297181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 7].length) (baseStart_1297181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1297181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1297181 prefixEnd_1297181 := by exact prefixLift 1297181
  have htrace : WordTrace (prefixWord ++ tailWord_1297181) baseStart_1297181 baseEnd_1297181 := by
    simpa [prefixWord, tailWord_1297181, baseEnd_1297181] using wordTrace_append hprefix tailTrace_1297181
  have hstable : (prefixWord ++ tailWord_1297181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297181).length < 2 ^ (prefixWord ++ tailWord_1297181).sum := by decide
  have hdescent : baseEnd_1297181 < baseStart_1297181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297288 : List Nat := [2, 1, 3, 3, 2, 2, 2, 3, 3]
def baseStart_1297288 : Nat := 118140960795 + 1297288 * 2 ^ 59
def prefixEnd_1297288 : Nat := 4983230072969 + 3 ^ 40 * 1297288 * 2
def baseEnd_1297288 : Nat := 296058796137789150415061

theorem tailTrace_1297288 : CollatzResearch.WordTrace tailWord_1297288 prefixEnd_1297288 296058796137789150415061 := by
  unfold tailWord_1297288
  simp only [CollatzResearch.WordTrace]
  refine ⟨23657990262077304998142259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31543987016103073330856345 23657990262077304998142259)
  ·
    refine ⟨35486985393115957497213389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23657990262077304998142259 35486985393115957497213389)
    ·
      refine ⟨13307619522418484061455021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35486985393115957497213389 13307619522418484061455021)
      ·
        refine ⟨4990357320906931523045633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13307619522418484061455021 4990357320906931523045633)
        ·
          refine ⟨3742767990680198642284225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4990357320906931523045633 3742767990680198642284225)
          ·
            refine ⟨2807075993010148981713169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3742767990680198642284225 2807075993010148981713169)
            ·
              refine ⟨2105306994757611736284877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2807075993010148981713169 2105306994757611736284877)
              ·
                refine ⟨789490123034104401106829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2105306994757611736284877 789490123034104401106829)
                ·
                  refine ⟨296058796137789150415061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 789490123034104401106829 296058796137789150415061)
                  ·
                    rfl

theorem cell21_1297288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 3].length) (baseStart_1297288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1297288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1297288 prefixEnd_1297288 := by exact prefixLift 1297288
  have htrace : WordTrace (prefixWord ++ tailWord_1297288) baseStart_1297288 baseEnd_1297288 := by
    simpa [prefixWord, tailWord_1297288, baseEnd_1297288] using wordTrace_append hprefix tailTrace_1297288
  have hstable : (prefixWord ++ tailWord_1297288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297288).length < 2 ^ (prefixWord ++ tailWord_1297288).sum := by decide
  have hdescent : baseEnd_1297288 < baseStart_1297288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297319 : List Nat := [1, 1, 6, 1, 3, 1, 3, 1, 4]
def baseStart_1297319 : Nat := 118140960795 + 1297319 * 2 ^ 59
def prefixEnd_1297319 : Nat := 4983230072969 + 3 ^ 40 * 1297319 * 2
def baseEnd_1297319 : Nat := 296065870760139985398331

theorem tailTrace_1297319 : CollatzResearch.WordTrace tailWord_1297319 prefixEnd_1297319 296065870760139985398331 := by
  unfold tailWord_1297319
  simp only [CollatzResearch.WordTrace]
  refine ⟨47317111187042302290663011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31544740791361534860442007 47317111187042302290663011)
  ·
    refine ⟨70975666780563453435994517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47317111187042302290663011 70975666780563453435994517)
    ·
      refine ⟨3326984380338911879812243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 70975666780563453435994517 3326984380338911879812243)
      ·
        refine ⟨4990476570508367819718365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3326984380338911879812243 4990476570508367819718365)
        ·
          refine ⟨1871428713940637932394387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4990476570508367819718365 1871428713940637932394387)
          ·
            refine ⟨2807143070910956898591581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1871428713940637932394387 2807143070910956898591581)
            ·
              refine ⟨1052678651591608836971843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2807143070910956898591581 1052678651591608836971843)
              ·
                refine ⟨1579017977387413255457765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052678651591608836971843 1579017977387413255457765)
                ·
                  refine ⟨296065870760139985398331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1579017977387413255457765 296065870760139985398331)
                  ·
                    rfl

theorem cell21_1297319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 4].length) (baseStart_1297319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1297319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1297319 prefixEnd_1297319 := by exact prefixLift 1297319
  have htrace : WordTrace (prefixWord ++ tailWord_1297319) baseStart_1297319 baseEnd_1297319 := by
    simpa [prefixWord, tailWord_1297319, baseEnd_1297319] using wordTrace_append hprefix tailTrace_1297319
  have hstable : (prefixWord ++ tailWord_1297319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297319).length < 2 ^ (prefixWord ++ tailWord_1297319).sum := by decide
  have hdescent : baseEnd_1297319 < baseStart_1297319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297344 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 6]
def baseStart_1297344 : Nat := 118140960795 + 1297344 * 2 ^ 59
def prefixEnd_1297344 : Nat := 4983230072969 + 3 ^ 40 * 1297344 * 2
def baseEnd_1297344 : Nat := 296071576100745497481613

theorem tailTrace_1297344 : CollatzResearch.WordTrace tailWord_1297344 prefixEnd_1297344 296071576100745497481613 := by
  unfold tailWord_1297344
  simp only [CollatzResearch.WordTrace]
  refine ⟨23659011505975865780161543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31545348674634487706882057 23659011505975865780161543)
  ·
    refine ⟨35488517258963798670242315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23659011505975865780161543 35488517258963798670242315)
    ·
      refine ⟨53232775888445698005363473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35488517258963798670242315 53232775888445698005363473)
      ·
        refine ⟨39924581916334273504022605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53232775888445698005363473 39924581916334273504022605)
        ·
          refine ⟨14971718218625352564008477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39924581916334273504022605 14971718218625352564008477)
          ·
            refine ⟨5614394331984507211503179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14971718218625352564008477 5614394331984507211503179)
            ·
              refine ⟨8421591497976760817254769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5614394331984507211503179 8421591497976760817254769)
              ·
                refine ⟨6316193623482570612941077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8421591497976760817254769 6316193623482570612941077)
                ·
                  refine ⟨296071576100745497481613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6316193623482570612941077 296071576100745497481613)
                  ·
                    rfl

theorem cell21_1297344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_1297344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1297344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1297344 prefixEnd_1297344 := by exact prefixLift 1297344
  have htrace : WordTrace (prefixWord ++ tailWord_1297344) baseStart_1297344 baseEnd_1297344 := by
    simpa [prefixWord, tailWord_1297344, baseEnd_1297344] using wordTrace_append hprefix tailTrace_1297344
  have hstable : (prefixWord ++ tailWord_1297344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297344).length < 2 ^ (prefixWord ++ tailWord_1297344).sum := by decide
  have hdescent : baseEnd_1297344 < baseStart_1297344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297451 : List Nat := [1, 1, 1, 1, 2, 1, 9, 5]
def baseStart_1297451 : Nat := 118140960795 + 1297451 * 2 ^ 59
def prefixEnd_1297451 : Nat := 4983230072969 + 3 ^ 40 * 1297451 * 2
def baseEnd_1297451 : Nat := 98698664986179029732687

theorem tailTrace_1297451 : CollatzResearch.WordTrace tailWord_1297451 prefixEnd_1297451 98698664986179029732687 := by
  unfold tailWord_1297451
  simp only [CollatzResearch.WordTrace]
  refine ⟨47321925622564088834468207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31547950415042725889645471 47321925622564088834468207)
  ·
    refine ⟨70982888433846133251702311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47321925622564088834468207 70982888433846133251702311)
    ·
      refine ⟨106474332650769199877553467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70982888433846133251702311 106474332650769199877553467)
      ·
        refine ⟨159711498976153799816330201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106474332650769199877553467 159711498976153799816330201)
        ·
          refine ⟨119783624232115349862247651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159711498976153799816330201 119783624232115349862247651)
          ·
            refine ⟨179675436348173024793371477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119783624232115349862247651 179675436348173024793371477)
            ·
              refine ⟨1052785759852576317148661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 179675436348173024793371477 1052785759852576317148661)
              ·
                refine ⟨98698664986179029732687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1052785759852576317148661 98698664986179029732687)
                ·
                  rfl

theorem cell21_1297451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 5].length) (baseStart_1297451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1297451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1297451 prefixEnd_1297451 := by exact prefixLift 1297451
  have htrace : WordTrace (prefixWord ++ tailWord_1297451) baseStart_1297451 baseEnd_1297451 := by
    simpa [prefixWord, tailWord_1297451, baseEnd_1297451] using wordTrace_append hprefix tailTrace_1297451
  have hstable : (prefixWord ++ tailWord_1297451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297451).length < 2 ^ (prefixWord ++ tailWord_1297451).sum := by decide
  have hdescent : baseEnd_1297451 < baseStart_1297451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297502 : List Nat := [4, 4, 1, 1, 1, 1, 4, 5]
def baseStart_1297502 : Nat := 118140960795 + 1297502 * 2 ^ 59
def prefixEnd_1297502 : Nat := 4983230072969 + 3 ^ 40 * 1297502 * 2
def baseEnd_1297502 : Nat := 98702544617790777949319

theorem tailTrace_1297502 : CollatzResearch.WordTrace tailWord_1297502 prefixEnd_1297502 98702544617790777949319 := by
  unfold tailWord_1297502
  simp only [CollatzResearch.WordTrace]
  refine ⟨5915473218172415568071845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31549190496919549696383173 5915473218172415568071845)
  ·
    refine ⟨1109151228407327919013471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5915473218172415568071845 1109151228407327919013471)
    ·
      refine ⟨1663726842610991878520207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1109151228407327919013471 1663726842610991878520207)
      ·
        refine ⟨2495590263916487817780311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1663726842610991878520207 2495590263916487817780311)
        ·
          refine ⟨3743385395874731726670467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2495590263916487817780311 3743385395874731726670467)
          ·
            refine ⟨5615078093812097590005701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3743385395874731726670467 5615078093812097590005701)
            ·
              refine ⟨1052827142589768298126069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5615078093812097590005701 1052827142589768298126069)
              ·
                refine ⟨98702544617790777949319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1052827142589768298126069 98702544617790777949319)
                ·
                  rfl

theorem cell21_1297502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_1297502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1297502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1297502 prefixEnd_1297502 := by exact prefixLift 1297502
  have htrace : WordTrace (prefixWord ++ tailWord_1297502) baseStart_1297502 baseEnd_1297502 := by
    simpa [prefixWord, tailWord_1297502, baseEnd_1297502] using wordTrace_append hprefix tailTrace_1297502
  have hstable : (prefixWord ++ tailWord_1297502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297502).length < 2 ^ (prefixWord ++ tailWord_1297502).sum := by decide
  have hdescent : baseEnd_1297502 < baseStart_1297502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297544 : List Nat := [2, 1, 3, 4, 2, 1, 2, 6]
def baseStart_1297544 : Nat := 118140960795 + 1297544 * 2 ^ 59
def prefixEnd_1297544 : Nat := 4983230072969 + 3 ^ 40 * 1297544 * 2
def baseEnd_1297544 : Nat := 98705739608529864715957

theorem tailTrace_1297544 : CollatzResearch.WordTrace tailWord_1297544 prefixEnd_1297544 98705739608529864715957 := by
  unfold tailWord_1297544
  simp only [CollatzResearch.WordTrace]
  refine ⟨23662658805613582858801843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31550211740818110478402457 23662658805613582858801843)
  ·
    refine ⟨35493988208420374288202765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23662658805613582858801843 35493988208420374288202765)
    ·
      refine ⟨13310245578157640358076037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35493988208420374288202765 13310245578157640358076037)
      ·
        refine ⟨2495671045904557567139257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13310245578157640358076037 2495671045904557567139257)
        ·
          refine ⟨1871753284428418175354443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2495671045904557567139257 1871753284428418175354443)
          ·
            refine ⟨2807629926642627263031665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1871753284428418175354443 2807629926642627263031665)
            ·
              refine ⟨2105722444981970447273749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2807629926642627263031665 2105722444981970447273749)
              ·
                refine ⟨98705739608529864715957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2105722444981970447273749 98705739608529864715957)
                ·
                  rfl

theorem cell21_1297544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 6].length) (baseStart_1297544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1297544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1297544 prefixEnd_1297544 := by exact prefixLift 1297544
  have htrace : WordTrace (prefixWord ++ tailWord_1297544) baseStart_1297544 baseEnd_1297544 := by
    simpa [prefixWord, tailWord_1297544, baseEnd_1297544] using wordTrace_append hprefix tailTrace_1297544
  have hstable : (prefixWord ++ tailWord_1297544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297544).length < 2 ^ (prefixWord ++ tailWord_1297544).sum := by decide
  have hdescent : baseEnd_1297544 < baseStart_1297544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297586 : List Nat := [3, 2, 1, 1, 1, 13]
def baseStart_1297586 : Nat := 118140960795 + 1297586 * 2 ^ 59
def prefixEnd_1297586 : Nat := 4983230072969 + 3 ^ 40 * 1297586 * 2
def baseEnd_1297586 : Nat := 10967659399918772386955

theorem tailTrace_1297586 : CollatzResearch.WordTrace tailWord_1297586 prefixEnd_1297586 10967659399918772386955 := by
  unfold tailWord_1297586
  simp only [CollatzResearch.WordTrace]
  refine ⟨11831712369268751722658153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31551232984716671260421741 11831712369268751722658153)
  ·
    refine ⟨8873784276951563791993615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11831712369268751722658153 8873784276951563791993615)
    ·
      refine ⟨13310676415427345687990423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8873784276951563791993615 13310676415427345687990423)
      ·
        refine ⟨19966014623141018531985635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13310676415427345687990423 19966014623141018531985635)
        ·
          refine ⟨29949021934711527797978453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19966014623141018531985635 29949021934711527797978453)
          ·
            refine ⟨10967659399918772386955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 29949021934711527797978453 10967659399918772386955)
            ·
              rfl

theorem cell21_1297586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 13].length) (baseStart_1297586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1297586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1297586 prefixEnd_1297586 := by exact prefixLift 1297586
  have htrace : WordTrace (prefixWord ++ tailWord_1297586) baseStart_1297586 baseEnd_1297586 := by
    simpa [prefixWord, tailWord_1297586, baseEnd_1297586] using wordTrace_append hprefix tailTrace_1297586
  have hstable : (prefixWord ++ tailWord_1297586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297586).length < 2 ^ (prefixWord ++ tailWord_1297586).sum := by decide
  have hdescent : baseEnd_1297586 < baseStart_1297586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297696 : List Nat := [2, 1, 1, 5, 4, 1, 7]
def baseStart_1297696 : Nat := 118140960795 + 1297696 * 2 ^ 59
def prefixEnd_1297696 : Nat := 4983230072969 + 3 ^ 40 * 1297696 * 2
def baseEnd_1297696 : Nat := 32905767477385678623803

theorem tailTrace_1297696 : CollatzResearch.WordTrace tailWord_1297696 prefixEnd_1297696 32905767477385678623803 := by
  unfold tailWord_1297696
  simp only [CollatzResearch.WordTrace]
  refine ⟨23665430753338247838568471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31553907671117663784757961 23665430753338247838568471)
  ·
    refine ⟨35498146130007371757852707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23665430753338247838568471 35498146130007371757852707)
    ·
      refine ⟨53247219195011057636779061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35498146130007371757852707 53247219195011057636779061)
      ·
        refine ⟨4991926799532286653448037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53247219195011057636779061 4991926799532286653448037)
        ·
          refine ⟨935986274912303747521507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4991926799532286653448037 935986274912303747521507)
          ·
            refine ⟨1403979412368455621282261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935986274912303747521507 1403979412368455621282261)
            ·
              refine ⟨32905767477385678623803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1403979412368455621282261 32905767477385678623803)
              ·
                rfl

theorem cell21_1297696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 7].length) (baseStart_1297696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1297696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1297696 prefixEnd_1297696 := by exact prefixLift 1297696
  have htrace : WordTrace (prefixWord ++ tailWord_1297696) baseStart_1297696 baseEnd_1297696 := by
    simpa [prefixWord, tailWord_1297696, baseEnd_1297696] using wordTrace_append hprefix tailTrace_1297696
  have hstable : (prefixWord ++ tailWord_1297696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297696).length < 2 ^ (prefixWord ++ tailWord_1297696).sum := by decide
  have hdescent : baseEnd_1297696 < baseStart_1297696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297817 : List Nat := [1, 2, 1, 2, 1, 7, 1, 2, 4]
def baseStart_1297817 : Nat := 118140960795 + 1297817 * 2 ^ 59
def prefixEnd_1297817 : Nat := 4983230072969 + 3 ^ 40 * 1297817 * 2
def baseEnd_1297817 : Nat := 296179521145001786097313

theorem tailTrace_1297817 : CollatzResearch.WordTrace tailWord_1297817 prefixEnd_1297817 296179521145001786097313 := by
  unfold tailWord_1297817
  simp only [CollatzResearch.WordTrace]
  refine ⟨47335274739238133342291705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31556849826158755561527803 47335274739238133342291705)
  ·
    refine ⟨35501456054428600006718779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47335274739238133342291705 35501456054428600006718779)
    ·
      refine ⟨53252184081642900010078169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35501456054428600006718779 53252184081642900010078169)
      ·
        refine ⟨39939138061232175007558627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53252184081642900010078169 39939138061232175007558627)
        ·
          refine ⟨59908707091848262511337941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39939138061232175007558627 59908707091848262511337941)
          ·
            refine ⟨1404110322465193652609483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 59908707091848262511337941 1404110322465193652609483)
            ·
              refine ⟨2106165483697790478914225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1404110322465193652609483 2106165483697790478914225)
              ·
                refine ⟨1579624112773342859185669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2106165483697790478914225 1579624112773342859185669)
                ·
                  refine ⟨296179521145001786097313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1579624112773342859185669 296179521145001786097313)
                  ·
                    rfl

theorem cell21_1297817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 4].length) (baseStart_1297817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1297817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1297817 prefixEnd_1297817 := by exact prefixLift 1297817
  have htrace : WordTrace (prefixWord ++ tailWord_1297817) baseStart_1297817 baseEnd_1297817 := by
    simpa [prefixWord, tailWord_1297817, baseEnd_1297817] using wordTrace_append hprefix tailTrace_1297817
  have hstable : (prefixWord ++ tailWord_1297817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297817).length < 2 ^ (prefixWord ++ tailWord_1297817).sum := by decide
  have hdescent : baseEnd_1297817 < baseStart_1297817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297859 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 6]
def baseStart_1297859 : Nat := 118140960795 + 1297859 * 2 ^ 59
def prefixEnd_1297859 : Nat := 4983230072969 + 3 ^ 40 * 1297859 * 2
def baseEnd_1297859 : Nat := 296189106117219046397227

theorem tailTrace_1297859 : CollatzResearch.WordTrace tailWord_1297859 prefixEnd_1297859 296189106117219046397227 := by
  unfold tailWord_1297859
  simp only [CollatzResearch.WordTrace]
  refine ⟨47336806605085974515320631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31557871070057316343547087 47336806605085974515320631)
  ·
    refine ⟨71005209907628961772980947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47336806605085974515320631 71005209907628961772980947)
    ·
      refine ⟨106507814861443442659471421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71005209907628961772980947 106507814861443442659471421)
      ·
        refine ⟨39940430573041290997301783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106507814861443442659471421 39940430573041290997301783)
        ·
          refine ⟨59910645859561936495952675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39940430573041290997301783 59910645859561936495952675)
          ·
            refine ⟨89865968789342904743929013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59910645859561936495952675 89865968789342904743929013)
            ·
              refine ⟨8424934574000897319743345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89865968789342904743929013 8424934574000897319743345)
              ·
                refine ⟨6318700930500672989807509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8424934574000897319743345 6318700930500672989807509)
                ·
                  refine ⟨296189106117219046397227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6318700930500672989807509 296189106117219046397227)
                  ·
                    rfl

theorem cell21_1297859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 6].length) (baseStart_1297859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1297859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1297859 prefixEnd_1297859 := by exact prefixLift 1297859
  have htrace : WordTrace (prefixWord ++ tailWord_1297859) baseStart_1297859 baseEnd_1297859 := by
    simpa [prefixWord, tailWord_1297859, baseEnd_1297859] using wordTrace_append hprefix tailTrace_1297859
  have hstable : (prefixWord ++ tailWord_1297859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297859).length < 2 ^ (prefixWord ++ tailWord_1297859).sum := by decide
  have hdescent : baseEnd_1297859 < baseStart_1297859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297893 : List Nat := [1, 3, 1, 5, 1, 2, 1, 3, 4]
def baseStart_1297893 : Nat := 118140960795 + 1297893 * 2 ^ 59
def prefixEnd_1297893 : Nat := 4983230072969 + 3 ^ 40 * 1297893 * 2
def baseEnd_1297893 : Nat := 296196865380442542830491

theorem tailTrace_1297893 : CollatzResearch.WordTrace tailWord_1297893 prefixEnd_1297893 296196865380442542830491 := by
  unfold tailWord_1297893
  simp only [CollatzResearch.WordTrace]
  refine ⟨47338046686962798322058333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31558697791308532214705555 47338046686962798322058333)
  ·
    refine ⟨17751767507611049370771875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47338046686962798322058333 17751767507611049370771875)
    ·
      refine ⟨26627651261416574056157813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17751767507611049370771875 26627651261416574056157813)
      ·
        refine ⟨2496342305757803817764795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26627651261416574056157813 2496342305757803817764795)
        ·
          refine ⟨3744513458636705726647193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2496342305757803817764795 3744513458636705726647193)
          ·
            refine ⟨2808385093977529294985395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3744513458636705726647193 2808385093977529294985395)
            ·
              refine ⟨4212577640966293942478093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2808385093977529294985395 4212577640966293942478093)
              ·
                refine ⟨1579716615362360228429285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4212577640966293942478093 1579716615362360228429285)
                ·
                  refine ⟨296196865380442542830491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1579716615362360228429285 296196865380442542830491)
                  ·
                    rfl

theorem cell21_1297893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_1297893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1297893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1297893 prefixEnd_1297893 := by exact prefixLift 1297893
  have htrace : WordTrace (prefixWord ++ tailWord_1297893) baseStart_1297893 baseEnd_1297893 := by
    simpa [prefixWord, tailWord_1297893, baseEnd_1297893] using wordTrace_append hprefix tailTrace_1297893
  have hstable : (prefixWord ++ tailWord_1297893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297893).length < 2 ^ (prefixWord ++ tailWord_1297893).sum := by decide
  have hdescent : baseEnd_1297893 < baseStart_1297893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298062 : List Nat := [4, 1, 1, 3, 1, 4, 2, 1, 4]
def baseStart_1298062 : Nat := 118140960795 + 1298062 * 2 ^ 59
def prefixEnd_1298062 : Nat := 4983230072969 + 3 ^ 40 * 1298062 * 2
def baseEnd_1298062 : Nat := 296235433482935804513479

theorem tailTrace_1298062 : CollatzResearch.WordTrace tailWord_1298062 prefixEnd_1298062 296235433482935804513479 := by
  unfold tailWord_1298062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5918026327918817523120055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31562807082233693456640293 5918026327918817523120055)
  ·
    refine ⟨8877039491878226284680083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5918026327918817523120055 8877039491878226284680083)
    ·
      refine ⟨13315559237817339427020125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8877039491878226284680083 13315559237817339427020125)
      ·
        refine ⟨4993334714181502285132547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13315559237817339427020125 4993334714181502285132547)
        ·
          refine ⟨7490002071272253427698821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4993334714181502285132547 7490002071272253427698821)
          ·
            refine ⟨1404375388363547517693529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7490002071272253427698821 1404375388363547517693529)
            ·
              refine ⟨1053281541272660638270147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1404375388363547517693529 1053281541272660638270147)
              ·
                refine ⟨1579922311908990957405221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1053281541272660638270147 1579922311908990957405221)
                ·
                  refine ⟨296235433482935804513479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1579922311908990957405221 296235433482935804513479)
                  ·
                    rfl

theorem cell21_1298062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_1298062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1298062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1298062 prefixEnd_1298062 := by exact prefixLift 1298062
  have htrace : WordTrace (prefixWord ++ tailWord_1298062) baseStart_1298062 baseEnd_1298062 := by
    simpa [prefixWord, tailWord_1298062, baseEnd_1298062] using wordTrace_append hprefix tailTrace_1298062
  have hstable : (prefixWord ++ tailWord_1298062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298062).length < 2 ^ (prefixWord ++ tailWord_1298062).sum := by decide
  have hdescent : baseEnd_1298062 < baseStart_1298062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298166 : List Nat := [5, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_1298166 : Nat := 118140960795 + 1298166 * 2 ^ 59
def prefixEnd_1298166 : Nat := 4983230072969 + 3 ^ 40 * 1298166 * 2
def baseEnd_1298166 : Nat := 296259167699854734779933

theorem tailTrace_1298166 : CollatzResearch.WordTrace tailWord_1298166 prefixEnd_1298166 296259167699854734779933 := by
  unfold tailWord_1298166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2959250238435860371671647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31565335876649177297830901 2959250238435860371671647)
  ·
    refine ⟨4438875357653790557507471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2959250238435860371671647 4438875357653790557507471)
    ·
      refine ⟨6658313036480685836261207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4438875357653790557507471 6658313036480685836261207)
      ·
        refine ⟨9987469554721028754391811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6658313036480685836261207 9987469554721028754391811)
        ·
          refine ⟨14981204332081543131587717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9987469554721028754391811 14981204332081543131587717)
          ·
            refine ⟨2808975812265289337172697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14981204332081543131587717 2808975812265289337172697)
            ·
              refine ⟨2106731859198967002879523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2808975812265289337172697 2106731859198967002879523)
              ·
                refine ⟨3160097788798450504319285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2106731859198967002879523 3160097788798450504319285)
                ·
                  refine ⟨296259167699854734779933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3160097788798450504319285 296259167699854734779933)
                  ·
                    rfl

theorem cell21_1298166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_1298166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1298166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1298166 prefixEnd_1298166 := by exact prefixLift 1298166
  have htrace : WordTrace (prefixWord ++ tailWord_1298166) baseStart_1298166 baseEnd_1298166 := by
    simpa [prefixWord, tailWord_1298166, baseEnd_1298166] using wordTrace_append hprefix tailTrace_1298166
  have hstable : (prefixWord ++ tailWord_1298166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298166).length < 2 ^ (prefixWord ++ tailWord_1298166).sum := by decide
  have hdescent : baseEnd_1298166 < baseStart_1298166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298225 : List Nat := [1, 2, 2, 3, 2, 2, 3, 1, 5]
def baseStart_1298225 : Nat := 118140960795 + 1298225 * 2 ^ 59
def prefixEnd_1298225 : Nat := 4983230072969 + 3 ^ 40 * 1298225 * 2
def baseEnd_1298225 : Nat := 296272632303683743296479

theorem tailTrace_1298225 : CollatzResearch.WordTrace tailWord_1298225 prefixEnd_1298225 296272632303683743296479 := by
  unfold tailWord_1298225
  simp only [CollatzResearch.WordTrace]
  refine ⟨47350155721760019023144129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31566770481173346015429419 47350155721760019023144129)
  ·
    refine ⟨35512616791320014267358097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47350155721760019023144129 35512616791320014267358097)
    ·
      refine ⟨26634462593490010700518573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35512616791320014267358097 26634462593490010700518573)
      ·
        refine ⟨9987923472558754012694465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26634462593490010700518573 9987923472558754012694465)
        ·
          refine ⟨7490942604419065509520849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9987923472558754012694465 7490942604419065509520849)
          ·
            refine ⟨5618206953314299132140637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7490942604419065509520849 5618206953314299132140637)
            ·
              refine ⟨2106827607492862174552739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5618206953314299132140637 2106827607492862174552739)
              ·
                refine ⟨3160241411239293261829109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2106827607492862174552739 3160241411239293261829109)
                ·
                  refine ⟨296272632303683743296479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3160241411239293261829109 296272632303683743296479)
                  ·
                    rfl

theorem cell21_1298225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 5].length) (baseStart_1298225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1298225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1298225 prefixEnd_1298225 := by exact prefixLift 1298225
  have htrace : WordTrace (prefixWord ++ tailWord_1298225) baseStart_1298225 baseEnd_1298225 := by
    simpa [prefixWord, tailWord_1298225, baseEnd_1298225] using wordTrace_append hprefix tailTrace_1298225
  have hstable : (prefixWord ++ tailWord_1298225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298225).length < 2 ^ (prefixWord ++ tailWord_1298225).sum := by decide
  have hdescent : baseEnd_1298225 < baseStart_1298225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298270 : List Nat := [4, 4, 13]
def baseStart_1298270 : Nat := 118140960795 + 1298270 * 2 ^ 59
def prefixEnd_1298270 : Nat := 4983230072969 + 3 ^ 40 * 1298270 * 2
def baseEnd_1298270 : Nat := 406423733767865109803

theorem tailTrace_1298270 : CollatzResearch.WordTrace tailWord_1298270 prefixEnd_1298270 406423733767865109803 := by
  unfold tailWord_1298270
  simp only [CollatzResearch.WordTrace]
  refine ⟨5918974625824623963566533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31567864671064661139021509 5918974625824623963566533)
  ·
    refine ⟨1109807742342116993168725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5918974625824623963566533 1109807742342116993168725)
    ·
      refine ⟨406423733767865109803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 13 1109807742342116993168725 406423733767865109803)
      ·
        rfl

theorem cell21_1298270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 13].length) (baseStart_1298270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1298270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1298270 prefixEnd_1298270 := by exact prefixLift 1298270
  have htrace : WordTrace (prefixWord ++ tailWord_1298270) baseStart_1298270 baseEnd_1298270 := by
    simpa [prefixWord, tailWord_1298270, baseEnd_1298270] using wordTrace_append hprefix tailTrace_1298270
  have hstable : (prefixWord ++ tailWord_1298270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298270).length < 2 ^ (prefixWord ++ tailWord_1298270).sum := by decide
  have hdescent : baseEnd_1298270 < baseStart_1298270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298276 : List Nat := [2, 3, 1, 1, 5, 2, 2, 2, 3]
def baseStart_1298276 : Nat := 118140960795 + 1298276 * 2 ^ 59
def prefixEnd_1298276 : Nat := 4983230072969 + 3 ^ 40 * 1298276 * 2
def baseEnd_1298276 : Nat := 296284271198518987946375

theorem tailTrace_1298276 : CollatzResearch.WordTrace tailWord_1298276 prefixEnd_1298276 296284271198518987946375 := by
  unfold tailWord_1298276
  simp only [CollatzResearch.WordTrace]
  refine ⟨23676007922287627366625341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31568010563050169822167121 23676007922287627366625341)
  ·
    refine ⟨8878502970857860262484503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23676007922287627366625341 8878502970857860262484503)
    ·
      refine ⟨13317754456286790393726755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8878502970857860262484503 13317754456286790393726755)
      ·
        refine ⟨19976631684430185590590133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13317754456286790393726755 19976631684430185590590133)
        ·
          refine ⟨1872809220415329899117825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19976631684430185590590133 1872809220415329899117825)
          ·
            refine ⟨1404606915311497424338369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1872809220415329899117825 1404606915311497424338369)
            ·
              refine ⟨1053455186483623068253777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1404606915311497424338369 1053455186483623068253777)
              ·
                refine ⟨790091389862717301190333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1053455186483623068253777 790091389862717301190333)
                ·
                  refine ⟨296284271198518987946375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 790091389862717301190333 296284271198518987946375)
                  ·
                    rfl

theorem cell21_1298276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_1298276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1298276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1298276 prefixEnd_1298276 := by exact prefixLift 1298276
  have htrace : WordTrace (prefixWord ++ tailWord_1298276) baseStart_1298276 baseEnd_1298276 := by
    simpa [prefixWord, tailWord_1298276, baseEnd_1298276] using wordTrace_append hprefix tailTrace_1298276
  have hstable : (prefixWord ++ tailWord_1298276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298276).length < 2 ^ (prefixWord ++ tailWord_1298276).sum := by decide
  have hdescent : baseEnd_1298276 < baseStart_1298276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298332 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 6]
def baseStart_1298332 : Nat := 118140960795 + 1298332 * 2 ^ 59
def prefixEnd_1298332 : Nat := 4983230072969 + 3 ^ 40 * 1298332 * 2
def baseEnd_1298332 : Nat := 296297051161475335012927

theorem tailTrace_1298332 : CollatzResearch.WordTrace tailWord_1298332 prefixEnd_1298332 296297051161475335012927 := by
  unfold tailWord_1298332
  simp only [CollatzResearch.WordTrace]
  refine ⟨23677029166186188148644625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31569372221581584198192833 23677029166186188148644625)
  ·
    refine ⟨17757771874639641111483469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23677029166186188148644625 17757771874639641111483469)
    ·
      refine ⟨6659164452989865416806301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17757771874639641111483469 6659164452989865416806301)
      ·
        refine ⟨2497186669871199531302363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6659164452989865416806301 2497186669871199531302363)
        ·
          refine ⟨3745780004806799296953545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2497186669871199531302363 3745780004806799296953545)
          ·
            refine ⟨2809335003605099472715159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3745780004806799296953545 2809335003605099472715159)
            ·
              refine ⟨4214002505407649209072739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2809335003605099472715159 4214002505407649209072739)
              ·
                refine ⟨6321003758111473813609109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4214002505407649209072739 6321003758111473813609109)
                ·
                  refine ⟨296297051161475335012927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6321003758111473813609109 296297051161475335012927)
                  ·
                    rfl

theorem cell21_1298332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_1298332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1298332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1298332 prefixEnd_1298332 := by exact prefixLift 1298332
  have htrace : WordTrace (prefixWord ++ tailWord_1298332) baseStart_1298332 baseEnd_1298332 := by
    simpa [prefixWord, tailWord_1298332, baseEnd_1298332] using wordTrace_append hprefix tailTrace_1298332
  have hstable : (prefixWord ++ tailWord_1298332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298332).length < 2 ^ (prefixWord ++ tailWord_1298332).sum := by decide
  have hdescent : baseEnd_1298332 < baseStart_1298332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298360 : List Nat := [2, 1, 2, 1, 2, 3, 1, 4, 5]
def baseStart_1298360 : Nat := 118140960795 + 1298360 * 2 ^ 59
def prefixEnd_1298360 : Nat := 4983230072969 + 3 ^ 40 * 1298360 * 2
def baseEnd_1298360 : Nat := 296303441142953508546203

theorem tailTrace_1298360 : CollatzResearch.WordTrace tailWord_1298360 prefixEnd_1298360 296303441142953508546203 := by
  unfold tailWord_1298360
  simp only [CollatzResearch.WordTrace]
  refine ⟨23677539788135468539654267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31570053050847291386205689 23677539788135468539654267)
  ·
    refine ⟨35516309682203202809481401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23677539788135468539654267 35516309682203202809481401)
    ·
      refine ⟨26637232261652402107111051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35516309682203202809481401 26637232261652402107111051)
      ·
        refine ⟨39955848392478603160666577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26637232261652402107111051 39955848392478603160666577)
        ·
          refine ⟨29966886294358952370499933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39955848392478603160666577 29966886294358952370499933)
          ·
            refine ⟨11237582360384607138937475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29966886294358952370499933 11237582360384607138937475)
            ·
              refine ⟨16856373540576910708406213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11237582360384607138937475 16856373540576910708406213)
              ·
                refine ⟨3160570038858170757826165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16856373540576910708406213 3160570038858170757826165)
                ·
                  refine ⟨296303441142953508546203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3160570038858170757826165 296303441142953508546203)
                  ·
                    rfl

theorem cell21_1298360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_1298360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1298360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1298360 prefixEnd_1298360 := by exact prefixLift 1298360
  have htrace : WordTrace (prefixWord ++ tailWord_1298360) baseStart_1298360 baseEnd_1298360 := by
    simpa [prefixWord, tailWord_1298360, baseEnd_1298360] using wordTrace_append hprefix tailTrace_1298360
  have hstable : (prefixWord ++ tailWord_1298360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298360).length < 2 ^ (prefixWord ++ tailWord_1298360).sum := by decide
  have hdescent : baseEnd_1298360 < baseStart_1298360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298391 : List Nat := [1, 1, 3, 2, 1, 1, 4, 4, 4]
def baseStart_1298391 : Nat := 118140960795 + 1298391 * 2 ^ 59
def prefixEnd_1298391 : Nat := 4983230072969 + 3 ^ 40 * 1298391 * 2
def baseEnd_1298391 : Nat := 296310515765304343529473

theorem tailTrace_1298391 : CollatzResearch.WordTrace tailWord_1298391 prefixEnd_1298391 296310515765304343529473 := by
  unfold tailWord_1298391
  simp only [CollatzResearch.WordTrace]
  refine ⟨47356210239158629373687027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31570806826105752915791351 47356210239158629373687027)
  ·
    refine ⟨71034315358737944060530541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47356210239158629373687027 71034315358737944060530541)
    ·
      refine ⟨26637868259526729022698953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71034315358737944060530541 26637868259526729022698953)
      ·
        refine ⟨19978401194645046767024215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26637868259526729022698953 19978401194645046767024215)
        ·
          refine ⟨29967601791967570150536323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19978401194645046767024215 29967601791967570150536323)
          ·
            refine ⟨44951402687951355225804485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29967601791967570150536323 44951402687951355225804485)
            ·
              refine ⟨8428388003990879104838341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44951402687951355225804485 8428388003990879104838341)
              ·
                refine ⟨1580322750748289832157189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8428388003990879104838341 1580322750748289832157189)
                ·
                  refine ⟨296310515765304343529473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1580322750748289832157189 296310515765304343529473)
                  ·
                    rfl

theorem cell21_1298391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 4].length) (baseStart_1298391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1298391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1298391 prefixEnd_1298391 := by exact prefixLift 1298391
  have htrace : WordTrace (prefixWord ++ tailWord_1298391) baseStart_1298391 baseEnd_1298391 := by
    simpa [prefixWord, tailWord_1298391, baseEnd_1298391] using wordTrace_append hprefix tailTrace_1298391
  have hstable : (prefixWord ++ tailWord_1298391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298391).length < 2 ^ (prefixWord ++ tailWord_1298391).sum := by decide
  have hdescent : baseEnd_1298391 < baseStart_1298391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298394 : List Nat := [3, 1, 1, 2, 5, 2, 1, 1, 5]
def baseStart_1298394 : Nat := 118140960795 + 1298394 * 2 ^ 59
def prefixEnd_1298394 : Nat := 4983230072969 + 3 ^ 40 * 1298394 * 2
def baseEnd_1298394 : Nat := 296311200406177004979467

theorem tailTrace_1298394 : CollatzResearch.WordTrace tailWord_1298394 prefixEnd_1298394 296311200406177004979467 := by
  unfold tailWord_1298394
  simp only [CollatzResearch.WordTrace]
  refine ⟨11839079914536940221511559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31570879772098507257364157 11839079914536940221511559)
  ·
    refine ⟨17758619871805410332267339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11839079914536940221511559 17758619871805410332267339)
    ·
      refine ⟨26637929807708115498401009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17758619871805410332267339 26637929807708115498401009)
      ·
        refine ⟨19978447355781086623800757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26637929807708115498401009 19978447355781086623800757)
        ·
          refine ⟨1872979439604476870981321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19978447355781086623800757 1872979439604476870981321)
          ·
            refine ⟨1404734579703357653235991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1872979439604476870981321 1404734579703357653235991)
            ·
              refine ⟨2107101869555036479853987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1404734579703357653235991 2107101869555036479853987)
              ·
                refine ⟨3160652804332554719780981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2107101869555036479853987 3160652804332554719780981)
                ·
                  refine ⟨296311200406177004979467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3160652804332554719780981 296311200406177004979467)
                  ·
                    rfl

theorem cell21_1298394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_1298394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1298394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1298394 prefixEnd_1298394 := by exact prefixLift 1298394
  have htrace : WordTrace (prefixWord ++ tailWord_1298394) baseStart_1298394 baseEnd_1298394 := by
    simpa [prefixWord, tailWord_1298394, baseEnd_1298394] using wordTrace_append hprefix tailTrace_1298394
  have hstable : (prefixWord ++ tailWord_1298394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298394).length < 2 ^ (prefixWord ++ tailWord_1298394).sum := by decide
  have hdescent : baseEnd_1298394 < baseStart_1298394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298445 : List Nat := [1, 7, 1, 2, 1, 1, 1, 4, 3]
def baseStart_1298445 : Nat := 118140960795 + 1298445 * 2 ^ 59
def prefixEnd_1298445 : Nat := 4983230072969 + 3 ^ 40 * 1298445 * 2
def baseEnd_1298445 : Nat := 296322839301012249629363

theorem tailTrace_1298445 : CollatzResearch.WordTrace tailWord_1298445 prefixEnd_1298445 296322839301012249629363 := by
  unfold tailWord_1298445
  simp only [CollatzResearch.WordTrace]
  refine ⟨47358179780962996596152789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31572119853975331064101859 47358179780962996596152789)
  ·
    refine ⟨1109957338616320232722331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 47358179780962996596152789 1109957338616320232722331)
    ·
      refine ⟨1664936007924480349083497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1109957338616320232722331 1664936007924480349083497)
      ·
        refine ⟨1248702005943360261812623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1664936007924480349083497 1248702005943360261812623)
        ·
          refine ⟨1873053008915040392718935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1248702005943360261812623 1873053008915040392718935)
          ·
            refine ⟨2809579513372560589078403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1873053008915040392718935 2809579513372560589078403)
            ·
              refine ⟨4214369270058840883617605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2809579513372560589078403 4214369270058840883617605)
              ·
                refine ⟨790194238136032665678301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4214369270058840883617605 790194238136032665678301)
                ·
                  refine ⟨296322839301012249629363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 790194238136032665678301 296322839301012249629363)
                  ·
                    rfl

theorem cell21_1298445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_1298445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1298445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1298445 prefixEnd_1298445 := by exact prefixLift 1298445
  have htrace : WordTrace (prefixWord ++ tailWord_1298445) baseStart_1298445 baseEnd_1298445 := by
    simpa [prefixWord, tailWord_1298445, baseEnd_1298445] using wordTrace_append hprefix tailTrace_1298445
  have hstable : (prefixWord ++ tailWord_1298445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298445).length < 2 ^ (prefixWord ++ tailWord_1298445).sum := by decide
  have hdescent : baseEnd_1298445 < baseStart_1298445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298467 : List Nat := [1, 1, 1, 4, 3, 1, 1, 5, 4]
def baseStart_1298467 : Nat := 118140960795 + 1298467 * 2 ^ 59
def prefixEnd_1298467 : Nat := 4983230072969 + 3 ^ 40 * 1298467 * 2
def baseEnd_1298467 : Nat := 296327860000745100262651

theorem tailTrace_1298467 : CollatzResearch.WordTrace tailWord_1298467 prefixEnd_1298467 296327860000745100262651 := by
  unfold tailWord_1298467
  simp only [CollatzResearch.WordTrace]
  refine ⟨47358982186883294353453655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31572654791255529568969103 47358982186883294353453655)
  ·
    refine ⟨71038473280324941530180483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47358982186883294353453655 71038473280324941530180483)
    ·
      refine ⟨106557709920487412295270725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71038473280324941530180483 106557709920487412295270725)
      ·
        refine ⟨19979570610091389805363261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106557709920487412295270725 19979570610091389805363261)
        ·
          refine ⟨7492338978784271177011223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19979570610091389805363261 7492338978784271177011223)
          ·
            refine ⟨11238508468176406765516835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7492338978784271177011223 11238508468176406765516835)
            ·
              refine ⟨16857762702264610148275253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11238508468176406765516835 16857762702264610148275253)
              ·
                refine ⟨1580415253337307201400805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16857762702264610148275253 1580415253337307201400805)
                ·
                  refine ⟨296327860000745100262651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1580415253337307201400805 296327860000745100262651)
                  ·
                    rfl

theorem cell21_1298467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 4].length) (baseStart_1298467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1298467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1298467 prefixEnd_1298467 := by exact prefixLift 1298467
  have htrace : WordTrace (prefixWord ++ tailWord_1298467) baseStart_1298467 baseEnd_1298467 := by
    simpa [prefixWord, tailWord_1298467, baseEnd_1298467] using wordTrace_append hprefix tailTrace_1298467
  have hstable : (prefixWord ++ tailWord_1298467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298467).length < 2 ^ (prefixWord ++ tailWord_1298467).sum := by decide
  have hdescent : baseEnd_1298467 < baseStart_1298467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298546 : List Nat := [3, 2, 1, 2, 2, 2, 3, 3, 3]
def baseStart_1298546 : Nat := 118140960795 + 1298546 * 2 ^ 59
def prefixEnd_1298546 : Nat := 4983230072969 + 3 ^ 40 * 1298546 * 2
def baseEnd_1298546 : Nat := 296345888877058518445823

theorem tailTrace_1298546 : CollatzResearch.WordTrace tailWord_1298546 prefixEnd_1298546 296345888877058518445823 := by
  unfold tailWord_1298546
  simp only [CollatzResearch.WordTrace]
  refine ⟨11840465888399272711394873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31574575702398060563719661 11840465888399272711394873)
  ·
    refine ⟨8880349416299454533546155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11840465888399272711394873 8880349416299454533546155)
    ·
      refine ⟨13320524124449181800319233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8880349416299454533546155 13320524124449181800319233)
      ·
        refine ⟨9990393093336886350239425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13320524124449181800319233 9990393093336886350239425)
        ·
          refine ⟨7492794820002664762679569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9990393093336886350239425 7492794820002664762679569)
          ·
            refine ⟨5619596115001998572009677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7492794820002664762679569 5619596115001998572009677)
            ·
              refine ⟨2107348543125749464503629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5619596115001998572009677 2107348543125749464503629)
              ·
                refine ⟨790255703672156049188861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2107348543125749464503629 790255703672156049188861)
                ·
                  refine ⟨296345888877058518445823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 790255703672156049188861 296345888877058518445823)
                  ·
                    rfl

theorem cell21_1298546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_1298546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1298546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1298546 prefixEnd_1298546 := by exact prefixLift 1298546
  have htrace : WordTrace (prefixWord ++ tailWord_1298546) baseStart_1298546 baseEnd_1298546 := by
    simpa [prefixWord, tailWord_1298546, baseEnd_1298546] using wordTrace_append hprefix tailTrace_1298546
  have hstable : (prefixWord ++ tailWord_1298546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298546).length < 2 ^ (prefixWord ++ tailWord_1298546).sum := by decide
  have hdescent : baseEnd_1298546 < baseStart_1298546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298557 : List Nat := [1, 4, 1, 1, 3, 2, 9]
def baseStart_1298557 : Nat := 118140960795 + 1298557 * 2 ^ 59
def prefixEnd_1298557 : Nat := 4983230072969 + 3 ^ 40 * 1298557 * 2
def baseEnd_1298557 : Nat := 32927599914102771529163

theorem tailTrace_1298557 : CollatzResearch.WordTrace tailWord_1298557 prefixEnd_1298557 32927599914102771529163 := by
  unfold tailWord_1298557
  simp only [CollatzResearch.WordTrace]
  refine ⟨47362264756557239724229925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31574843171038159816153283 47362264756557239724229925)
  ·
    refine ⟨8880424641854482448293111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47362264756557239724229925 8880424641854482448293111)
    ·
      refine ⟨13320636962781723672439667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8880424641854482448293111 13320636962781723672439667)
      ·
        refine ⟨19980955444172585508659501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13320636962781723672439667 19980955444172585508659501)
        ·
          refine ⟨7492858291564719565747313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19980955444172585508659501 7492858291564719565747313)
          ·
            refine ⟨5619643718673539674310485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7492858291564719565747313 5619643718673539674310485)
            ·
              refine ⟨32927599914102771529163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5619643718673539674310485 32927599914102771529163)
              ·
                rfl

theorem cell21_1298557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 9].length) (baseStart_1298557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1298557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1298557 prefixEnd_1298557 := by exact prefixLift 1298557
  have htrace : WordTrace (prefixWord ++ tailWord_1298557) baseStart_1298557 baseEnd_1298557 := by
    simpa [prefixWord, tailWord_1298557, baseEnd_1298557] using wordTrace_append hprefix tailTrace_1298557
  have hstable : (prefixWord ++ tailWord_1298557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298557).length < 2 ^ (prefixWord ++ tailWord_1298557).sum := by decide
  have hdescent : baseEnd_1298557 < baseStart_1298557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298588 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 7]
def baseStart_1298588 : Nat := 118140960795 + 1298588 * 2 ^ 59
def prefixEnd_1298588 : Nat := 4983230072969 + 3 ^ 40 * 1298588 * 2
def baseEnd_1298588 : Nat := 296355473849275778745737

theorem tailTrace_1298588 : CollatzResearch.WordTrace tailWord_1298588 prefixEnd_1298588 296355473849275778745737 := by
  unfold tailWord_1298588
  simp only [CollatzResearch.WordTrace]
  refine ⟨23681697709722466009304209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31575596946296621345738945 23681697709722466009304209)
  ·
    refine ⟨17761273282291849506978157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23681697709722466009304209 17761273282291849506978157)
    ·
      refine ⟨6660477480859443565116809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17761273282291849506978157 6660477480859443565116809)
      ·
        refine ⟨4995358110644582673837607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6660477480859443565116809 4995358110644582673837607)
        ·
          refine ⟨7493037165966874010756411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4995358110644582673837607 7493037165966874010756411)
          ·
            refine ⟨11239555748950311016134617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7493037165966874010756411 11239555748950311016134617)
            ·
              refine ⟨8429666811712733262100963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11239555748950311016134617 8429666811712733262100963)
              ·
                refine ⟨12644500217569099893151445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8429666811712733262100963 12644500217569099893151445)
                ·
                  refine ⟨296355473849275778745737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12644500217569099893151445 296355473849275778745737)
                  ·
                    rfl

theorem cell21_1298588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_1298588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1298588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1298588 prefixEnd_1298588 := by exact prefixLift 1298588
  have htrace : WordTrace (prefixWord ++ tailWord_1298588) baseStart_1298588 baseEnd_1298588 := by
    simpa [prefixWord, tailWord_1298588, baseEnd_1298588] using wordTrace_append hprefix tailTrace_1298588
  have hstable : (prefixWord ++ tailWord_1298588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298588).length < 2 ^ (prefixWord ++ tailWord_1298588).sum := by decide
  have hdescent : baseEnd_1298588 < baseStart_1298588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298619 : List Nat := [1, 1, 1, 1, 1, 2, 8, 2, 4]
def baseStart_1298619 : Nat := 118140960795 + 1298619 * 2 ^ 59
def prefixEnd_1298619 : Nat := 4983230072969 + 3 ^ 40 * 1298619 * 2
def baseEnd_1298619 : Nat := 296362548471626613729007

theorem tailTrace_1298619 : CollatzResearch.WordTrace tailWord_1298619 prefixEnd_1298619 296362548471626613729007 := by
  unfold tailWord_1298619
  simp only [CollatzResearch.WordTrace]
  refine ⟨47364526082332624312986911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31576350721555082875324607 47364526082332624312986911)
  ·
    refine ⟨71046789123498936469480367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47364526082332624312986911 71046789123498936469480367)
    ·
      refine ⟨106570183685248404704220551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71046789123498936469480367 106570183685248404704220551)
      ·
        refine ⟨159855275527872607056330827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106570183685248404704220551 159855275527872607056330827)
        ·
          refine ⟨239782913291808910584496241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159855275527872607056330827 239782913291808910584496241)
          ·
            refine ⟨179837184968856682938372181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239782913291808910584496241 179837184968856682938372181)
            ·
              refine ⟨2107467011353789253184049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 179837184968856682938372181 2107467011353789253184049)
              ·
                refine ⟨1580600258515341939888037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2107467011353789253184049 1580600258515341939888037)
                ·
                  refine ⟨296362548471626613729007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1580600258515341939888037 296362548471626613729007)
                  ·
                    rfl

theorem cell21_1298619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 4].length) (baseStart_1298619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1298619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1298619 prefixEnd_1298619 := by exact prefixLift 1298619
  have htrace : WordTrace (prefixWord ++ tailWord_1298619) baseStart_1298619 baseEnd_1298619 := by
    simpa [prefixWord, tailWord_1298619, baseEnd_1298619] using wordTrace_append hprefix tailTrace_1298619
  have hstable : (prefixWord ++ tailWord_1298619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298619).length < 2 ^ (prefixWord ++ tailWord_1298619).sum := by decide
  have hdescent : baseEnd_1298619 < baseStart_1298619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298791 : List Nat := [1, 1, 5, 1, 3, 3, 2, 2, 3]
def baseStart_1298791 : Nat := 118140960795 + 1298791 * 2 ^ 59
def prefixEnd_1298791 : Nat := 4983230072969 + 3 ^ 40 * 1298791 * 2
def baseEnd_1298791 : Nat := 296401801214992536861989

theorem tailTrace_1298791 : CollatzResearch.WordTrace tailWord_1298791 prefixEnd_1298791 296401801214992536861989 := by
  unfold tailWord_1298791
  simp only [CollatzResearch.WordTrace]
  refine ⟨47370799437709497688248227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31580532958472998458832151 47370799437709497688248227)
  ·
    refine ⟨71056199156564246532372341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47370799437709497688248227 71056199156564246532372341)
    ·
      refine ⟨6661518670927898112409907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71056199156564246532372341 6661518670927898112409907)
      ·
        refine ⟨9992278006391847168614861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6661518670927898112409907 9992278006391847168614861)
        ·
          refine ⟨3747104252396942688230573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9992278006391847168614861 3747104252396942688230573)
          ·
            refine ⟨1405164094648853508086465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3747104252396942688230573 1405164094648853508086465)
            ·
              refine ⟨1053873070986640131064849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1405164094648853508086465 1053873070986640131064849)
              ·
                refine ⟨790404803239980098298637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1053873070986640131064849 790404803239980098298637)
                ·
                  refine ⟨296401801214992536861989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 790404803239980098298637 296401801214992536861989)
                  ·
                    rfl

theorem cell21_1298791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 3].length) (baseStart_1298791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1298791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1298791 prefixEnd_1298791 := by exact prefixLift 1298791
  have htrace : WordTrace (prefixWord ++ tailWord_1298791) baseStart_1298791 baseEnd_1298791 := by
    simpa [prefixWord, tailWord_1298791, baseEnd_1298791] using wordTrace_append hprefix tailTrace_1298791
  have hstable : (prefixWord ++ tailWord_1298791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298791).length < 2 ^ (prefixWord ++ tailWord_1298791).sum := by decide
  have hdescent : baseEnd_1298791 < baseStart_1298791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298802 : List Nat := [3, 2, 1, 2, 1, 5, 1, 6]
def baseStart_1298802 : Nat := 118140960795 + 1298802 * 2 ^ 59
def prefixEnd_1298802 : Nat := 4983230072969 + 3 ^ 40 * 1298802 * 2
def baseEnd_1298802 : Nat := 98801437188286320726211

theorem tailTrace_1298802 : CollatzResearch.WordTrace tailWord_1298802 prefixEnd_1298802 98801437188286320726211 := by
  unfold tailWord_1298802
  simp only [CollatzResearch.WordTrace]
  refine ⟨11842800160167411641724665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31580800427113097711265773 11842800160167411641724665)
  ·
    refine ⟨8882100120125558731293499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11842800160167411641724665 8882100120125558731293499)
    ·
      refine ⟨13323150180188338096940249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8882100120125558731293499 13323150180188338096940249)
      ·
        refine ⟨9992362635141253572705187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13323150180188338096940249 9992362635141253572705187)
        ·
          refine ⟨14988543952711880359057781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9992362635141253572705187 14988543952711880359057781)
          ·
            refine ⟨1405175995566738783661667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14988543952711880359057781 1405175995566738783661667)
            ·
              refine ⟨2107763993350108175492501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405175995566738783661667 2107763993350108175492501)
              ·
                refine ⟨98801437188286320726211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2107763993350108175492501 98801437188286320726211)
                ·
                  rfl

theorem cell21_1298802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_1298802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1298802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1298802 prefixEnd_1298802 := by exact prefixLift 1298802
  have htrace : WordTrace (prefixWord ++ tailWord_1298802) baseStart_1298802 baseEnd_1298802 := by
    simpa [prefixWord, tailWord_1298802, baseEnd_1298802] using wordTrace_append hprefix tailTrace_1298802
  have hstable : (prefixWord ++ tailWord_1298802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298802).length < 2 ^ (prefixWord ++ tailWord_1298802).sum := by decide
  have hdescent : baseEnd_1298802 < baseStart_1298802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298878 : List Nat := [4, 2, 1, 1, 1, 1, 6, 5]
def baseStart_1298878 : Nat := 118140960795 + 1298878 * 2 ^ 59
def prefixEnd_1298878 : Nat := 4983230072969 + 3 ^ 40 * 1298878 * 2
def baseEnd_1298878 : Nat := 98807218600099906303937

theorem tailTrace_1298878 : CollatzResearch.WordTrace tailWord_1298878 prefixEnd_1298878 98807218600099906303937 := by
  unfold tailWord_1298878
  simp only [CollatzResearch.WordTrace]
  refine ⟨5921746573549288943333161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31582648392262874364443525 5921746573549288943333161)
  ·
    refine ⟨4441309930161966707499871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5921746573549288943333161 4441309930161966707499871)
    ·
      refine ⟨6661964895242950061249807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4441309930161966707499871 6661964895242950061249807)
      ·
        refine ⟨9992947342864425091874711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6661964895242950061249807 9992947342864425091874711)
        ·
          refine ⟨14989421014296637637812067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9992947342864425091874711 14989421014296637637812067)
          ·
            refine ⟨22484131521444956456718101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14989421014296637637812067 22484131521444956456718101)
            ·
              refine ⟨1053943665067732333908661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22484131521444956456718101 1053943665067732333908661)
              ·
                refine ⟨98807218600099906303937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1053943665067732333908661 98807218600099906303937)
                ·
                  rfl

theorem cell21_1298878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_1298878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1298878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1298878 prefixEnd_1298878 := by exact prefixLift 1298878
  have htrace : WordTrace (prefixWord ++ tailWord_1298878) baseStart_1298878 baseEnd_1298878 := by
    simpa [prefixWord, tailWord_1298878, baseEnd_1298878] using wordTrace_append hprefix tailTrace_1298878
  have hstable : (prefixWord ++ tailWord_1298878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298878).length < 2 ^ (prefixWord ++ tailWord_1298878).sum := by decide
  have hdescent : baseEnd_1298878 < baseStart_1298878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298884 : List Nat := [2, 3, 3, 2, 3, 1, 1, 3, 3]
def baseStart_1298884 : Nat := 118140960795 + 1298884 * 2 ^ 59
def prefixEnd_1298884 : Nat := 4983230072969 + 3 ^ 40 * 1298884 * 2
def baseEnd_1298884 : Nat := 296423025082045041811799

theorem tailTrace_1298884 : CollatzResearch.WordTrace tailWord_1298884 prefixEnd_1298884 296423025082045041811799 := by
  unfold tailWord_1298884
  simp only [CollatzResearch.WordTrace]
  refine ⟨23687095713186287285691853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31582794284248383047589137 23687095713186287285691853)
  ·
    refine ⟨8882660892444857732134445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23687095713186287285691853 8882660892444857732134445)
    ·
      refine ⟨3330997834666821649550417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8882660892444857732134445 3330997834666821649550417)
      ·
        refine ⟨2498248376000116237162813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3330997834666821649550417 2498248376000116237162813)
        ·
          refine ⟨936843141000043588936055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2498248376000116237162813 936843141000043588936055)
          ·
            refine ⟨1405264711500065383404083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936843141000043588936055 1405264711500065383404083)
            ·
              refine ⟨2107897067250098075106125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405264711500065383404083 2107897067250098075106125)
              ·
                refine ⟨790461400218786778164797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2107897067250098075106125 790461400218786778164797)
                ·
                  refine ⟨296423025082045041811799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 790461400218786778164797 296423025082045041811799)
                  ·
                    rfl

theorem cell21_1298884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_1298884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1298884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1298884 prefixEnd_1298884 := by exact prefixLift 1298884
  have htrace : WordTrace (prefixWord ++ tailWord_1298884) baseStart_1298884 baseEnd_1298884 := by
    simpa [prefixWord, tailWord_1298884, baseEnd_1298884] using wordTrace_append hprefix tailTrace_1298884
  have hstable : (prefixWord ++ tailWord_1298884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298884).length < 2 ^ (prefixWord ++ tailWord_1298884).sum := by decide
  have hdescent : baseEnd_1298884 < baseStart_1298884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298906 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 6]
def baseStart_1298906 : Nat := 118140960795 + 1298906 * 2 ^ 59
def prefixEnd_1298906 : Nat := 4983230072969 + 3 ^ 40 * 1298906 * 2
def baseEnd_1298906 : Nat := 296428045781777892445087

theorem tailTrace_1298906 : CollatzResearch.WordTrace tailWord_1298906 prefixEnd_1298906 296428045781777892445087 := by
  unfold tailWord_1298906
  simp only [CollatzResearch.WordTrace]
  refine ⟨11843748458073218082171143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31583329221528581552456381 11843748458073218082171143)
  ·
    refine ⟨17765622687109827123256715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11843748458073218082171143 17765622687109827123256715)
    ·
      refine ⟨26648434030664740684885073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17765622687109827123256715 26648434030664740684885073)
      ·
        refine ⟨19986325522998555513663805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26648434030664740684885073 19986325522998555513663805)
        ·
          refine ⟨7494872071124458317623927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19986325522998555513663805 7494872071124458317623927)
          ·
            refine ⟨11242308106686687476435891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7494872071124458317623927 11242308106686687476435891)
            ·
              refine ⟨16863462160030031214653837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11242308106686687476435891 16863462160030031214653837)
              ·
                refine ⟨6323798310011261705495189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16863462160030031214653837 6323798310011261705495189)
                ·
                  refine ⟨296428045781777892445087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6323798310011261705495189 296428045781777892445087)
                  ·
                    rfl

theorem cell21_1298906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_1298906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1298906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1298906 prefixEnd_1298906 := by exact prefixLift 1298906
  have htrace : WordTrace (prefixWord ++ tailWord_1298906) baseStart_1298906 baseEnd_1298906 := by
    simpa [prefixWord, tailWord_1298906, baseEnd_1298906] using wordTrace_append hprefix tailTrace_1298906
  have hstable : (prefixWord ++ tailWord_1298906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298906).length < 2 ^ (prefixWord ++ tailWord_1298906).sum := by decide
  have hdescent : baseEnd_1298906 < baseStart_1298906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298957 : List Nat := [1, 7, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1298957 : Nat := 118140960795 + 1298957 * 2 ^ 59
def prefixEnd_1298957 : Nat := 4983230072969 + 3 ^ 40 * 1298957 * 2
def baseEnd_1298957 : Nat := 296439684676613137094983

theorem tailTrace_1298957 : CollatzResearch.WordTrace tailWord_1298957 prefixEnd_1298957 296439684676613137094983 := by
  unfold tailWord_1298957
  simp only [CollatzResearch.WordTrace]
  refine ⟨47376853955108108038791125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31584569303405405359194083 47376853955108108038791125)
  ·
    refine ⟨1110395014572846282159167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 47376853955108108038791125 1110395014572846282159167)
    ·
      refine ⟨1665592521859269423238751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1110395014572846282159167 1665592521859269423238751)
      ·
        refine ⟨2498388782788904134858127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1665592521859269423238751 2498388782788904134858127)
        ·
          refine ⟨3747583174183356202287191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2498388782788904134858127 3747583174183356202287191)
          ·
            refine ⟨5621374761275034303430787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3747583174183356202287191 5621374761275034303430787)
            ·
              refine ⟨8432062141912551455146181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5621374761275034303430787 8432062141912551455146181)
              ·
                refine ⟨1581011651608603397839909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8432062141912551455146181 1581011651608603397839909)
                ·
                  refine ⟨296439684676613137094983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1581011651608603397839909 296439684676613137094983)
                  ·
                    rfl

theorem cell21_1298957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1298957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1298957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1298957 prefixEnd_1298957 := by exact prefixLift 1298957
  have htrace : WordTrace (prefixWord ++ tailWord_1298957) baseStart_1298957 baseEnd_1298957 := by
    simpa [prefixWord, tailWord_1298957, baseEnd_1298957] using wordTrace_append hprefix tailTrace_1298957
  have hstable : (prefixWord ++ tailWord_1298957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298957).length < 2 ^ (prefixWord ++ tailWord_1298957).sum := by decide
  have hdescent : baseEnd_1298957 < baseStart_1298957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299072 : List Nat := [2, 1, 1, 2, 1, 5, 9]
def baseStart_1299072 : Nat := 118140960795 + 1299072 * 2 ^ 59
def prefixEnd_1299072 : Nat := 4983230072969 + 3 ^ 40 * 1299072 * 2
def baseEnd_1299072 : Nat := 32940658804822054742009

theorem tailTrace_1299072 : CollatzResearch.WordTrace tailWord_1299072 prefixEnd_1299072 32940658804822054742009 := by
  unfold tailWord_1299072
  simp only [CollatzResearch.WordTrace]
  refine ⟨23690524174845741339613735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31587365566460988452818313 23690524174845741339613735)
  ·
    refine ⟨35535786262268612009420603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23690524174845741339613735 35535786262268612009420603)
    ·
      refine ⟨53303679393402918014130905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35535786262268612009420603 53303679393402918014130905)
      ·
        refine ⟨39977759545052188510598179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53303679393402918014130905 39977759545052188510598179)
        ·
          refine ⟨59966639317578282765897269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39977759545052188510598179 59966639317578282765897269)
          ·
            refine ⟨5621872436022964009302869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59966639317578282765897269 5621872436022964009302869)
            ·
              refine ⟨32940658804822054742009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5621872436022964009302869 32940658804822054742009)
              ·
                rfl

theorem cell21_1299072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 9].length) (baseStart_1299072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299072 prefixEnd_1299072 := by exact prefixLift 1299072
  have htrace : WordTrace (prefixWord ++ tailWord_1299072) baseStart_1299072 baseEnd_1299072 := by
    simpa [prefixWord, tailWord_1299072, baseEnd_1299072] using wordTrace_append hprefix tailTrace_1299072
  have hstable : (prefixWord ++ tailWord_1299072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299072).length < 2 ^ (prefixWord ++ tailWord_1299072).sum := by decide
  have hdescent : baseEnd_1299072 < baseStart_1299072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299092 : List Nat := [2, 4, 2, 2, 1, 2, 1, 3, 4]
def baseStart_1299092 : Nat := 118140960795 + 1299092 * 2 ^ 59
def prefixEnd_1299092 : Nat := 4983230072969 + 3 ^ 40 * 1299092 * 2
def baseEnd_1299092 : Nat := 296470493515882902344707

theorem tailTrace_1299092 : CollatzResearch.WordTrace tailWord_1299092 prefixEnd_1299092 296470493515882902344707 := by
  unfold tailWord_1299092
  simp only [CollatzResearch.WordTrace]
  refine ⟨23690888904809513047477765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31587851873079350729970353 23690888904809513047477765)
  ·
    refine ⟨4442041669651783696402081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23690888904809513047477765 4442041669651783696402081)
    ·
      refine ⟨3331531252238837772301561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4442041669651783696402081 3331531252238837772301561)
      ·
        refine ⟨2498648439179128329226171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3331531252238837772301561 2498648439179128329226171)
        ·
          refine ⟨3747972658768692493839257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2498648439179128329226171 3747972658768692493839257)
          ·
            refine ⟨2810979494076519370379443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3747972658768692493839257 2810979494076519370379443)
            ·
              refine ⟨4216469241114779055569165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2810979494076519370379443 4216469241114779055569165)
              ·
                refine ⟨1581175965418042145838437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4216469241114779055569165 1581175965418042145838437)
                ·
                  refine ⟨296470493515882902344707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1581175965418042145838437 296470493515882902344707)
                  ·
                    rfl

theorem cell21_1299092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_1299092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299092 prefixEnd_1299092 := by exact prefixLift 1299092
  have htrace : WordTrace (prefixWord ++ tailWord_1299092) baseStart_1299092 baseEnd_1299092 := by
    simpa [prefixWord, tailWord_1299092, baseEnd_1299092] using wordTrace_append hprefix tailTrace_1299092
  have hstable : (prefixWord ++ tailWord_1299092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299092).length < 2 ^ (prefixWord ++ tailWord_1299092).sum := by decide
  have hdescent : baseEnd_1299092 < baseStart_1299092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299120 : List Nat := [2, 1, 1, 1, 2, 1, 3, 7, 3]
def baseStart_1299120 : Nat := 118140960795 + 1299120 * 2 ^ 59
def prefixEnd_1299120 : Nat := 4983230072969 + 3 ^ 40 * 1299120 * 2
def baseEnd_1299120 : Nat := 296476883497361075877983

theorem tailTrace_1299120 : CollatzResearch.WordTrace tailWord_1299120 prefixEnd_1299120 296476883497361075877983 := by
  unfold tailWord_1299120
  simp only [CollatzResearch.WordTrace]
  refine ⟨23691399526758793438487407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31588532702345057917983209 23691399526758793438487407)
  ·
    refine ⟨35537099290138190157731111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23691399526758793438487407 35537099290138190157731111)
    ·
      refine ⟨53305648935207285236596667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35537099290138190157731111 53305648935207285236596667)
      ·
        refine ⟨79958473402810927854895001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53305648935207285236596667 79958473402810927854895001)
        ·
          refine ⟨59968855052108195891171251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79958473402810927854895001 59968855052108195891171251)
          ·
            refine ⟨89953282578162293836756877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59968855052108195891171251 89953282578162293836756877)
            ·
              refine ⟨33732480966810860188783829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89953282578162293836756877 33732480966810860188783829)
              ·
                refine ⟨790605022659629535674621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 33732480966810860188783829 790605022659629535674621)
                ·
                  refine ⟨296476883497361075877983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 790605022659629535674621 296476883497361075877983)
                  ·
                    rfl

theorem cell21_1299120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 3].length) (baseStart_1299120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299120 prefixEnd_1299120 := by exact prefixLift 1299120
  have htrace : WordTrace (prefixWord ++ tailWord_1299120) baseStart_1299120 baseEnd_1299120 := by
    simpa [prefixWord, tailWord_1299120, baseEnd_1299120] using wordTrace_append hprefix tailTrace_1299120
  have hstable : (prefixWord ++ tailWord_1299120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299120).length < 2 ^ (prefixWord ++ tailWord_1299120).sum := by decide
  have hdescent : baseEnd_1299120 < baseStart_1299120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299196 : List Nat := [2, 2, 2, 1, 3, 3, 2, 1, 5]
def baseStart_1299196 : Nat := 118140960795 + 1299196 * 2 ^ 59
def prefixEnd_1299196 : Nat := 4983230072969 + 3 ^ 40 * 1299196 * 2
def baseEnd_1299196 : Nat := 296494227732801832611161

theorem tailTrace_1299196 : CollatzResearch.WordTrace tailWord_1299196 prefixEnd_1299196 296494227732801832611161 := by
  unfold tailWord_1299196
  simp only [CollatzResearch.WordTrace]
  refine ⟨23692785500621125928370721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31590380667494834571160961 23692785500621125928370721)
  ·
    refine ⟨17769589125465844446278041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23692785500621125928370721 17769589125465844446278041)
    ·
      refine ⟨13327191844099383334708531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17769589125465844446278041 13327191844099383334708531)
      ·
        refine ⟨19990787766149075002062797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13327191844099383334708531 19990787766149075002062797)
        ·
          refine ⟨7496545412305903125773549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19990787766149075002062797 7496545412305903125773549)
          ·
            refine ⟨2811204529614713672165081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7496545412305903125773549 2811204529614713672165081)
            ·
              refine ⟨2108403397211035254123811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2811204529614713672165081 2108403397211035254123811)
              ·
                refine ⟨3162605095816552881185717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2108403397211035254123811 3162605095816552881185717)
                ·
                  refine ⟨296494227732801832611161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3162605095816552881185717 296494227732801832611161)
                  ·
                    rfl

theorem cell21_1299196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_1299196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299196 prefixEnd_1299196 := by exact prefixLift 1299196
  have htrace : WordTrace (prefixWord ++ tailWord_1299196) baseStart_1299196 baseEnd_1299196 := by
    simpa [prefixWord, tailWord_1299196, baseEnd_1299196] using wordTrace_append hprefix tailTrace_1299196
  have hstable : (prefixWord ++ tailWord_1299196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299196).length < 2 ^ (prefixWord ++ tailWord_1299196).sum := by decide
  have hdescent : baseEnd_1299196 < baseStart_1299196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299261 : List Nat := [1, 4, 1, 4, 2, 2, 2, 1, 4]
def baseStart_1299261 : Nat := 118140960795 + 1299261 * 2 ^ 59
def prefixEnd_1299261 : Nat := 4983230072969 + 3 ^ 40 * 1299261 * 2
def baseEnd_1299261 : Nat := 296509061618376164027695

theorem tailTrace_1299261 : CollatzResearch.WordTrace tailWord_1299261 prefixEnd_1299261 296509061618376164027695 := by
  unfold tailWord_1299261
  simp only [CollatzResearch.WordTrace]
  refine ⟨47387941746006767957857637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31591961164004511971905091 47387941746006767957857637)
  ·
    refine ⟨8885239077376268992098307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47387941746006767957857637 8885239077376268992098307)
    ·
      refine ⟨13327858616064403488147461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8885239077376268992098307 13327858616064403488147461)
      ·
        refine ⟨2498973490512075654027649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13327858616064403488147461 2498973490512075654027649)
        ·
          refine ⟨1874230117884056740520737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2498973490512075654027649 1874230117884056740520737)
          ·
            refine ⟨1405672588413042555390553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1874230117884056740520737 1405672588413042555390553)
            ·
              refine ⟨1054254441309781916542915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1405672588413042555390553 1054254441309781916542915)
              ·
                refine ⟨1581381661964672874814373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054254441309781916542915 1581381661964672874814373)
                ·
                  refine ⟨296509061618376164027695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1581381661964672874814373 296509061618376164027695)
                  ·
                    rfl

theorem cell21_1299261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_1299261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299261 prefixEnd_1299261 := by exact prefixLift 1299261
  have htrace : WordTrace (prefixWord ++ tailWord_1299261) baseStart_1299261 baseEnd_1299261 := by
    simpa [prefixWord, tailWord_1299261, baseEnd_1299261] using wordTrace_append hprefix tailTrace_1299261
  have hstable : (prefixWord ++ tailWord_1299261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299261).length < 2 ^ (prefixWord ++ tailWord_1299261).sum := by decide
  have hdescent : baseEnd_1299261 < baseStart_1299261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299269 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 8]
def baseStart_1299269 : Nat := 118140960795 + 1299269 * 2 ^ 59
def prefixEnd_1299269 : Nat := 4983230072969 + 3 ^ 40 * 1299269 * 2
def baseEnd_1299269 : Nat := 296510887327369927894345

theorem tailTrace_1299269 : CollatzResearch.WordTrace tailWord_1299269 prefixEnd_1299269 296510887327369927894345 := by
  unfold tailWord_1299269
  simp only [CollatzResearch.WordTrace]
  refine ⟨47388233529977785324148861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31592155686651856882765907 47388233529977785324148861)
  ·
    refine ⟨17770587573741669496555823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47388233529977785324148861 17770587573741669496555823)
    ·
      refine ⟨26655881360612504244833735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17770587573741669496555823 26655881360612504244833735)
      ·
        refine ⟨39983822040918756367250603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26655881360612504244833735 39983822040918756367250603)
        ·
          refine ⟨59975733061378134550875905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39983822040918756367250603 59975733061378134550875905)
          ·
            refine ⟨44981799796033600913156929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59975733061378134550875905 44981799796033600913156929)
            ·
              refine ⟨33736349847025200684867697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44981799796033600913156929 33736349847025200684867697)
              ·
                refine ⟨25302262385268900513650773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33736349847025200684867697 25302262385268900513650773)
                ·
                  refine ⟨296510887327369927894345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25302262385268900513650773 296510887327369927894345)
                  ·
                    rfl

theorem cell21_1299269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_1299269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299269 prefixEnd_1299269 := by exact prefixLift 1299269
  have htrace : WordTrace (prefixWord ++ tailWord_1299269) baseStart_1299269 baseEnd_1299269 := by
    simpa [prefixWord, tailWord_1299269, baseEnd_1299269] using wordTrace_append hprefix tailTrace_1299269
  have hstable : (prefixWord ++ tailWord_1299269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299269).length < 2 ^ (prefixWord ++ tailWord_1299269).sum := by decide
  have hdescent : baseEnd_1299269 < baseStart_1299269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299300 : List Nat := [2, 3, 1, 1, 4, 10]
def baseStart_1299300 : Nat := 118140960795 + 1299300 * 2 ^ 59
def prefixEnd_1299300 : Nat := 4983230072969 + 3 ^ 40 * 1299300 * 2
def baseEnd_1299300 : Nat := 10982146738878546773245

theorem tailTrace_1299300 : CollatzResearch.WordTrace tailWord_1299300 prefixEnd_1299300 10982146738878546773245 := by
  unfold tailWord_1299300
  simp only [CollatzResearch.WordTrace]
  refine ⟨23694682096432738809263677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31592909461910318412351569 23694682096432738809263677)
  ·
    refine ⟨8885505786162277053473879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23694682096432738809263677 8885505786162277053473879)
    ·
      refine ⟨13328258679243415580210819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8885505786162277053473879 13328258679243415580210819)
      ·
        refine ⟨19992388018865123370316229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13328258679243415580210819 19992388018865123370316229)
        ·
          refine ⟨3748572753537210631934293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19992388018865123370316229 3748572753537210631934293)
          ·
            refine ⟨10982146738878546773245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3748572753537210631934293 10982146738878546773245)
            ·
              rfl

theorem cell21_1299300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 10].length) (baseStart_1299300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299300 prefixEnd_1299300 := by exact prefixLift 1299300
  have htrace : WordTrace (prefixWord ++ tailWord_1299300) baseStart_1299300 baseEnd_1299300 := by
    simpa [prefixWord, tailWord_1299300, baseEnd_1299300] using wordTrace_append hprefix tailTrace_1299300
  have hstable : (prefixWord ++ tailWord_1299300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299300).length < 2 ^ (prefixWord ++ tailWord_1299300).sum := by decide
  have hdescent : baseEnd_1299300 < baseStart_1299300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299303 : List Nat := [1, 1, 5, 1, 2, 3, 2, 2, 4]
def baseStart_1299303 : Nat := 118140960795 + 1299303 * 2 ^ 59
def prefixEnd_1299303 : Nat := 4983230072969 + 3 ^ 40 * 1299303 * 2
def baseEnd_1299303 : Nat := 296518646590593424327609

theorem tailTrace_1299303 : CollatzResearch.WordTrace tailWord_1299303 prefixEnd_1299303 296518646590593424327609 := by
  unfold tailWord_1299303
  simp only [CollatzResearch.WordTrace]
  refine ⟨47389473611854609130886563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31592982407903072753924375 47389473611854609130886563)
  ·
    refine ⟨71084210417781913696329845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47389473611854609130886563 71084210417781913696329845)
    ·
      refine ⟨6664144726667054409030923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71084210417781913696329845 6664144726667054409030923)
      ·
        refine ⟨9996217090000581613546385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6664144726667054409030923 9996217090000581613546385)
        ·
          refine ⟨7497162817500436210159789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9996217090000581613546385 7497162817500436210159789)
          ·
            refine ⟨2811436056562663578809921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7497162817500436210159789 2811436056562663578809921)
            ·
              refine ⟨2108577042421997684107441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2811436056562663578809921 2108577042421997684107441)
              ·
                refine ⟨1581432781816498263080581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2108577042421997684107441 1581432781816498263080581)
                ·
                  refine ⟨296518646590593424327609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1581432781816498263080581 296518646590593424327609)
                  ·
                    rfl

theorem cell21_1299303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 4].length) (baseStart_1299303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299303 prefixEnd_1299303 := by exact prefixLift 1299303
  have htrace : WordTrace (prefixWord ++ tailWord_1299303) baseStart_1299303 baseEnd_1299303 := by
    simpa [prefixWord, tailWord_1299303, baseEnd_1299303] using wordTrace_append hprefix tailTrace_1299303
  have hstable : (prefixWord ++ tailWord_1299303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299303).length < 2 ^ (prefixWord ++ tailWord_1299303).sum := by decide
  have hdescent : baseEnd_1299303 < baseStart_1299303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299317 : List Nat := [1, 3, 4, 1, 1, 2, 3, 6]
def baseStart_1299317 : Nat := 118140960795 + 1299317 * 2 ^ 59
def prefixEnd_1299317 : Nat := 4983230072969 + 3 ^ 40 * 1299317 * 2
def baseEnd_1299317 : Nat := 98840613860444170364749

theorem tailTrace_1299317 : CollatzResearch.WordTrace tailWord_1299317 prefixEnd_1299317 98840613860444170364749 := by
  unfold tailWord_1299317
  simp only [CollatzResearch.WordTrace]
  refine ⟨47389984233803889521896205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31593322822535926347930803 47389984233803889521896205)
  ·
    refine ⟨17771244087676458570711077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47389984233803889521896205 17771244087676458570711077)
    ·
      refine ⟨3332108266439335982008327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17771244087676458570711077 3332108266439335982008327)
      ·
        refine ⟨4998162399659003973012491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3332108266439335982008327 4998162399659003973012491)
        ·
          refine ⟨7497243599488505959518737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4998162399659003973012491 7497243599488505959518737)
          ·
            refine ⟨5622932699616379469639053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7497243599488505959518737 5622932699616379469639053)
            ·
              refine ⟨2108599762356142301114645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5622932699616379469639053 2108599762356142301114645)
              ·
                refine ⟨98840613860444170364749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2108599762356142301114645 98840613860444170364749)
                ·
                  rfl

theorem cell21_1299317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 6].length) (baseStart_1299317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299317 prefixEnd_1299317 := by exact prefixLift 1299317
  have htrace : WordTrace (prefixWord ++ tailWord_1299317) baseStart_1299317 baseEnd_1299317 := by
    simpa [prefixWord, tailWord_1299317, baseEnd_1299317] using wordTrace_append hprefix tailTrace_1299317
  have hstable : (prefixWord ++ tailWord_1299317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299317).length < 2 ^ (prefixWord ++ tailWord_1299317).sum := by decide
  have hdescent : baseEnd_1299317 < baseStart_1299317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299331 : List Nat := [1, 1, 1, 3, 4, 1, 3, 2, 5]
def baseStart_1299331 : Nat := 118140960795 + 1299331 * 2 ^ 59
def prefixEnd_1299331 : Nat := 4983230072969 + 3 ^ 40 * 1299331 * 2
def baseEnd_1299331 : Nat := 296525036572071597860885

theorem tailTrace_1299331 : CollatzResearch.WordTrace tailWord_1299331 prefixEnd_1299331 296525036572071597860885 := by
  unfold tailWord_1299331
  simp only [CollatzResearch.WordTrace]
  refine ⟨47390494855753169912905847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31593663237168779941937231 47390494855753169912905847)
  ·
    refine ⟨71085742283629754869358771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47390494855753169912905847 71085742283629754869358771)
    ·
      refine ⟨106628613425444632304038157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71085742283629754869358771 106628613425444632304038157)
      ·
        refine ⟨39985730034541737114014309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106628613425444632304038157 39985730034541737114014309)
        ·
          refine ⟨7497324381476575708877683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39985730034541737114014309 7497324381476575708877683)
          ·
            refine ⟨11245986572214863563316525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7497324381476575708877683 11245986572214863563316525)
            ·
              refine ⟨4217244964580573836243697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11245986572214863563316525 4217244964580573836243697)
              ·
                refine ⟨3162933723435430377182773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4217244964580573836243697 3162933723435430377182773)
                ·
                  refine ⟨296525036572071597860885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3162933723435430377182773 296525036572071597860885)
                  ·
                    rfl

theorem cell21_1299331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 5].length) (baseStart_1299331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299331 prefixEnd_1299331 := by exact prefixLift 1299331
  have htrace : WordTrace (prefixWord ++ tailWord_1299331) baseStart_1299331 baseEnd_1299331 := by
    simpa [prefixWord, tailWord_1299331, baseEnd_1299331] using wordTrace_append hprefix tailTrace_1299331
  have hstable : (prefixWord ++ tailWord_1299331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299331).length < 2 ^ (prefixWord ++ tailWord_1299331).sum := by decide
  have hdescent : baseEnd_1299331 < baseStart_1299331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299345 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 6]
def baseStart_1299345 : Nat := 118140960795 + 1299345 * 2 ^ 59
def prefixEnd_1299345 : Nat := 4983230072969 + 3 ^ 40 * 1299345 * 2
def baseEnd_1299345 : Nat := 296528231562810684627523

theorem tailTrace_1299345 : CollatzResearch.WordTrace tailWord_1299345 prefixEnd_1299345 296528231562810684627523 := by
  unfold tailWord_1299345
  simp only [CollatzResearch.WordTrace]
  refine ⟨47391005477702450303915489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31594003651801633535943659 47391005477702450303915489)
  ·
    refine ⟨35543254108276837727936617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47391005477702450303915489 35543254108276837727936617)
    ·
      refine ⟨26657440581207628295952463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35543254108276837727936617 26657440581207628295952463)
      ·
        refine ⟨39986160871811442443928695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26657440581207628295952463 39986160871811442443928695)
        ·
          refine ⟨59979241307717163665893043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39986160871811442443928695 59979241307717163665893043)
          ·
            refine ⟨89968861961575745498839565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59979241307717163665893043 89968861961575745498839565)
            ·
              refine ⟨33738323235590904562064837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89968861961575745498839565 33738323235590904562064837)
              ·
                refine ⟨6325935606673294605387157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33738323235590904562064837 6325935606673294605387157)
                ·
                  refine ⟨296528231562810684627523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6325935606673294605387157 296528231562810684627523)
                  ·
                    rfl

theorem cell21_1299345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_1299345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299345 prefixEnd_1299345 := by exact prefixLift 1299345
  have htrace : WordTrace (prefixWord ++ tailWord_1299345) baseStart_1299345 baseEnd_1299345 := by
    simpa [prefixWord, tailWord_1299345, baseEnd_1299345] using wordTrace_append hprefix tailTrace_1299345
  have hstable : (prefixWord ++ tailWord_1299345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299345).length < 2 ^ (prefixWord ++ tailWord_1299345).sum := by decide
  have hdescent : baseEnd_1299345 < baseStart_1299345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299452 : List Nat := [2, 2, 2, 1, 2, 3, 2, 7]
def baseStart_1299452 : Nat := 118140960795 + 1299452 * 2 ^ 59
def prefixEnd_1299452 : Nat := 4983230072969 + 3 ^ 40 * 1299452 * 2
def baseEnd_1299452 : Nat := 98850883473534092114657

theorem tailTrace_1299452 : CollatzResearch.WordTrace tailWord_1299452 prefixEnd_1299452 98850883473534092114657 := by
  unfold tailWord_1299452
  simp only [CollatzResearch.WordTrace]
  refine ⟨23697454044157403789030305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31596605392209871718707073 23697454044157403789030305)
  ·
    refine ⟨17773090533118052841772729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23697454044157403789030305 17773090533118052841772729)
    ·
      refine ⟨13329817899838539631329547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17773090533118052841772729 13329817899838539631329547)
      ·
        refine ⟨19994726849757809446994321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13329817899838539631329547 19994726849757809446994321)
        ·
          refine ⟨14996045137318357085245741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19994726849757809446994321 14996045137318357085245741)
          ·
            refine ⟨5623516926494383906967153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14996045137318357085245741 5623516926494383906967153)
            ·
              refine ⟨4217637694870787930225365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5623516926494383906967153 4217637694870787930225365)
              ·
                refine ⟨98850883473534092114657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4217637694870787930225365 98850883473534092114657)
                ·
                  rfl

theorem cell21_1299452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 7].length) (baseStart_1299452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299452 prefixEnd_1299452 := by exact prefixLift 1299452
  have htrace : WordTrace (prefixWord ++ tailWord_1299452) baseStart_1299452 baseEnd_1299452 := by
    simpa [prefixWord, tailWord_1299452, baseEnd_1299452] using wordTrace_append hprefix tailTrace_1299452
  have hstable : (prefixWord ++ tailWord_1299452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299452).length < 2 ^ (prefixWord ++ tailWord_1299452).sum := by decide
  have hdescent : baseEnd_1299452 < baseStart_1299452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299469 : List Nat := [1, 7, 1, 12]
def baseStart_1299469 : Nat := 118140960795 + 1299469 * 2 ^ 59
def prefixEnd_1299469 : Nat := 4983230072969 + 3 ^ 40 * 1299469 * 2
def baseEnd_1299469 : Nat := 1220397243013226438521

theorem tailTrace_1299469 : CollatzResearch.WordTrace tailWord_1299469 prefixEnd_1299469 1220397243013226438521 := by
  unfold tailWord_1299469
  simp only [CollatzResearch.WordTrace]
  refine ⟨47395528129253219481429461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31597018752835479654286307 47395528129253219481429461)
  ·
    refine ⟨1110832690529372331596003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 47395528129253219481429461 1110832690529372331596003)
    ·
      refine ⟨1666249035794058497394005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1110832690529372331596003 1666249035794058497394005)
      ·
        refine ⟨1220397243013226438521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1666249035794058497394005 1220397243013226438521)
        ·
          rfl

theorem cell21_1299469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 12].length) (baseStart_1299469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299469 prefixEnd_1299469 := by exact prefixLift 1299469
  have htrace : WordTrace (prefixWord ++ tailWord_1299469) baseStart_1299469 baseEnd_1299469 := by
    simpa [prefixWord, tailWord_1299469, baseEnd_1299469] using wordTrace_append hprefix tailTrace_1299469
  have hstable : (prefixWord ++ tailWord_1299469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299469).length < 2 ^ (prefixWord ++ tailWord_1299469).sum := by decide
  have hdescent : baseEnd_1299469 < baseStart_1299469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299517 : List Nat := [1, 4, 1, 3, 1, 3, 2, 3, 3]
def baseStart_1299517 : Nat := 118140960795 + 1299517 * 2 ^ 59
def prefixEnd_1299517 : Nat := 4983230072969 + 3 ^ 40 * 1299517 * 2
def baseEnd_1299517 : Nat := 296567484306176607760505

theorem tailTrace_1299517 : CollatzResearch.WordTrace tailWord_1299517 prefixEnd_1299517 296567484306176607760505 := by
  unfold tailWord_1299517
  simp only [CollatzResearch.WordTrace]
  refine ⟨47397278833079323679176805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31598185888719549119451203 47397278833079323679176805)
  ·
    refine ⟨8886989781202373189845651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47397278833079323679176805 8886989781202373189845651)
    ·
      refine ⟨13330484671803559784768477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8886989781202373189845651 13330484671803559784768477)
      ·
        refine ⟨4998931751926334919288179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13330484671803559784768477 4998931751926334919288179)
        ·
          refine ⟨7498397627889502378932269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4998931751926334919288179 7498397627889502378932269)
          ·
            refine ⟨2811899110458563392099601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7498397627889502378932269 2811899110458563392099601)
            ·
              refine ⟨2108924332843922544074701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2811899110458563392099601 2108924332843922544074701)
              ·
                refine ⟨790846624816470954028013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2108924332843922544074701 790846624816470954028013)
                ·
                  refine ⟨296567484306176607760505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 790846624816470954028013 296567484306176607760505)
                  ·
                    rfl

theorem cell21_1299517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_1299517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299517 prefixEnd_1299517 := by exact prefixLift 1299517
  have htrace : WordTrace (prefixWord ++ tailWord_1299517) baseStart_1299517 baseEnd_1299517 := by
    simpa [prefixWord, tailWord_1299517, baseEnd_1299517] using wordTrace_append hprefix tailTrace_1299517
  have hstable : (prefixWord ++ tailWord_1299517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299517).length < 2 ^ (prefixWord ++ tailWord_1299517).sum := by decide
  have hdescent : baseEnd_1299517 < baseStart_1299517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299559 : List Nat := [1, 1, 5, 1, 1, 3, 2, 2, 5]
def baseStart_1299559 : Nat := 118140960795 + 1299559 * 2 ^ 59
def prefixEnd_1299559 : Nat := 4983230072969 + 3 ^ 40 * 1299559 * 2
def baseEnd_1299559 : Nat := 296577069278393868060419

theorem tailTrace_1299559 : CollatzResearch.WordTrace tailWord_1299559 prefixEnd_1299559 296577069278393868060419 := by
  unfold tailWord_1299559
  simp only [CollatzResearch.WordTrace]
  refine ⟨47398810698927164852205731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31599207132618109901470487 47398810698927164852205731)
  ·
    refine ⟨71098216048390747278308597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47398810698927164852205731 71098216048390747278308597)
    ·
      refine ⟨6665457754536632557341431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71098216048390747278308597 6665457754536632557341431)
      ·
        refine ⟨9998186631804948836012147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6665457754536632557341431 9998186631804948836012147)
        ·
          refine ⟨14997279947707423254018221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9998186631804948836012147 14997279947707423254018221)
          ·
            refine ⟨5623979980390283720256833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14997279947707423254018221 5623979980390283720256833)
            ·
              refine ⟨4217984985292712790192625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5623979980390283720256833 4217984985292712790192625)
              ·
                refine ⟨3163488738969534592644469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4217984985292712790192625 3163488738969534592644469)
                ·
                  refine ⟨296577069278393868060419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3163488738969534592644469 296577069278393868060419)
                  ·
                    rfl

theorem cell21_1299559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 5].length) (baseStart_1299559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299559 prefixEnd_1299559 := by exact prefixLift 1299559
  have htrace : WordTrace (prefixWord ++ tailWord_1299559) baseStart_1299559 baseEnd_1299559 := by
    simpa [prefixWord, tailWord_1299559, baseEnd_1299559] using wordTrace_append hprefix tailTrace_1299559
  have hstable : (prefixWord ++ tailWord_1299559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299559).length < 2 ^ (prefixWord ++ tailWord_1299559).sum := by decide
  have hdescent : baseEnd_1299559 < baseStart_1299559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299562 : List Nat := [3, 1, 3, 2, 2, 3, 2, 5]
def baseStart_1299562 : Nat := 118140960795 + 1299562 * 2 ^ 59
def prefixEnd_1299562 : Nat := 4983230072969 + 3 ^ 40 * 1299562 * 2
def baseEnd_1299562 : Nat := 98859251306422176503471

theorem tailTrace_1299562 : CollatzResearch.WordTrace tailWord_1299562 prefixEnd_1299562 98859251306422176503471 := by
  unfold tailWord_1299562
  simp only [CollatzResearch.WordTrace]
  refine ⟨11849730029479074091141235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31599280078610864243043293 11849730029479074091141235)
  ·
    refine ⟨17774595044218611136711853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11849730029479074091141235 17774595044218611136711853)
    ·
      refine ⟨6665473141581979176266945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17774595044218611136711853 6665473141581979176266945)
      ·
        refine ⟨4999104856186484382200209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6665473141581979176266945 4999104856186484382200209)
        ·
          refine ⟨3749328642139863286650157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4999104856186484382200209 3749328642139863286650157)
          ·
            refine ⟨1405998240802448732493809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3749328642139863286650157 1405998240802448732493809)
            ·
              refine ⟨1054498680601836549370357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1405998240802448732493809 1054498680601836549370357)
              ·
                refine ⟨98859251306422176503471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1054498680601836549370357 98859251306422176503471)
                ·
                  rfl

theorem cell21_1299562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_1299562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299562 prefixEnd_1299562 := by exact prefixLift 1299562
  have htrace : WordTrace (prefixWord ++ tailWord_1299562) baseStart_1299562 baseEnd_1299562 := by
    simpa [prefixWord, tailWord_1299562, baseEnd_1299562] using wordTrace_append hprefix tailTrace_1299562
  have hstable : (prefixWord ++ tailWord_1299562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299562).length < 2 ^ (prefixWord ++ tailWord_1299562).sum := by decide
  have hdescent : baseEnd_1299562 < baseStart_1299562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299576 : List Nat := [2, 1, 2, 1, 1, 1, 7, 3, 3]
def baseStart_1299576 : Nat := 118140960795 + 1299576 * 2 ^ 59
def prefixEnd_1299576 : Nat := 4983230072969 + 3 ^ 40 * 1299576 * 2
def baseEnd_1299576 : Nat := 296580948910005616277051

theorem tailTrace_1299576 : CollatzResearch.WordTrace tailWord_1299576 prefixEnd_1299576 296580948910005616277051 := by
  unfold tailWord_1299576
  simp only [CollatzResearch.WordTrace]
  refine ⟨23699715369932788377787291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31599620493243717837049721 23699715369932788377787291)
  ·
    refine ⟨35549573054899182566680937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23699715369932788377787291 35549573054899182566680937)
    ·
      refine ⟨26662179791174386925010703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35549573054899182566680937 26662179791174386925010703)
      ·
        refine ⟨39993269686761580387516055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26662179791174386925010703 39993269686761580387516055)
        ·
          refine ⟨59989904530142370581274083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39993269686761580387516055 59989904530142370581274083)
          ·
            refine ⟨89984856795213555871911125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59989904530142370581274083 89984856795213555871911125)
            ·
              refine ⟨2109020081137817715747917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 89984856795213555871911125 2109020081137817715747917)
              ·
                refine ⟨790882530426681643405469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2109020081137817715747917 790882530426681643405469)
                ·
                  refine ⟨296580948910005616277051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 790882530426681643405469 296580948910005616277051)
                  ·
                    rfl

theorem cell21_1299576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 3].length) (baseStart_1299576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299576 prefixEnd_1299576 := by exact prefixLift 1299576
  have htrace : WordTrace (prefixWord ++ tailWord_1299576) baseStart_1299576 baseEnd_1299576 := by
    simpa [prefixWord, tailWord_1299576, baseEnd_1299576] using wordTrace_append hprefix tailTrace_1299576
  have hstable : (prefixWord ++ tailWord_1299576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299576).length < 2 ^ (prefixWord ++ tailWord_1299576).sum := by decide
  have hdescent : baseEnd_1299576 < baseStart_1299576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299593 : List Nat := [1, 2, 1, 1, 4, 4, 3, 2, 3]
def baseStart_1299593 : Nat := 118140960795 + 1299593 * 2 ^ 59
def prefixEnd_1299593 : Nat := 4983230072969 + 3 ^ 40 * 1299593 * 2
def baseEnd_1299593 : Nat := 296584828541617364493683

theorem tailTrace_1299593 : CollatzResearch.WordTrace tailWord_1299593 prefixEnd_1299593 296584828541617364493683 := by
  unfold tailWord_1299593
  simp only [CollatzResearch.WordTrace]
  refine ⟨47400050780803988658943433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31600033853869325772628955 47400050780803988658943433)
  ·
    refine ⟨35550038085602991494207575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47400050780803988658943433 35550038085602991494207575)
    ·
      refine ⟨53325057128404487241311363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35550038085602991494207575 53325057128404487241311363)
      ·
        refine ⟨79987585692606730861967045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53325057128404487241311363 79987585692606730861967045)
        ·
          refine ⟨14997672317363762036618821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79987585692606730861967045 14997672317363762036618821)
          ·
            refine ⟨2812063559505705381866029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14997672317363762036618821 2812063559505705381866029)
            ·
              refine ⟨1054523834814639518199761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2812063559505705381866029 1054523834814639518199761)
              ·
                refine ⟨790892876110979638649821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1054523834814639518199761 790892876110979638649821)
                ·
                  refine ⟨296584828541617364493683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 790892876110979638649821 296584828541617364493683)
                  ·
                    rfl

theorem cell21_1299593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 3].length) (baseStart_1299593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299593 prefixEnd_1299593 := by exact prefixLift 1299593
  have htrace : WordTrace (prefixWord ++ tailWord_1299593) baseStart_1299593 baseEnd_1299593 := by
    simpa [prefixWord, tailWord_1299593, baseEnd_1299593] using wordTrace_append hprefix tailTrace_1299593
  have hstable : (prefixWord ++ tailWord_1299593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299593).length < 2 ^ (prefixWord ++ tailWord_1299593).sum := by decide
  have hdescent : baseEnd_1299593 < baseStart_1299593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299607 : List Nat := [1, 1, 3, 3, 3, 1, 4, 1, 4]
def baseStart_1299607 : Nat := 118140960795 + 1299607 * 2 ^ 59
def prefixEnd_1299607 : Nat := 4983230072969 + 3 ^ 40 * 1299607 * 2
def baseEnd_1299607 : Nat := 296588023532356451260321

theorem tailTrace_1299607 : CollatzResearch.WordTrace tailWord_1299607 prefixEnd_1299607 296588023532356451260321 := by
  unfold tailWord_1299607
  simp only [CollatzResearch.WordTrace]
  refine ⟨47400561402753269049953075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31600374268502179366635383 47400561402753269049953075)
  ·
    refine ⟨71100842104129903574929613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47400561402753269049953075 71100842104129903574929613)
    ·
      refine ⟨26662815789048713840598605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71100842104129903574929613 26662815789048713840598605)
      ·
        refine ⟨9998555920893267690224477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26662815789048713840598605 9998555920893267690224477)
        ·
          refine ⟨3749458470334975383834179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9998555920893267690224477 3749458470334975383834179)
          ·
            refine ⟨5624187705502463075751269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3749458470334975383834179 5624187705502463075751269)
            ·
              refine ⟨1054535194781711826703363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5624187705502463075751269 1054535194781711826703363)
              ·
                refine ⟨1581802792172567740055045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054535194781711826703363 1581802792172567740055045)
                ·
                  refine ⟨296588023532356451260321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1581802792172567740055045 296588023532356451260321)
                  ·
                    rfl

theorem cell21_1299607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 4].length) (baseStart_1299607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299607 prefixEnd_1299607 := by exact prefixLift 1299607
  have htrace : WordTrace (prefixWord ++ tailWord_1299607) baseStart_1299607 baseEnd_1299607 := by
    simpa [prefixWord, tailWord_1299607, baseEnd_1299607] using wordTrace_append hprefix tailTrace_1299607
  have hstable : (prefixWord ++ tailWord_1299607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299607).length < 2 ^ (prefixWord ++ tailWord_1299607).sum := by decide
  have hdescent : baseEnd_1299607 < baseStart_1299607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299638 : List Nat := [5, 1, 3, 2, 1, 9]
def baseStart_1299638 : Nat := 118140960795 + 1299638 * 2 ^ 59
def prefixEnd_1299638 : Nat := 4983230072969 + 3 ^ 40 * 1299638 * 2
def baseEnd_1299638 : Nat := 10985003635359529120133

theorem tailTrace_1299638 : CollatzResearch.WordTrace tailWord_1299638 prefixEnd_1299638 10985003635359529120133 := by
  unfold tailWord_1299638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2962605754102560084020723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31601128043760640896221045 2962605754102560084020723)
  ·
    refine ⟨4443908631153840126031085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2962605754102560084020723 4443908631153840126031085)
    ·
      refine ⟨1666465736682690047261657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4443908631153840126031085 1666465736682690047261657)
      ·
        refine ⟨1249849302512017535446243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1666465736682690047261657 1249849302512017535446243)
        ·
          refine ⟨1874773953768026303169365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1249849302512017535446243 1874773953768026303169365)
          ·
            refine ⟨10985003635359529120133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1874773953768026303169365 10985003635359529120133)
            ·
              rfl

theorem cell21_1299638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 9].length) (baseStart_1299638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299638 prefixEnd_1299638 := by exact prefixLift 1299638
  have htrace : WordTrace (prefixWord ++ tailWord_1299638) baseStart_1299638 baseEnd_1299638 := by
    simpa [prefixWord, tailWord_1299638, baseEnd_1299638] using wordTrace_append hprefix tailTrace_1299638
  have hstable : (prefixWord ++ tailWord_1299638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299638).length < 2 ^ (prefixWord ++ tailWord_1299638).sum := by decide
  have hdescent : baseEnd_1299638 < baseStart_1299638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299663 : List Nat := [1, 1, 2, 1, 1, 3, 2, 10]
def baseStart_1299663 : Nat := 118140960795 + 1299663 * 2 ^ 59
def prefixEnd_1299663 : Nat := 4983230072969 + 3 ^ 40 * 1299663 * 2
def baseEnd_1299663 : Nat := 98866934498437599442291

theorem tailTrace_1299663 : CollatzResearch.WordTrace tailWord_1299663 prefixEnd_1299663 98866934498437599442291 := by
  unfold tailWord_1299663
  simp only [CollatzResearch.WordTrace]
  refine ⟨47402603890550390613991643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31601735927033593742661095 47402603890550390613991643)
  ·
    refine ⟨71103905835825585920987465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47402603890550390613991643 71103905835825585920987465)
    ·
      refine ⟨53327929376869189440740599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71103905835825585920987465 53327929376869189440740599)
      ·
        refine ⟨79991894065303784161110899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53327929376869189440740599 79991894065303784161110899)
        ·
          refine ⟨119987841097955676241666349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79991894065303784161110899 119987841097955676241666349)
          ·
            refine ⟨44995440411733378590624881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119987841097955676241666349 44995440411733378590624881)
            ·
              refine ⟨33746580308800033942968661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44995440411733378590624881 33746580308800033942968661)
              ·
                refine ⟨98866934498437599442291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33746580308800033942968661 98866934498437599442291)
                ·
                  rfl

theorem cell21_1299663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 10].length) (baseStart_1299663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299663 prefixEnd_1299663 := by exact prefixLift 1299663
  have htrace : WordTrace (prefixWord ++ tailWord_1299663) baseStart_1299663 baseEnd_1299663 := by
    simpa [prefixWord, tailWord_1299663, baseEnd_1299663] using wordTrace_append hprefix tailTrace_1299663
  have hstable : (prefixWord ++ tailWord_1299663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299663).length < 2 ^ (prefixWord ++ tailWord_1299663).sum := by decide
  have hdescent : baseEnd_1299663 < baseStart_1299663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299666 : List Nat := [3, 2, 2, 2, 1, 1, 1, 5, 4]
def baseStart_1299666 : Nat := 118140960795 + 1299666 * 2 ^ 59
def prefixEnd_1299666 : Nat := 4983230072969 + 3 ^ 40 * 1299666 * 2
def baseEnd_1299666 : Nat := 296601488136185459776867

theorem tailTrace_1299666 : CollatzResearch.WordTrace tailWord_1299666 prefixEnd_1299666 296601488136185459776867 := by
  unfold tailWord_1299666
  simp only [CollatzResearch.WordTrace]
  refine ⟨11850678327384880531587713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31601808873026348084233901 11850678327384880531587713)
  ·
    refine ⟨8888008745538660398690785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11850678327384880531587713 8888008745538660398690785)
    ·
      refine ⟨6666006559153995299018089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8888008745538660398690785 6666006559153995299018089)
      ·
        refine ⟨4999504919365496474263567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6666006559153995299018089 4999504919365496474263567)
        ·
          refine ⟨7499257379048244711395351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4999504919365496474263567 7499257379048244711395351)
          ·
            refine ⟨11248886068572367067093027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7499257379048244711395351 11248886068572367067093027)
            ·
              refine ⟨16873329102858550600639541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11248886068572367067093027 16873329102858550600639541)
              ·
                refine ⟨1581874603392989118809957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16873329102858550600639541 1581874603392989118809957)
                ·
                  refine ⟨296601488136185459776867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1581874603392989118809957 296601488136185459776867)
                  ·
                    rfl

theorem cell21_1299666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_1299666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299666 prefixEnd_1299666 := by exact prefixLift 1299666
  have htrace : WordTrace (prefixWord ++ tailWord_1299666) baseStart_1299666 baseEnd_1299666 := by
    simpa [prefixWord, tailWord_1299666, baseEnd_1299666] using wordTrace_append hprefix tailTrace_1299666
  have hstable : (prefixWord ++ tailWord_1299666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299666).length < 2 ^ (prefixWord ++ tailWord_1299666).sum := by decide
  have hdescent : baseEnd_1299666 < baseStart_1299666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299711 : List Nat := [1, 1, 2, 2, 1, 6, 2, 1, 5]
def baseStart_1299711 : Nat := 118140960795 + 1299711 * 2 ^ 59
def prefixEnd_1299711 : Nat := 4983230072969 + 3 ^ 40 * 1299711 * 2
def baseEnd_1299711 : Nat := 296611757749275381526775

theorem tailTrace_1299711 : CollatzResearch.WordTrace tailWord_1299711 prefixEnd_1299711 296611757749275381526775 := by
  unfold tailWord_1299711
  simp only [CollatzResearch.WordTrace]
  refine ⟨47404354594376494811738987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31602903062917663207825991 47404354594376494811738987)
  ·
    refine ⟨71106531891564742217608481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47404354594376494811738987 71106531891564742217608481)
    ·
      refine ⟨53329898918673556663206361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71106531891564742217608481 53329898918673556663206361)
      ·
        refine ⟨39997424189005167497404771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53329898918673556663206361 39997424189005167497404771)
        ·
          refine ⟨59996136283507751246107157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39997424189005167497404771 59996136283507751246107157)
          ·
            refine ⟨2812318888289425839661273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59996136283507751246107157 2812318888289425839661273)
            ·
              refine ⟨2109239166217069379745955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2812318888289425839661273 2109239166217069379745955)
              ·
                refine ⟨3163858749325604069618933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2109239166217069379745955 3163858749325604069618933)
                ·
                  refine ⟨296611757749275381526775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3163858749325604069618933 296611757749275381526775)
                  ·
                    rfl

theorem cell21_1299711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 5].length) (baseStart_1299711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299711 prefixEnd_1299711 := by exact prefixLift 1299711
  have htrace : WordTrace (prefixWord ++ tailWord_1299711) baseStart_1299711 baseEnd_1299711 := by
    simpa [prefixWord, tailWord_1299711, baseEnd_1299711] using wordTrace_append hprefix tailTrace_1299711
  have hstable : (prefixWord ++ tailWord_1299711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299711).length < 2 ^ (prefixWord ++ tailWord_1299711).sum := by decide
  have hdescent : baseEnd_1299711 < baseStart_1299711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299815 : List Nat := [1, 1, 5, 1, 13]
def baseStart_1299815 : Nat := 118140960795 + 1299815 * 2 ^ 59
def prefixEnd_1299815 : Nat := 4983230072969 + 3 ^ 40 * 1299815 * 2
def baseEnd_1299815 : Nat := 3662166567483880392509

theorem tailTrace_1299815 : CollatzResearch.WordTrace tailWord_1299815 prefixEnd_1299815 3662166567483880392509 := by
  unfold tailWord_1299815
  simp only [CollatzResearch.WordTrace]
  refine ⟨47408147785999720573524899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31605431857333147049016599 47408147785999720573524899)
  ·
    refine ⟨71112221678999580860287349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47408147785999720573524899 71112221678999580860287349)
    ·
      refine ⟨6666770782406210705651939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71112221678999580860287349 6666770782406210705651939)
      ·
        refine ⟨10000156173609316058477909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6666770782406210705651939 10000156173609316058477909)
        ·
          refine ⟨3662166567483880392509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 10000156173609316058477909 3662166567483880392509)
          ·
            rfl

theorem cell21_1299815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 13].length) (baseStart_1299815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299815 prefixEnd_1299815 := by exact prefixLift 1299815
  have htrace : WordTrace (prefixWord ++ tailWord_1299815) baseStart_1299815 baseEnd_1299815 := by
    simpa [prefixWord, tailWord_1299815, baseEnd_1299815] using wordTrace_append hprefix tailTrace_1299815
  have hstable : (prefixWord ++ tailWord_1299815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299815).length < 2 ^ (prefixWord ++ tailWord_1299815).sum := by decide
  have hdescent : baseEnd_1299815 < baseStart_1299815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299821 : List Nat := [1, 5, 1, 1, 1, 3, 4, 2, 3]
def baseStart_1299821 : Nat := 118140960795 + 1299821 * 2 ^ 59
def prefixEnd_1299821 : Nat := 4983230072969 + 3 ^ 40 * 1299821 * 2
def baseEnd_1299821 : Nat := 296636861247939634693217

theorem tailTrace_1299821 : CollatzResearch.WordTrace tailWord_1299821 prefixEnd_1299821 296636861247939634693217 := by
  unfold tailWord_1299821
  simp only [CollatzResearch.WordTrace]
  refine ⟨47408366623977983598243317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31605577749318655732162211 47408366623977983598243317)
  ·
    refine ⟨4444534370997935962335311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47408366623977983598243317 4444534370997935962335311)
    ·
      refine ⟨6666801556496903943502967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4444534370997935962335311 6666801556496903943502967)
      ·
        refine ⟨10000202334745355915254451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6666801556496903943502967 10000202334745355915254451)
        ·
          refine ⟨15000303502118033872881677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10000202334745355915254451 15000303502118033872881677)
          ·
            refine ⟨5625113813294262702330629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15000303502118033872881677 5625113813294262702330629)
            ·
              refine ⟨1054708839992674256686993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5625113813294262702330629 1054708839992674256686993)
              ·
                refine ⟨791031629994505692515245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1054708839992674256686993 791031629994505692515245)
                ·
                  refine ⟨296636861247939634693217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 791031629994505692515245 296636861247939634693217)
                  ·
                    rfl

theorem cell21_1299821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_1299821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299821 prefixEnd_1299821 := by exact prefixLift 1299821
  have htrace : WordTrace (prefixWord ++ tailWord_1299821) baseStart_1299821 baseEnd_1299821 := by
    simpa [prefixWord, tailWord_1299821, baseEnd_1299821] using wordTrace_append hprefix tailTrace_1299821
  have hstable : (prefixWord ++ tailWord_1299821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299821).length < 2 ^ (prefixWord ++ tailWord_1299821).sum := by decide
  have hdescent : baseEnd_1299821 < baseStart_1299821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299849 : List Nat := [1, 2, 1, 1, 7, 1, 3, 5]
def baseStart_1299849 : Nat := 118140960795 + 1299849 * 2 ^ 59
def prefixEnd_1299849 : Nat := 4983230072969 + 3 ^ 40 * 1299849 * 2
def baseEnd_1299849 : Nat := 98881083743139269408831

theorem tailTrace_1299849 : CollatzResearch.WordTrace tailWord_1299849 prefixEnd_1299849 98881083743139269408831 := by
  unfold tailWord_1299849
  simp only [CollatzResearch.WordTrace]
  refine ⟨47409387867876544380262601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31606258578584362920175067 47409387867876544380262601)
  ·
    refine ⟨35557040900907408285196951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47409387867876544380262601 35557040900907408285196951)
    ·
      refine ⟨53335561351361112427795427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35557040900907408285196951 53335561351361112427795427)
      ·
        refine ⟨80003342027041668641693141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53335561351361112427795427 80003342027041668641693141)
        ·
          refine ⟨1875078328758789108789683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 80003342027041668641693141 1875078328758789108789683)
          ·
            refine ⟨2812617493138183663184525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1875078328758789108789683 2812617493138183663184525)
            ·
              refine ⟨1054731559926818873694197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2812617493138183663184525 1054731559926818873694197)
              ·
                refine ⟨98881083743139269408831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1054731559926818873694197 98881083743139269408831)
                ·
                  rfl

theorem cell21_1299849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 5].length) (baseStart_1299849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299849 prefixEnd_1299849 := by exact prefixLift 1299849
  have htrace : WordTrace (prefixWord ++ tailWord_1299849) baseStart_1299849 baseEnd_1299849 := by
    simpa [prefixWord, tailWord_1299849, baseEnd_1299849] using wordTrace_append hprefix tailTrace_1299849
  have hstable : (prefixWord ++ tailWord_1299849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299849).length < 2 ^ (prefixWord ++ tailWord_1299849).sum := by decide
  have hdescent : baseEnd_1299849 < baseStart_1299849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299877 : List Nat := [1, 3, 1, 2, 1, 1, 2, 6, 4]
def baseStart_1299877 : Nat := 118140960795 + 1299877 * 2 ^ 59
def prefixEnd_1299877 : Nat := 4983230072969 + 3 ^ 40 * 1299877 * 2
def baseEnd_1299877 : Nat := 296649641210895981759769

theorem tailTrace_1299877 : CollatzResearch.WordTrace tailWord_1299877 prefixEnd_1299877 296649641210895981759769 := by
  unfold tailWord_1299877
  simp only [CollatzResearch.WordTrace]
  refine ⟨47410409111775105162281885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31606939407850070108187923 47410409111775105162281885)
  ·
    refine ⟨17778903416915664435855707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47410409111775105162281885 17778903416915664435855707)
    ·
      refine ⟨26668355125373496653783561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17778903416915664435855707 26668355125373496653783561)
      ·
        refine ⟨20001266344030122490337671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26668355125373496653783561 20001266344030122490337671)
        ·
          refine ⟨30001899516045183735506507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20001266344030122490337671 30001899516045183735506507)
          ·
            refine ⟨45002849274067775603259761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30001899516045183735506507 45002849274067775603259761)
            ·
              refine ⟨33752136955550831702444821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45002849274067775603259761 33752136955550831702444821)
              ·
                refine ⟨1582131419791445236052101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33752136955550831702444821 1582131419791445236052101)
                ·
                  refine ⟨296649641210895981759769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1582131419791445236052101 296649641210895981759769)
                  ·
                    rfl

theorem cell21_1299877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_1299877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299877 prefixEnd_1299877 := by exact prefixLift 1299877
  have htrace : WordTrace (prefixWord ++ tailWord_1299877) baseStart_1299877 baseEnd_1299877 := by
    simpa [prefixWord, tailWord_1299877, baseEnd_1299877] using wordTrace_append hprefix tailTrace_1299877
  have hstable : (prefixWord ++ tailWord_1299877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299877).length < 2 ^ (prefixWord ++ tailWord_1299877).sum := by decide
  have hdescent : baseEnd_1299877 < baseStart_1299877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299939 : List Nat := [1, 1, 1, 6, 2, 1, 3, 1, 5]
def baseStart_1299939 : Nat := 118140960795 + 1299939 * 2 ^ 59
def prefixEnd_1299939 : Nat := 4983230072969 + 3 ^ 40 * 1299939 * 2
def baseEnd_1299939 : Nat := 296663790455597651726309

theorem tailTrace_1299939 : CollatzResearch.WordTrace tailWord_1299939 prefixEnd_1299939 296663790455597651726309 := by
  unfold tailWord_1299939
  simp only [CollatzResearch.WordTrace]
  refine ⟨47412670437550489751038871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31608446958366993167359247 47412670437550489751038871)
  ·
    refine ⟨71119005656325734626558307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47412670437550489751038871 71119005656325734626558307)
    ·
      refine ⟨106678508484488601939837461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71119005656325734626558307 106678508484488601939837461)
      ·
        refine ⟨5000555085210403215929881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 106678508484488601939837461 5000555085210403215929881)
        ·
          refine ⟨3750416313907802411947411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5000555085210403215929881 3750416313907802411947411)
          ·
            refine ⟨5625624470861703617921117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3750416313907802411947411 5625624470861703617921117)
            ·
              refine ⟨2109609176573138856720419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5625624470861703617921117 2109609176573138856720419)
              ·
                refine ⟨3164413764859708285080629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2109609176573138856720419 3164413764859708285080629)
                ·
                  refine ⟨296663790455597651726309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3164413764859708285080629 296663790455597651726309)
                  ·
                    rfl

theorem cell21_1299939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 5].length) (baseStart_1299939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1299939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1299939 prefixEnd_1299939 := by exact prefixLift 1299939
  have htrace : WordTrace (prefixWord ++ tailWord_1299939) baseStart_1299939 baseEnd_1299939 := by
    simpa [prefixWord, tailWord_1299939, baseEnd_1299939] using wordTrace_append hprefix tailTrace_1299939
  have hstable : (prefixWord ++ tailWord_1299939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299939).length < 2 ^ (prefixWord ++ tailWord_1299939).sum := by decide
  have hdescent : baseEnd_1299939 < baseStart_1299939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300012 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 10]
def baseStart_1300012 : Nat := 118140960795 + 1300012 * 2 ^ 59
def prefixEnd_1300012 : Nat := 4983230072969 + 3 ^ 40 * 1300012 * 2
def baseEnd_1300012 : Nat := 296680450050165747009493

theorem tailTrace_1300012 : CollatzResearch.WordTrace tailWord_1300012 prefixEnd_1300012 296680450050165747009493 := by
  unfold tailWord_1300012
  simp only [CollatzResearch.WordTrace]
  refine ⟨23707666483143011609223145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31610221977524015478964193 23707666483143011609223145)
  ·
    refine ⟨17780749862357258706917359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23707666483143011609223145 17780749862357258706917359)
    ·
      refine ⟨26671124793535888060376039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17780749862357258706917359 26671124793535888060376039)
      ·
        refine ⟨40006687190303832090564059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26671124793535888060376039 40006687190303832090564059)
        ·
          refine ⟨60010030785455748135846089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40006687190303832090564059 60010030785455748135846089)
          ·
            refine ⟨45007523089091811101884567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60010030785455748135846089 45007523089091811101884567)
            ·
              refine ⟨67511284633637716652826851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45007523089091811101884567 67511284633637716652826851)
              ·
                refine ⟨101266926950456574979240277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67511284633637716652826851 101266926950456574979240277)
                ·
                  refine ⟨296680450050165747009493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 101266926950456574979240277 296680450050165747009493)
                  ·
                    rfl

theorem cell21_1300012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_1300012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1300012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1300012 prefixEnd_1300012 := by exact prefixLift 1300012
  have htrace : WordTrace (prefixWord ++ tailWord_1300012) baseStart_1300012 baseEnd_1300012 := by
    simpa [prefixWord, tailWord_1300012, baseEnd_1300012] using wordTrace_append hprefix tailTrace_1300012
  have hstable : (prefixWord ++ tailWord_1300012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300012).length < 2 ^ (prefixWord ++ tailWord_1300012).sum := by decide
  have hdescent : baseEnd_1300012 < baseStart_1300012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300108 : List Nat := [2, 2, 1, 2, 1, 1, 7, 2, 3]
def baseStart_1300108 : Nat := 118140960795 + 1300108 * 2 ^ 59
def prefixEnd_1300108 : Nat := 4983230072969 + 3 ^ 40 * 1300108 * 2
def baseEnd_1300108 : Nat := 296702358558090913409297

theorem tailTrace_1300108 : CollatzResearch.WordTrace tailWord_1300108 prefixEnd_1300108 296702358558090913409297 := by
  unfold tailWord_1300108
  simp only [CollatzResearch.WordTrace]
  refine ⟨23709417186969115806970489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31612556249292154409293985 23709417186969115806970489)
  ·
    refine ⟨17782062890226836855227867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23709417186969115806970489 17782062890226836855227867)
    ·
      refine ⟨26673094335340255282841801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17782062890226836855227867 26673094335340255282841801)
      ·
        refine ⟨20004820751505191462131351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26673094335340255282841801 20004820751505191462131351)
        ·
          refine ⟨30007231127257787193197027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20004820751505191462131351 30007231127257787193197027)
          ·
            refine ⟨45010846690886680789795541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30007231127257787193197027 45010846690886680789795541)
            ·
              refine ⟨1054941719317656581010833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 45010846690886680789795541 1054941719317656581010833)
              ·
                refine ⟨791206289488242435758125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1054941719317656581010833 791206289488242435758125)
                ·
                  refine ⟨296702358558090913409297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 791206289488242435758125 296702358558090913409297)
                  ·
                    rfl

theorem cell21_1300108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 3].length) (baseStart_1300108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1300108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1300108 prefixEnd_1300108 := by exact prefixLift 1300108
  have htrace : WordTrace (prefixWord ++ tailWord_1300108) baseStart_1300108 baseEnd_1300108 := by
    simpa [prefixWord, tailWord_1300108, baseEnd_1300108] using wordTrace_append hprefix tailTrace_1300108
  have hstable : (prefixWord ++ tailWord_1300108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300108).length < 2 ^ (prefixWord ++ tailWord_1300108).sum := by decide
  have hdescent : baseEnd_1300108 < baseStart_1300108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300119 : List Nat := [1, 1, 3, 3, 2, 2, 1, 8]
def baseStart_1300119 : Nat := 118140960795 + 1300119 * 2 ^ 59
def prefixEnd_1300119 : Nat := 4983230072969 + 3 ^ 40 * 1300119 * 2
def baseEnd_1300119 : Nat := 98901622969319112908647

theorem tailTrace_1300119 : CollatzResearch.WordTrace tailWord_1300119 prefixEnd_1300119 98901622969319112908647 := by
  unfold tailWord_1300119
  simp only [CollatzResearch.WordTrace]
  refine ⟨47419235576898380492591411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31612823717932253661727607 47419235576898380492591411)
  ·
    refine ⟨71128853365347570738887117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47419235576898380492591411 71128853365347570738887117)
    ·
      refine ⟨26673320012005339027082669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71128853365347570738887117 26673320012005339027082669)
      ·
        refine ⟨10002495004502002135156001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26673320012005339027082669 10002495004502002135156001)
        ·
          refine ⟨7501871253376501601367001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10002495004502002135156001 7501871253376501601367001)
          ·
            refine ⟨5626403440032376201025251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7501871253376501601367001 5626403440032376201025251)
            ·
              refine ⟨8439605160048564301537877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5626403440032376201025251 8439605160048564301537877)
              ·
                refine ⟨98901622969319112908647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8439605160048564301537877 98901622969319112908647)
                ·
                  rfl

theorem cell21_1300119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 8].length) (baseStart_1300119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1300119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1300119 prefixEnd_1300119 := by exact prefixLift 1300119
  have htrace : WordTrace (prefixWord ++ tailWord_1300119) baseStart_1300119 baseEnd_1300119 := by
    simpa [prefixWord, tailWord_1300119, baseEnd_1300119] using wordTrace_append hprefix tailTrace_1300119
  have hstable : (prefixWord ++ tailWord_1300119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300119).length < 2 ^ (prefixWord ++ tailWord_1300119).sum := by decide
  have hdescent : baseEnd_1300119 < baseStart_1300119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300167 : List Nat := [1, 1, 4, 1, 1, 1, 5, 4, 3]
def baseStart_1300167 : Nat := 118140960795 + 1300167 * 2 ^ 59
def prefixEnd_1300167 : Nat := 4983230072969 + 3 ^ 40 * 1300167 * 2
def baseEnd_1300167 : Nat := 296715823161919921925843

theorem tailTrace_1300167 : CollatzResearch.WordTrace tailWord_1300167 prefixEnd_1300167 296715823161919921925843 := by
  unfold tailWord_1300167
  simp only [CollatzResearch.WordTrace]
  refine ⟨47420986280724484690338755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31613990853816323126892503 47420986280724484690338755)
  ·
    refine ⟨71131479421086727035508133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47420986280724484690338755 71131479421086727035508133)
    ·
      refine ⟨13337152391453761319157775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71131479421086727035508133 13337152391453761319157775)
      ·
        refine ⟨20005728587180641978736663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13337152391453761319157775 20005728587180641978736663)
        ·
          refine ⟨30008592880770962968104995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20005728587180641978736663 30008592880770962968104995)
          ·
            refine ⟨45012889321156444452157493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30008592880770962968104995 45012889321156444452157493)
            ·
              refine ⟨4219958373858416667389765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45012889321156444452157493 4219958373858416667389765)
              ·
                refine ⟨791242195098453125135581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4219958373858416667389765 791242195098453125135581)
                ·
                  refine ⟨296715823161919921925843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 791242195098453125135581 296715823161919921925843)
                  ·
                    rfl

theorem cell21_1300167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 3].length) (baseStart_1300167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1300167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1300167 prefixEnd_1300167 := by exact prefixLift 1300167
  have htrace : WordTrace (prefixWord ++ tailWord_1300167) baseStart_1300167 baseEnd_1300167 := by
    simpa [prefixWord, tailWord_1300167, baseEnd_1300167] using wordTrace_append hprefix tailTrace_1300167
  have hstable : (prefixWord ++ tailWord_1300167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300167).length < 2 ^ (prefixWord ++ tailWord_1300167).sum := by decide
  have hdescent : baseEnd_1300167 < baseStart_1300167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
