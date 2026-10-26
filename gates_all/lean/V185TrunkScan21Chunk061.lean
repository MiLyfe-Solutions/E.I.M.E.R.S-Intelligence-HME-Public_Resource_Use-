import V185TrunkScan21Chunk060

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_739239 : List Nat := [1, 1, 6, 1, 2, 1, 3, 2, 4]
def baseStart_739239 : Nat := 118140960795 + 739239 * 2 ^ 59
def prefixEnd_739239 : Nat := 4983230072969 + 3 ^ 40 * 739239 * 2
def baseEnd_739239 : Nat := 168704411355172647872359

theorem tailTrace_739239 : CollatzResearch.WordTrace tailWord_739239 prefixEnd_739239 168704411355172647872359 := by
  unfold tailWord_739239
  simp only [CollatzResearch.WordTrace]
  refine ⟨26962261368870829814876771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17974840912580553209917847 26962261368870829814876771)
  ·
    refine ⟨40443392053306244722315157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26962261368870829814876771 40443392053306244722315157)
    ·
      refine ⟨1895784002498730221358523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40443392053306244722315157 1895784002498730221358523)
      ·
        refine ⟨2843676003748095332037785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1895784002498730221358523 2843676003748095332037785)
        ·
          refine ⟨2132757002811071499028339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2843676003748095332037785 2132757002811071499028339)
          ·
            refine ⟨3199135504216607248542509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2132757002811071499028339 3199135504216607248542509)
            ·
              refine ⟨1199675814081227718203441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3199135504216607248542509 1199675814081227718203441)
              ·
                refine ⟨899756860560920788652581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1199675814081227718203441 899756860560920788652581)
                ·
                  refine ⟨168704411355172647872359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 899756860560920788652581 168704411355172647872359)
                  ·
                    rfl

theorem cell21_739239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 4].length) (baseStart_739239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739239 prefixEnd_739239 := by exact prefixLift 739239
  have htrace : WordTrace (prefixWord ++ tailWord_739239) baseStart_739239 baseEnd_739239 := by
    simpa [prefixWord, tailWord_739239, baseEnd_739239] using wordTrace_append hprefix tailTrace_739239
  have hstable : (prefixWord ++ tailWord_739239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739239).length < 2 ^ (prefixWord ++ tailWord_739239).sum := by decide
  have hdescent : baseEnd_739239 < baseStart_739239 := by decide
  rcases family_descends (prefixWord ++ tailWord_739239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739371 : List Nat := [1, 1, 1, 1, 2, 1, 4, 10]
def baseStart_739371 : Nat := 118140960795 + 739371 * 2 ^ 59
def prefixEnd_739371 : Nat := 4983230072969 + 3 ^ 40 * 739371 * 2
def baseEnd_739371 : Nat := 56244845184523250557363

theorem tailTrace_739371 : CollatzResearch.WordTrace tailWord_739371 prefixEnd_739371 56244845184523250557363 := by
  unfold tailWord_739371
  simp only [CollatzResearch.WordTrace]
  refine ⟨26967075804392616358681967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17978050536261744239121311 26967075804392616358681967)
  ·
    refine ⟨40450613706588924538022951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26967075804392616358681967 40450613706588924538022951)
    ·
      refine ⟨60675920559883386807034427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40450613706588924538022951 60675920559883386807034427)
      ·
        refine ⟨91013880839825080210551641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60675920559883386807034427 91013880839825080210551641)
        ·
          refine ⟨68260410629868810157913731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91013880839825080210551641 68260410629868810157913731)
          ·
            refine ⟨102390615944803215236870597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68260410629868810157913731 102390615944803215236870597)
            ·
              refine ⟨19198240489650602856913237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102390615944803215236870597 19198240489650602856913237)
              ·
                refine ⟨56244845184523250557363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19198240489650602856913237 56244845184523250557363)
                ·
                  rfl

theorem cell21_739371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 10].length) (baseStart_739371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739371 prefixEnd_739371 := by exact prefixLift 739371
  have htrace : WordTrace (prefixWord ++ tailWord_739371) baseStart_739371 baseEnd_739371 := by
    simpa [prefixWord, tailWord_739371, baseEnd_739371] using wordTrace_append hprefix tailTrace_739371
  have hstable : (prefixWord ++ tailWord_739371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739371).length < 2 ^ (prefixWord ++ tailWord_739371).sum := by decide
  have hdescent : baseEnd_739371 < baseStart_739371 := by decide
  rcases family_descends (prefixWord ++ tailWord_739371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739402 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 9]
def baseStart_739402 : Nat := 118140960795 + 739402 * 2 ^ 59
def prefixEnd_739402 : Nat := 4983230072969 + 3 ^ 40 * 739402 * 2
def baseEnd_739402 : Nat := 168741610175920586655359

theorem tailTrace_739402 : CollatzResearch.WordTrace tailWord_739402 prefixEnd_739402 168741610175920586655359 := by
  unfold tailWord_739402
  simp only [CollatzResearch.WordTrace]
  refine ⟨6742051616820077163265115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17978804311520205768706973 6742051616820077163265115)
  ·
    refine ⟨10113077425230115744897673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6742051616820077163265115 10113077425230115744897673)
    ·
      refine ⟨7584808068922586808673255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10113077425230115744897673 7584808068922586808673255)
      ·
        refine ⟨11377212103383880213009883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7584808068922586808673255 11377212103383880213009883)
        ·
          refine ⟨17065818155075820319514825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11377212103383880213009883 17065818155075820319514825)
          ·
            refine ⟨12799363616306865239636119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17065818155075820319514825 12799363616306865239636119)
            ·
              refine ⟨19199045424460297859454179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12799363616306865239636119 19199045424460297859454179)
              ·
                refine ⟨28798568136690446789181269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19199045424460297859454179 28798568136690446789181269)
                ·
                  refine ⟨168741610175920586655359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28798568136690446789181269 168741610175920586655359)
                  ·
                    rfl

theorem cell21_739402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_739402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739402 prefixEnd_739402 := by exact prefixLift 739402
  have htrace : WordTrace (prefixWord ++ tailWord_739402) baseStart_739402 baseEnd_739402 := by
    simpa [prefixWord, tailWord_739402, baseEnd_739402] using wordTrace_append hprefix tailTrace_739402
  have hstable : (prefixWord ++ tailWord_739402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739402).length < 2 ^ (prefixWord ++ tailWord_739402).sum := by decide
  have hdescent : baseEnd_739402 < baseStart_739402 := by decide
  rcases family_descends (prefixWord ++ tailWord_739402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739453 : List Nat := [1, 4, 1, 1, 3, 4, 1, 3, 3]
def baseStart_739453 : Nat := 118140960795 + 739453 * 2 ^ 59
def prefixEnd_739453 : Nat := 4983230072969 + 3 ^ 40 * 739453 * 2
def baseEnd_739453 : Nat := 168753249070755831305255

theorem tailTrace_739453 : CollatzResearch.WordTrace tailWord_739453 prefixEnd_739453 168753249070755831305255 := by
  unfold tailWord_739453
  simp only [CollatzResearch.WordTrace]
  refine ⟨26970066590095544363167013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17980044393397029575444675 26970066590095544363167013)
  ·
    refine ⟨5056887485642914568093815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26970066590095544363167013 5056887485642914568093815)
    ·
      refine ⟨7585331228464371852140723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5056887485642914568093815 7585331228464371852140723)
      ·
        refine ⟨11377996842696557778211085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7585331228464371852140723 11377996842696557778211085)
        ·
          refine ⟨4266748816011209166829157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11377996842696557778211085 4266748816011209166829157)
          ·
            refine ⟨800015403002101718780467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4266748816011209166829157 800015403002101718780467)
            ·
              refine ⟨1200023104503152578170701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 800015403002101718780467 1200023104503152578170701)
              ·
                refine ⟨450008664188682216814013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1200023104503152578170701 450008664188682216814013)
                ·
                  refine ⟨168753249070755831305255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 450008664188682216814013 168753249070755831305255)
                  ·
                    rfl

theorem cell21_739453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_739453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739453 prefixEnd_739453 := by exact prefixLift 739453
  have htrace : WordTrace (prefixWord ++ tailWord_739453) baseStart_739453 baseEnd_739453 := by
    simpa [prefixWord, tailWord_739453, baseEnd_739453] using wordTrace_append hprefix tailTrace_739453
  have hstable : (prefixWord ++ tailWord_739453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739453).length < 2 ^ (prefixWord ++ tailWord_739453).sum := by decide
  have hdescent : baseEnd_739453 < baseStart_739453 := by decide
  rcases family_descends (prefixWord ++ tailWord_739453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739464 : List Nat := [2, 1, 3, 4, 1, 1, 9]
def baseStart_739464 : Nat := 118140960795 + 739464 * 2 ^ 59
def prefixEnd_739464 : Nat := 4983230072969 + 3 ^ 40 * 739464 * 2
def baseEnd_739464 : Nat := 18750639935624695180211

theorem tailTrace_739464 : CollatzResearch.WordTrace tailWord_739464 prefixEnd_739464 18750639935624695180211 := by
  unfold tailWord_739464
  simp only [CollatzResearch.WordTrace]
  refine ⟨13485233896527846620908723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17980311862037128827878297 13485233896527846620908723)
  ·
    refine ⟨20227850844791769931363085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13485233896527846620908723 20227850844791769931363085)
    ·
      refine ⟨7585444066796913724261157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20227850844791769931363085 7585444066796913724261157)
      ·
        refine ⟨1422270762524421323298967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7585444066796913724261157 1422270762524421323298967)
        ·
          refine ⟨2133406143786631984948451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1422270762524421323298967 2133406143786631984948451)
          ·
            refine ⟨3200109215679947977422677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133406143786631984948451 3200109215679947977422677)
            ·
              refine ⟨18750639935624695180211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3200109215679947977422677 18750639935624695180211)
              ·
                rfl

theorem cell21_739464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 9].length) (baseStart_739464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739464 prefixEnd_739464 := by exact prefixLift 739464
  have htrace : WordTrace (prefixWord ++ tailWord_739464) baseStart_739464 baseEnd_739464 := by
    simpa [prefixWord, tailWord_739464, baseEnd_739464] using wordTrace_append hprefix tailTrace_739464
  have hstable : (prefixWord ++ tailWord_739464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739464).length < 2 ^ (prefixWord ++ tailWord_739464).sum := by decide
  have hdescent : baseEnd_739464 < baseStart_739464 := by decide
  rcases family_descends (prefixWord ++ tailWord_739464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739470 : List Nat := [4, 1, 1, 3, 3, 1, 3, 2, 3]
def baseStart_739470 : Nat := 118140960795 + 739470 * 2 ^ 59
def prefixEnd_739470 : Nat := 4983230072969 + 3 ^ 40 * 739470 * 2
def baseEnd_739470 : Nat := 168757128702367579521887

theorem tailTrace_739470 : CollatzResearch.WordTrace tailWord_739470 prefixEnd_739470 168757128702367579521887 := by
  unfold tailWord_739470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3371335828879244533316983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17980457754022637511023909 3371335828879244533316983)
  ·
    refine ⟨5057003743318866799975475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3371335828879244533316983 5057003743318866799975475)
    ·
      refine ⟨7585505614978300199963213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5057003743318866799975475 7585505614978300199963213)
      ·
        refine ⟨2844564605616862574986205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7585505614978300199963213 2844564605616862574986205)
        ·
          refine ⟨1066711727106323465619827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2844564605616862574986205 1066711727106323465619827)
          ·
            refine ⟨1600067590659485198429741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066711727106323465619827 1600067590659485198429741)
            ·
              refine ⟨600025346497306949411153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1600067590659485198429741 600025346497306949411153)
              ·
                refine ⟨450019009872980212058365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 600025346497306949411153 450019009872980212058365)
                ·
                  refine ⟨168757128702367579521887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 450019009872980212058365 168757128702367579521887)
                  ·
                    rfl

theorem cell21_739470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_739470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739470 prefixEnd_739470 := by exact prefixLift 739470
  have htrace : WordTrace (prefixWord ++ tailWord_739470) baseStart_739470 baseEnd_739470 := by
    simpa [prefixWord, tailWord_739470, baseEnd_739470] using wordTrace_append hprefix tailTrace_739470
  have hstable : (prefixWord ++ tailWord_739470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739470).length < 2 ^ (prefixWord ++ tailWord_739470).sum := by decide
  have hdescent : baseEnd_739470 < baseStart_739470 := by decide
  rcases family_descends (prefixWord ++ tailWord_739470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739557 : List Nat := [1, 3, 1, 4, 2, 2, 3, 5]
def baseStart_739557 : Nat := 118140960795 + 739557 * 2 ^ 59
def prefixEnd_739557 : Nat := 4983230072969 + 3 ^ 40 * 739557 * 2
def baseEnd_739557 : Nat := 56258994429224920523903

theorem tailTrace_739557 : CollatzResearch.WordTrace tailWord_739557 prefixEnd_739557 56258994429224920523903 := by
  unfold tailWord_739557
  simp only [CollatzResearch.WordTrace]
  refine ⟨26973859781718770124952925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17982573187812513416635283 26973859781718770124952925)
  ·
    refine ⟨10115197418144538796857347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26973859781718770124952925 10115197418144538796857347)
    ·
      refine ⟨15172796127216808195286021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10115197418144538796857347 15172796127216808195286021)
      ·
        refine ⟨2844899273853151536616129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15172796127216808195286021 2844899273853151536616129)
        ·
          refine ⟨2133674455389863652462097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2844899273853151536616129 2133674455389863652462097)
          ·
            refine ⟨1600255841542397739346573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2133674455389863652462097 1600255841542397739346573)
            ·
              refine ⟨600095940578399152254965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1600255841542397739346573 600095940578399152254965)
              ·
                refine ⟨56258994429224920523903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 600095940578399152254965 56258994429224920523903)
                ·
                  rfl

theorem cell21_739557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 5].length) (baseStart_739557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739557 prefixEnd_739557 := by exact prefixLift 739557
  have htrace : WordTrace (prefixWord ++ tailWord_739557) baseStart_739557 baseEnd_739557 := by
    simpa [prefixWord, tailWord_739557, baseEnd_739557] using wordTrace_append hprefix tailTrace_739557
  have hstable : (prefixWord ++ tailWord_739557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739557).length < 2 ^ (prefixWord ++ tailWord_739557).sum := by decide
  have hdescent : baseEnd_739557 < baseStart_739557 := by decide
  rcases family_descends (prefixWord ++ tailWord_739557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739585 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 6]
def baseStart_739585 : Nat := 118140960795 + 739585 * 2 ^ 59
def prefixEnd_739585 : Nat := 4983230072969 + 3 ^ 40 * 739585 * 2
def baseEnd_739585 : Nat := 168783373269152935104985

theorem tailTrace_739585 : CollatzResearch.WordTrace tailWord_739585 prefixEnd_739585 168783373269152935104985 := by
  unfold tailWord_739585
  simp only [CollatzResearch.WordTrace]
  refine ⟨26974881025617330906972209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17983254017078220604648139 26974881025617330906972209)
  ·
    refine ⟨20231160769212998180229157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26974881025617330906972209 20231160769212998180229157)
    ·
      refine ⟨3793342644227437158792967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20231160769212998180229157 3793342644227437158792967)
      ·
        refine ⟨5690013966341155738189451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3793342644227437158792967 5690013966341155738189451)
        ·
          refine ⟨8535020949511733607284177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5690013966341155738189451 8535020949511733607284177)
          ·
            refine ⟨6401265712133800205463133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8535020949511733607284177 6401265712133800205463133)
            ·
              refine ⟨2400474642050175077048675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6401265712133800205463133 2400474642050175077048675)
              ·
                refine ⟨3600711963075262615573013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2400474642050175077048675 3600711963075262615573013)
                ·
                  refine ⟨168783373269152935104985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3600711963075262615573013 168783373269152935104985)
                  ·
                    rfl

theorem cell21_739585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_739585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739585 prefixEnd_739585 := by exact prefixLift 739585
  have htrace : WordTrace (prefixWord ++ tailWord_739585) baseStart_739585 baseEnd_739585 := by
    simpa [prefixWord, tailWord_739585, baseEnd_739585] using wordTrace_append hprefix tailTrace_739585
  have hstable : (prefixWord ++ tailWord_739585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739585).length < 2 ^ (prefixWord ++ tailWord_739585).sum := by decide
  have hdescent : baseEnd_739585 < baseStart_739585 := by decide
  rcases family_descends (prefixWord ++ tailWord_739585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739588 : List Nat := [2, 3, 2, 2, 3, 1, 2, 1, 5]
def baseStart_739588 : Nat := 118140960795 + 739588 * 2 ^ 59
def prefixEnd_739588 : Nat := 4983230072969 + 3 ^ 40 * 739588 * 2
def baseEnd_739588 : Nat := 168784057910025596554979

theorem tailTrace_739588 : CollatzResearch.WordTrace tailWord_739588 prefixEnd_739588 168784057910025596554979 := by
  unfold tailWord_739588
  simp only [CollatzResearch.WordTrace]
  refine ⟨13487495222303231209665709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17983326963070974946220945 13487495222303231209665709)
  ·
    refine ⟨5057810708363711703624641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13487495222303231209665709 5057810708363711703624641)
    ·
      refine ⟨3793358031272783777718481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5057810708363711703624641 3793358031272783777718481)
      ·
        refine ⟨2845018523454587833288861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3793358031272783777718481 2845018523454587833288861)
        ·
          refine ⟨1066881946295470437483323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2845018523454587833288861 1066881946295470437483323)
          ·
            refine ⟨1600322919443205656224985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066881946295470437483323 1600322919443205656224985)
            ·
              refine ⟨1200242189582404242168739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1600322919443205656224985 1200242189582404242168739)
              ·
                refine ⟨1800363284373606363253109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1200242189582404242168739 1800363284373606363253109)
                ·
                  refine ⟨168784057910025596554979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1800363284373606363253109 168784057910025596554979)
                  ·
                    rfl

theorem cell21_739588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_739588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739588 prefixEnd_739588 := by exact prefixLift 739588
  have htrace : WordTrace (prefixWord ++ tailWord_739588) baseStart_739588 baseEnd_739588 := by
    simpa [prefixWord, tailWord_739588, baseEnd_739588] using wordTrace_append hprefix tailTrace_739588
  have hstable : (prefixWord ++ tailWord_739588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739588).length < 2 ^ (prefixWord ++ tailWord_739588).sum := by decide
  have hdescent : baseEnd_739588 < baseStart_739588 := by decide
  rcases family_descends (prefixWord ++ tailWord_739588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739616 : List Nat := [2, 1, 1, 5, 2, 2, 1, 7]
def baseStart_739616 : Nat := 118140960795 + 739616 * 2 ^ 59
def prefixEnd_739616 : Nat := 4983230072969 + 3 ^ 40 * 739616 * 2
def baseEnd_739616 : Nat := 56263482630501256696085

theorem tailTrace_739616 : CollatzResearch.WordTrace tailWord_739616 prefixEnd_739616 56263482630501256696085 := by
  unfold tailWord_739616
  simp only [CollatzResearch.WordTrace]
  refine ⟨13488005844252511600675351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17984007792336682134233801 13488005844252511600675351)
  ·
    refine ⟨20232008766378767401013027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13488005844252511600675351 20232008766378767401013027)
    ·
      refine ⟨30348013149568151101519541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20232008766378767401013027 30348013149568151101519541)
      ·
        refine ⟨2845126232772014165767457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30348013149568151101519541 2845126232772014165767457)
        ·
          refine ⟨2133844674579010624325593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2845126232772014165767457 2133844674579010624325593)
          ·
            refine ⟨1600383505934257968244195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2133844674579010624325593 1600383505934257968244195)
            ·
              refine ⟨2400575258901386952366293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1600383505934257968244195 2400575258901386952366293)
              ·
                refine ⟨56263482630501256696085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2400575258901386952366293 56263482630501256696085)
                ·
                  rfl

theorem cell21_739616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 7].length) (baseStart_739616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739616 prefixEnd_739616 := by exact prefixLift 739616
  have htrace : WordTrace (prefixWord ++ tailWord_739616) baseStart_739616 baseEnd_739616 := by
    simpa [prefixWord, tailWord_739616, baseEnd_739616] using wordTrace_append hprefix tailTrace_739616
  have hstable : (prefixWord ++ tailWord_739616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739616).length < 2 ^ (prefixWord ++ tailWord_739616).sum := by decide
  have hdescent : baseEnd_739616 < baseStart_739616 := by decide
  rcases family_descends (prefixWord ++ tailWord_739616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739633 : List Nat := [1, 2, 2, 3, 5, 1, 7]
def baseStart_739633 : Nat := 118140960795 + 739633 * 2 ^ 59
def prefixEnd_739633 : Nat := 4983230072969 + 3 ^ 40 * 739633 * 2
def baseEnd_739633 : Nat := 18754925280346168700543

theorem tailTrace_739633 : CollatzResearch.WordTrace tailWord_739633 prefixEnd_739633 18754925280346168700543 := by
  unfold tailWord_739633
  simp only [CollatzResearch.WordTrace]
  refine ⟨26976631729443435104719553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17984421152962290069813035 26976631729443435104719553)
  ·
    refine ⟨20232473797082576328539665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26976631729443435104719553 20232473797082576328539665)
    ·
      refine ⟨15174355347811932246404749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20232473797082576328539665 15174355347811932246404749)
      ·
        refine ⟨5690383255429474592401781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15174355347811932246404749 5690383255429474592401781)
        ·
          refine ⟨533473430196513243037667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5690383255429474592401781 533473430196513243037667)
          ·
            refine ⟨800210145294769864556501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533473430196513243037667 800210145294769864556501)
            ·
              refine ⟨18754925280346168700543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 800210145294769864556501 18754925280346168700543)
              ·
                rfl

theorem cell21_739633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 7].length) (baseStart_739633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739633 prefixEnd_739633 := by exact prefixLift 739633
  have htrace : WordTrace (prefixWord ++ tailWord_739633) baseStart_739633 baseEnd_739633 := by
    simpa [prefixWord, tailWord_739633, baseEnd_739633] using wordTrace_append hprefix tailTrace_739633
  have hstable : (prefixWord ++ tailWord_739633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739633).length < 2 ^ (prefixWord ++ tailWord_739633).sum := by decide
  have hdescent : baseEnd_739633 < baseStart_739633 := by decide
  rcases family_descends (prefixWord ++ tailWord_739633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739692 : List Nat := [2, 2, 1, 1, 7, 8]
def baseStart_739692 : Nat := 118140960795 + 739692 * 2 ^ 59
def prefixEnd_739692 : Nat := 4983230072969 + 3 ^ 40 * 739692 * 2
def baseEnd_739692 : Nat := 6252140449146093585979

theorem tailTrace_739692 : CollatzResearch.WordTrace tailWord_739692 prefixEnd_739692 6252140449146093585979 := by
  unfold tailWord_739692
  simp only [CollatzResearch.WordTrace]
  refine ⟨13489391818114844090558665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17985855757486458787411553 13489391818114844090558665)
  ·
    refine ⟨10117043863586133067918999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13489391818114844090558665 10117043863586133067918999)
    ·
      refine ⟨15175565795379199601878499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10117043863586133067918999 15175565795379199601878499)
      ·
        refine ⟨22763348693068799402817749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15175565795379199601878499 22763348693068799402817749)
        ·
          refine ⟨533515984993799986003541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 22763348693068799402817749 533515984993799986003541)
          ·
            refine ⟨6252140449146093585979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 533515984993799986003541 6252140449146093585979)
            ·
              rfl

theorem cell21_739692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 8].length) (baseStart_739692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739692 prefixEnd_739692 := by exact prefixLift 739692
  have htrace : WordTrace (prefixWord ++ tailWord_739692) baseStart_739692 baseEnd_739692 := by
    simpa [prefixWord, tailWord_739692, baseEnd_739692] using wordTrace_append hprefix tailTrace_739692
  have hstable : (prefixWord ++ tailWord_739692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739692).length < 2 ^ (prefixWord ++ tailWord_739692).sum := by decide
  have hdescent : baseEnd_739692 < baseStart_739692 := by decide
  rcases family_descends (prefixWord ++ tailWord_739692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739827 : List Nat := [1, 1, 1, 2, 2, 2, 6, 6]
def baseStart_739827 : Nat := 118140960795 + 739827 * 2 ^ 59
def prefixEnd_739827 : Nat := 4983230072969 + 3 ^ 40 * 739827 * 2
def baseEnd_739827 : Nat := 56279533655404764023719

theorem tailTrace_739827 : CollatzResearch.WordTrace tailWord_739827 prefixEnd_739827 56279533655404764023719 := by
  unfold tailWord_739827
  simp only [CollatzResearch.WordTrace]
  refine ⟨26983707490740606237281735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17989138327160404158187823 26983707490740606237281735)
  ·
    refine ⟨40475561236110909355922603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26983707490740606237281735 40475561236110909355922603)
    ·
      refine ⟨60713341854166364033883905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40475561236110909355922603 60713341854166364033883905)
      ·
        refine ⟨45535006390624773025412929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60713341854166364033883905 45535006390624773025412929)
        ·
          refine ⟨34151254792968579769059697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45535006390624773025412929 34151254792968579769059697)
          ·
            refine ⟨25613441094726434826794773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34151254792968579769059697 25613441094726434826794773)
            ·
              refine ⟨1200630051315301632506005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25613441094726434826794773 1200630051315301632506005)
              ·
                refine ⟨56279533655404764023719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1200630051315301632506005 56279533655404764023719)
                ·
                  rfl

theorem cell21_739827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 6].length) (baseStart_739827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739827 prefixEnd_739827 := by exact prefixLift 739827
  have htrace : WordTrace (prefixWord ++ tailWord_739827) baseStart_739827 baseEnd_739827 := by
    simpa [prefixWord, tailWord_739827, baseEnd_739827] using wordTrace_append hprefix tailTrace_739827
  have hstable : (prefixWord ++ tailWord_739827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739827).length < 2 ^ (prefixWord ++ tailWord_739827).sum := by decide
  have hdescent : baseEnd_739827 < baseStart_739827 := by decide
  rcases family_descends (prefixWord ++ tailWord_739827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739830 : List Nat := [5, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_739830 : Nat := 118140960795 + 739830 * 2 ^ 59
def prefixEnd_739830 : Nat := 4983230072969 + 3 ^ 40 * 739830 * 2
def baseEnd_739830 : Nat := 168839285607086953521151

theorem tailTrace_739830 : CollatzResearch.WordTrace tailWord_739830 prefixEnd_739830 168839285607086953521151 := by
  unfold tailWord_739830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1686488556858108609352559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17989211273153158499760629 1686488556858108609352559)
  ·
    refine ⟨2529732835287162914028839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1686488556858108609352559 2529732835287162914028839)
    ·
      refine ⟨3794599252930744371043259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2529732835287162914028839 3794599252930744371043259)
      ·
        refine ⟨5691898879396116556564889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3794599252930744371043259 5691898879396116556564889)
        ·
          refine ⟨4268924159547087417423667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5691898879396116556564889 4268924159547087417423667)
          ·
            refine ⟨6403386239320631126135501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4268924159547087417423667 6403386239320631126135501)
            ·
              refine ⟨2401269839745236672300813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6403386239320631126135501 2401269839745236672300813)
              ·
                refine ⟨900476189904463752112805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2401269839745236672300813 900476189904463752112805)
                ·
                  refine ⟨168839285607086953521151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 900476189904463752112805 168839285607086953521151)
                  ·
                    rfl

theorem cell21_739830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_739830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739830 prefixEnd_739830 := by exact prefixLift 739830
  have htrace : WordTrace (prefixWord ++ tailWord_739830) baseStart_739830 baseEnd_739830 := by
    simpa [prefixWord, tailWord_739830, baseEnd_739830] using wordTrace_append hprefix tailTrace_739830
  have hstable : (prefixWord ++ tailWord_739830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739830).length < 2 ^ (prefixWord ++ tailWord_739830).sum := by decide
  have hdescent : baseEnd_739830 < baseStart_739830 := by decide
  rcases family_descends (prefixWord ++ tailWord_739830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739844 : List Nat := [2, 3, 2, 3, 1, 1, 2, 7]
def baseStart_739844 : Nat := 118140960795 + 739844 * 2 ^ 59
def prefixEnd_739844 : Nat := 4983230072969 + 3 ^ 40 * 739844 * 2
def baseEnd_739844 : Nat := 56280826865942013429263

theorem tailTrace_739844 : CollatzResearch.WordTrace tailWord_739844 prefixEnd_739844 56280826865942013429263 := by
  unfold tailWord_739844
  simp only [CollatzResearch.WordTrace]
  refine ⟨13492163765839509070325293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17989551687786012093767057 13492163765839509070325293)
  ·
    refine ⟨5059561412189815901371985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13492163765839509070325293 5059561412189815901371985)
    ·
      refine ⟨3794671059142361926028989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5059561412189815901371985 3794671059142361926028989)
      ·
        refine ⟨1423001647178385722260871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3794671059142361926028989 1423001647178385722260871)
        ·
          refine ⟨2134502470767578583391307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1423001647178385722260871 2134502470767578583391307)
          ·
            refine ⟨3201753706151367875086961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2134502470767578583391307 3201753706151367875086961)
            ·
              refine ⟨2401315279613525906315221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3201753706151367875086961 2401315279613525906315221)
              ·
                refine ⟨56280826865942013429263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2401315279613525906315221 56280826865942013429263)
                ·
                  rfl

theorem cell21_739844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 7].length) (baseStart_739844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739844 prefixEnd_739844 := by exact prefixLift 739844
  have htrace : WordTrace (prefixWord ++ tailWord_739844) baseStart_739844 baseEnd_739844 := by
    simpa [prefixWord, tailWord_739844, baseEnd_739844] using wordTrace_append hprefix tailTrace_739844
  have hstable : (prefixWord ++ tailWord_739844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739844).length < 2 ^ (prefixWord ++ tailWord_739844).sum := by decide
  have hdescent : baseEnd_739844 < baseStart_739844 := by decide
  rcases family_descends (prefixWord ++ tailWord_739844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739889 : List Nat := [1, 2, 2, 3, 1, 1, 4, 3, 4]
def baseStart_739889 : Nat := 118140960795 + 739889 * 2 ^ 59
def prefixEnd_739889 : Nat := 4983230072969 + 3 ^ 40 * 739889 * 2
def baseEnd_739889 : Nat := 168852750210915962037697

theorem tailTrace_739889 : CollatzResearch.WordTrace tailWord_739889 prefixEnd_739889 168852750210915962037697 := by
  unfold tailWord_739889
  simp only [CollatzResearch.WordTrace]
  refine ⟨26985968816515990826038721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17990645877677327217359147 26985968816515990826038721)
  ·
    refine ⟨20239476612386993119529041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26985968816515990826038721 20239476612386993119529041)
    ·
      refine ⟨15179607459290244839646781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20239476612386993119529041 15179607459290244839646781)
      ·
        refine ⟨5692352797233841814867543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15179607459290244839646781 5692352797233841814867543)
        ·
          refine ⟨8538529195850762722301315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5692352797233841814867543 8538529195850762722301315)
          ·
            refine ⟨12807793793776144083451973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8538529195850762722301315 12807793793776144083451973)
            ·
              refine ⟨2401461336333027015647245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12807793793776144083451973 2401461336333027015647245)
              ·
                refine ⟨900548001124885130867717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2401461336333027015647245 900548001124885130867717)
                ·
                  refine ⟨168852750210915962037697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 900548001124885130867717 168852750210915962037697)
                  ·
                    rfl

theorem cell21_739889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 4].length) (baseStart_739889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739889 prefixEnd_739889 := by exact prefixLift 739889
  have htrace : WordTrace (prefixWord ++ tailWord_739889) baseStart_739889 baseEnd_739889 := by
    simpa [prefixWord, tailWord_739889, baseEnd_739889] using wordTrace_append hprefix tailTrace_739889
  have hstable : (prefixWord ++ tailWord_739889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739889).length < 2 ^ (prefixWord ++ tailWord_739889).sum := by decide
  have hdescent : baseEnd_739889 < baseStart_739889 := by decide
  rcases family_descends (prefixWord ++ tailWord_739889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739954 : List Nat := [3, 2, 1, 2, 5, 1, 2, 5]
def baseStart_739954 : Nat := 118140960795 + 739954 * 2 ^ 59
def prefixEnd_739954 : Nat := 4983230072969 + 3 ^ 40 * 739954 * 2
def baseEnd_739954 : Nat := 56289194698830097818077

theorem tailTrace_739954 : CollatzResearch.WordTrace tailWord_739954 prefixEnd_739954 56289194698830097818077 := by
  unfold tailWord_739954
  simp only [CollatzResearch.WordTrace]
  refine ⟨6747084890320126731788729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17992226374187004618103277 6747084890320126731788729)
  ·
    refine ⟨5060313667740095048841547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6747084890320126731788729 5060313667740095048841547)
    ·
      refine ⟨7590470501610142573262321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5060313667740095048841547 7590470501610142573262321)
      ·
        refine ⟨5692852876207606929946741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7590470501610142573262321 5692852876207606929946741)
        ·
          refine ⟨533704957144463149682507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5692852876207606929946741 533704957144463149682507)
          ·
            refine ⟨800557435716694724523761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533704957144463149682507 800557435716694724523761)
            ·
              refine ⟨600418076787521043392821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 800557435716694724523761 600418076787521043392821)
              ·
                refine ⟨56289194698830097818077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 600418076787521043392821 56289194698830097818077)
                ·
                  rfl

theorem cell21_739954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 5].length) (baseStart_739954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739954 prefixEnd_739954 := by exact prefixLift 739954
  have htrace : WordTrace (prefixWord ++ tailWord_739954) baseStart_739954 baseEnd_739954 := by
    simpa [prefixWord, tailWord_739954, baseEnd_739954] using wordTrace_append hprefix tailTrace_739954
  have hstable : (prefixWord ++ tailWord_739954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739954).length < 2 ^ (prefixWord ++ tailWord_739954).sum := by decide
  have hdescent : baseEnd_739954 < baseStart_739954 := by decide
  rcases family_descends (prefixWord ++ tailWord_739954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739968 : List Nat := [2, 1, 1, 2, 1, 7, 1, 3, 3]
def baseStart_739968 : Nat := 118140960795 + 739968 * 2 ^ 59
def prefixEnd_739968 : Nat := 4983230072969 + 3 ^ 40 * 739968 * 2
def baseEnd_739968 : Nat := 168870779087229380220869

theorem tailTrace_739968 : CollatzResearch.WordTrace tailWord_739968 prefixEnd_739968 168870779087229380220869 := by
  unfold tailWord_739968
  simp only [CollatzResearch.WordTrace]
  refine ⟨13494425091614893659082279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17992566788819858212109705 13494425091614893659082279)
  ·
    refine ⟨20241637637422340488623419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13494425091614893659082279 20241637637422340488623419)
    ·
      refine ⟨30362456456133510732935129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20241637637422340488623419 30362456456133510732935129)
      ·
        refine ⟨22771842342100133049701347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30362456456133510732935129 22771842342100133049701347)
        ·
          refine ⟨34157763513150199574552021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22771842342100133049701347 34157763513150199574552021)
          ·
            refine ⟨800572582339457802528563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 34157763513150199574552021 800572582339457802528563)
            ·
              refine ⟨1200858873509186703792845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 800572582339457802528563 1200858873509186703792845)
              ·
                refine ⟨450322077565945013922317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1200858873509186703792845 450322077565945013922317)
                ·
                  refine ⟨168870779087229380220869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 450322077565945013922317 168870779087229380220869)
                  ·
                    rfl

theorem cell21_739968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 3].length) (baseStart_739968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739968 prefixEnd_739968 := by exact prefixLift 739968
  have htrace : WordTrace (prefixWord ++ tailWord_739968) baseStart_739968 baseEnd_739968 := by
    simpa [prefixWord, tailWord_739968, baseEnd_739968] using wordTrace_append hprefix tailTrace_739968
  have hstable : (prefixWord ++ tailWord_739968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739968).length < 2 ^ (prefixWord ++ tailWord_739968).sum := by decide
  have hdescent : baseEnd_739968 < baseStart_739968 := by decide
  rcases family_descends (prefixWord ++ tailWord_739968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739996 : List Nat := [2, 2, 3, 2, 2, 2, 2, 6]
def baseStart_739996 : Nat := 118140960795 + 739996 * 2 ^ 59
def prefixEnd_739996 : Nat := 4983230072969 + 3 ^ 40 * 739996 * 2
def baseEnd_739996 : Nat := 56292389689569184584715

theorem tailTrace_739996 : CollatzResearch.WordTrace tailWord_739996 prefixEnd_739996 56292389689569184584715 := by
  unfold tailWord_739996
  simp only [CollatzResearch.WordTrace]
  refine ⟨13494935713564174050091921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17993247618085565400122561 13494935713564174050091921)
  ·
    refine ⟨10121201785173130537568941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13494935713564174050091921 10121201785173130537568941)
    ·
      refine ⟨3795450669439923951588353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10121201785173130537568941 3795450669439923951588353)
      ·
        refine ⟨2846588002079942963691265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3795450669439923951588353 2846588002079942963691265)
        ·
          refine ⟨2134941001559957222768449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2846588002079942963691265 2134941001559957222768449)
          ·
            refine ⟨1601205751169967917076337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2134941001559957222768449 1601205751169967917076337)
            ·
              refine ⟨1200904313377475937807253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601205751169967917076337 1200904313377475937807253)
              ·
                refine ⟨56292389689569184584715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1200904313377475937807253 56292389689569184584715)
                ·
                  rfl

theorem cell21_739996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 6].length) (baseStart_739996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_739996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_739996 prefixEnd_739996 := by exact prefixLift 739996
  have htrace : WordTrace (prefixWord ++ tailWord_739996) baseStart_739996 baseEnd_739996 := by
    simpa [prefixWord, tailWord_739996, baseEnd_739996] using wordTrace_append hprefix tailTrace_739996
  have hstable : (prefixWord ++ tailWord_739996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739996).length < 2 ^ (prefixWord ++ tailWord_739996).sum := by decide
  have hdescent : baseEnd_739996 < baseStart_739996 := by decide
  rcases family_descends (prefixWord ++ tailWord_739996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740044 : List Nat := [2, 2, 1, 5, 1, 2, 1, 4, 3]
def baseStart_740044 : Nat := 118140960795 + 740044 * 2 ^ 59
def prefixEnd_740044 : Nat := 4983230072969 + 3 ^ 40 * 740044 * 2
def baseEnd_740044 : Nat := 168888123322670136954047

theorem tailTrace_740044 : CollatzResearch.WordTrace tailWord_740044 prefixEnd_740044 168888123322670136954047 := by
  unfold tailWord_740044
  simp only [CollatzResearch.WordTrace]
  refine ⟨13495811065477226148965593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17994414753969634865287457 13495811065477226148965593)
  ·
    refine ⟨10121858299107919611724195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13495811065477226148965593 10121858299107919611724195)
    ·
      refine ⟨15182787448661879417586293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10121858299107919611724195 15182787448661879417586293)
      ·
        refine ⟨1423386323312051195398715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15182787448661879417586293 1423386323312051195398715)
        ·
          refine ⟨2135079484968076793098073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1423386323312051195398715 2135079484968076793098073)
          ·
            refine ⟨1601309613726057594823555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2135079484968076793098073 1601309613726057594823555)
            ·
              refine ⟨2401964420589086392235333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1601309613726057594823555 2401964420589086392235333)
              ·
                refine ⟨450368328860453698544125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2401964420589086392235333 450368328860453698544125)
                ·
                  refine ⟨168888123322670136954047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 450368328860453698544125 168888123322670136954047)
                  ·
                    rfl

theorem cell21_740044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 3].length) (baseStart_740044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_740044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_740044 prefixEnd_740044 := by exact prefixLift 740044
  have htrace : WordTrace (prefixWord ++ tailWord_740044) baseStart_740044 baseEnd_740044 := by
    simpa [prefixWord, tailWord_740044, baseEnd_740044] using wordTrace_append hprefix tailTrace_740044
  have hstable : (prefixWord ++ tailWord_740044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740044).length < 2 ^ (prefixWord ++ tailWord_740044).sum := by decide
  have hdescent : baseEnd_740044 < baseStart_740044 := by decide
  rcases family_descends (prefixWord ++ tailWord_740044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740055 : List Nat := [1, 1, 3, 2, 1, 4, 3, 6]
def baseStart_740055 : Nat := 118140960795 + 740055 * 2 ^ 59
def prefixEnd_740055 : Nat := 4983230072969 + 3 ^ 40 * 740055 * 2
def baseEnd_740055 : Nat := 56296877890845520756897

theorem tailTrace_740055 : CollatzResearch.WordTrace tailWord_740055 prefixEnd_740055 56296877890845520756897 := by
  unfold tailWord_740055
  simp only [CollatzResearch.WordTrace]
  refine ⟨26992023333914601176581619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17994682222609734117721079 26992023333914601176581619)
  ·
    refine ⟨40488035000871901764872429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26992023333914601176581619 40488035000871901764872429)
    ·
      refine ⟨15183013125326963161827161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40488035000871901764872429 15183013125326963161827161)
      ·
        refine ⟨11387259843995222371370371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15183013125326963161827161 11387259843995222371370371)
        ·
          refine ⟨17080889765992833557055557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11387259843995222371370371 17080889765992833557055557)
          ·
            refine ⟨3202666831123656291947917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17080889765992833557055557 3202666831123656291947917)
            ·
              refine ⟨1201000061671371109480469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3202666831123656291947917 1201000061671371109480469)
              ·
                refine ⟨56296877890845520756897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1201000061671371109480469 56296877890845520756897)
                ·
                  rfl

theorem cell21_740055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 6].length) (baseStart_740055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_740055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_740055 prefixEnd_740055 := by exact prefixLift 740055
  have htrace : WordTrace (prefixWord ++ tailWord_740055) baseStart_740055 baseEnd_740055 := by
    simpa [prefixWord, tailWord_740055, baseEnd_740055] using wordTrace_append hprefix tailTrace_740055
  have hstable : (prefixWord ++ tailWord_740055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740055).length < 2 ^ (prefixWord ++ tailWord_740055).sum := by decide
  have hdescent : baseEnd_740055 < baseStart_740055 := by decide
  rcases family_descends (prefixWord ++ tailWord_740055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740086 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_740086 : Nat := 118140960795 + 740086 * 2 ^ 59
def prefixEnd_740086 : Nat := 4983230072969 + 3 ^ 40 * 740086 * 2
def baseEnd_740086 : Nat := 168897708294887397253961

theorem tailTrace_740086 : CollatzResearch.WordTrace tailWord_740086 prefixEnd_740086 168897708294887397253961 := by
  unfold tailWord_740086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1687072124800143341935007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17995435997868195647306741 1687072124800143341935007)
  ·
    refine ⟨2530608187200215012902511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1687072124800143341935007 2530608187200215012902511)
    ·
      refine ⟨3795912280800322519353767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2530608187200215012902511 3795912280800322519353767)
      ·
        refine ⟨5693868421200483779030651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3795912280800322519353767 5693868421200483779030651)
        ·
          refine ⟨8540802631800725668545977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5693868421200483779030651 8540802631800725668545977)
          ·
            refine ⟨6405601973850544251409483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8540802631800725668545977 6405601973850544251409483)
            ·
              refine ⟨9608402960775816377114225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6405601973850544251409483 9608402960775816377114225)
              ·
                refine ⟨7206302220581862282835669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9608402960775816377114225 7206302220581862282835669)
                ·
                  refine ⟨168897708294887397253961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7206302220581862282835669 168897708294887397253961)
                  ·
                    rfl

theorem cell21_740086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_740086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_740086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_740086 prefixEnd_740086 := by exact prefixLift 740086
  have htrace : WordTrace (prefixWord ++ tailWord_740086) baseStart_740086 baseEnd_740086 := by
    simpa [prefixWord, tailWord_740086, baseEnd_740086] using wordTrace_append hprefix tailTrace_740086
  have hstable : (prefixWord ++ tailWord_740086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740086).length < 2 ^ (prefixWord ++ tailWord_740086).sum := by decide
  have hdescent : baseEnd_740086 < baseStart_740086 := by decide
  rcases family_descends (prefixWord ++ tailWord_740086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740103 : List Nat := [1, 1, 4, 4, 1, 2, 2, 1, 5]
def baseStart_740103 : Nat := 118140960795 + 740103 * 2 ^ 59
def prefixEnd_740103 : Nat := 4983230072969 + 3 ^ 40 * 740103 * 2
def baseEnd_740103 : Nat := 168901587926499145470593

theorem tailTrace_740103 : CollatzResearch.WordTrace tailWord_740103 prefixEnd_740103 168901587926499145470593 := by
  unfold tailWord_740103
  simp only [CollatzResearch.WordTrace]
  refine ⟨26993774037740705374328963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17995849358493803582885975 26993774037740705374328963)
  ·
    refine ⟨40490661056611058061493445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26993774037740705374328963 40490661056611058061493445)
    ·
      refine ⟨7591998948114573386530021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40490661056611058061493445 7591998948114573386530021)
      ·
        refine ⟨1423499802771482509974379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7591998948114573386530021 1423499802771482509974379)
        ·
          refine ⟨2135249704157223764961569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1423499802771482509974379 2135249704157223764961569)
          ·
            refine ⟨1601437278117917823721177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2135249704157223764961569 1601437278117917823721177)
            ·
              refine ⟨1201077958588438367790883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601437278117917823721177 1201077958588438367790883)
              ·
                refine ⟨1801616937882657551686325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1201077958588438367790883 1801616937882657551686325)
                ·
                  refine ⟨168901587926499145470593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1801616937882657551686325 168901587926499145470593)
                  ·
                    rfl

theorem cell21_740103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 5].length) (baseStart_740103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_740103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_740103 prefixEnd_740103 := by exact prefixLift 740103
  have htrace : WordTrace (prefixWord ++ tailWord_740103) baseStart_740103 baseEnd_740103 := by
    simpa [prefixWord, tailWord_740103, baseEnd_740103] using wordTrace_append hprefix tailTrace_740103
  have hstable : (prefixWord ++ tailWord_740103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740103).length < 2 ^ (prefixWord ++ tailWord_740103).sum := by decide
  have hdescent : baseEnd_740103 < baseStart_740103 := by decide
  rcases family_descends (prefixWord ++ tailWord_740103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740213 : List Nat := [1, 3, 4, 1, 1, 4, 2, 2, 3]
def baseStart_740213 : Nat := 118140960795 + 740213 * 2 ^ 59
def prefixEnd_740213 : Nat := 4983230072969 + 3 ^ 40 * 740213 * 2
def baseEnd_740213 : Nat := 168926691425163398637035

theorem tailTrace_740213 : CollatzResearch.WordTrace tailWord_740213 prefixEnd_740213 168926691425163398637035 := by
  unfold tailWord_740213
  simp only [CollatzResearch.WordTrace]
  refine ⟨26997786067342194160833293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17998524044894796107222195 26997786067342194160833293)
  ·
    refine ⟨10124169775253322810312485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26997786067342194160833293 10124169775253322810312485)
    ·
      refine ⟨1898281832859998026933591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10124169775253322810312485 1898281832859998026933591)
      ·
        refine ⟨2847422749289997040400387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1898281832859998026933591 2847422749289997040400387)
        ·
          refine ⟨4271134123934995560600581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2847422749289997040400387 4271134123934995560600581)
          ·
            refine ⟨800837648237811667612609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4271134123934995560600581 800837648237811667612609)
            ·
              refine ⟨600628236178358750709457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 800837648237811667612609 600628236178358750709457)
              ·
                refine ⟨450471177133769063032093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 600628236178358750709457 450471177133769063032093)
                ·
                  refine ⟨168926691425163398637035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 450471177133769063032093 168926691425163398637035)
                  ·
                    rfl

theorem cell21_740213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 3].length) (baseStart_740213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_740213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_740213 prefixEnd_740213 := by exact prefixLift 740213
  have htrace : WordTrace (prefixWord ++ tailWord_740213) baseStart_740213 baseEnd_740213 := by
    simpa [prefixWord, tailWord_740213, baseEnd_740213] using wordTrace_append hprefix tailTrace_740213
  have hstable : (prefixWord ++ tailWord_740213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740213).length < 2 ^ (prefixWord ++ tailWord_740213).sum := by decide
  have hdescent : baseEnd_740213 < baseStart_740213 := by decide
  rcases family_descends (prefixWord ++ tailWord_740213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740255 : List Nat := [1, 1, 2, 5, 2, 1, 1, 5, 3]
def baseStart_740255 : Nat := 118140960795 + 740255 * 2 ^ 59
def prefixEnd_740255 : Nat := 4983230072969 + 3 ^ 40 * 740255 * 2
def baseEnd_740255 : Nat := 168936276397380658936949

theorem tailTrace_740255 : CollatzResearch.WordTrace tailWord_740255 prefixEnd_740255 168936276397380658936949 := by
  unfold tailWord_740255
  simp only [CollatzResearch.WordTrace]
  refine ⟨26999317933190035333862219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17999545288793356889241479 26999317933190035333862219)
  ·
    refine ⟨40498976899785053000793329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26999317933190035333862219 40498976899785053000793329)
    ·
      refine ⟨30374232674838789750594997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40498976899785053000793329 30374232674838789750594997)
      ·
        refine ⟨2847584313266136539118281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30374232674838789750594997 2847584313266136539118281)
        ·
          refine ⟨2135688234949602404338711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2847584313266136539118281 2135688234949602404338711)
          ·
            refine ⟨3203532352424403606508067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2135688234949602404338711 3203532352424403606508067)
            ·
              refine ⟨4805298528636605409762101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3203532352424403606508067 4805298528636605409762101)
              ·
                refine ⟨450496737059681757165197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4805298528636605409762101 450496737059681757165197)
                ·
                  refine ⟨168936276397380658936949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 450496737059681757165197 168936276397380658936949)
                  ·
                    rfl

theorem cell21_740255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 3].length) (baseStart_740255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_740255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_740255 prefixEnd_740255 := by exact prefixLift 740255
  have htrace : WordTrace (prefixWord ++ tailWord_740255) baseStart_740255 baseEnd_740255 := by
    simpa [prefixWord, tailWord_740255, baseEnd_740255] using wordTrace_append hprefix tailTrace_740255
  have hstable : (prefixWord ++ tailWord_740255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740255).length < 2 ^ (prefixWord ++ tailWord_740255).sum := by decide
  have hdescent : baseEnd_740255 < baseStart_740255 := by decide
  rcases family_descends (prefixWord ++ tailWord_740255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740286 : List Nat := [4, 2, 1, 1, 1, 2, 5, 1, 4]
def baseStart_740286 : Nat := 118140960795 + 740286 * 2 ^ 59
def prefixEnd_740286 : Nat := 4983230072969 + 3 ^ 40 * 740286 * 2
def baseEnd_740286 : Nat := 168943351019731493920219

theorem tailTrace_740286 : CollatzResearch.WordTrace tailWord_740286 prefixEnd_740286 168943351019731493920219 := by
  unfold tailWord_740286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3375056074509715953530089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18000299064051818418827141 3375056074509715953530089)
  ·
    refine ⟨2531292055882286965147567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3375056074509715953530089 2531292055882286965147567)
    ·
      refine ⟨3796938083823430447721351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2531292055882286965147567 3796938083823430447721351)
      ·
        refine ⟨5695407125735145671582027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3796938083823430447721351 5695407125735145671582027)
        ·
          refine ⟨8543110688602718507373041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5695407125735145671582027 8543110688602718507373041)
          ·
            refine ⟨6407333016452038880529781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8543110688602718507373041 6407333016452038880529781)
            ·
              refine ⟨600687470292378645049667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6407333016452038880529781 600687470292378645049667)
              ·
                refine ⟨901031205438567967574501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 600687470292378645049667 901031205438567967574501)
                ·
                  refine ⟨168943351019731493920219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 901031205438567967574501 168943351019731493920219)
                  ·
                    rfl

theorem cell21_740286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_740286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_740286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_740286 prefixEnd_740286 := by exact prefixLift 740286
  have htrace : WordTrace (prefixWord ++ tailWord_740286) baseStart_740286 baseEnd_740286 := by
    simpa [prefixWord, tailWord_740286, baseEnd_740286] using wordTrace_append hprefix tailTrace_740286
  have hstable : (prefixWord ++ tailWord_740286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740286).length < 2 ^ (prefixWord ++ tailWord_740286).sum := by decide
  have hdescent : baseEnd_740286 < baseStart_740286 := by decide
  rcases family_descends (prefixWord ++ tailWord_740286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740328 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 6]
def baseStart_740328 : Nat := 118140960795 + 740328 * 2 ^ 59
def prefixEnd_740328 : Nat := 4983230072969 + 3 ^ 40 * 740328 * 2
def baseEnd_740328 : Nat := 168952935991948754220133

theorem tailTrace_740328 : CollatzResearch.WordTrace tailWord_740328 prefixEnd_740328 168952935991948754220133 := by
  unfold tailWord_740328
  simp only [CollatzResearch.WordTrace]
  refine ⟨13500990230962784400634819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18001320307950379200846425 13500990230962784400634819)
  ·
    refine ⟨20251485346444176600952229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13500990230962784400634819 20251485346444176600952229)
    ·
      refine ⟨3797153502458283112678543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20251485346444176600952229 3797153502458283112678543)
      ·
        refine ⟨5695730253687424669017815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3797153502458283112678543 5695730253687424669017815)
        ·
          refine ⟨8543595380531137003526723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5695730253687424669017815 8543595380531137003526723)
          ·
            refine ⟨12815393070796705505290085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8543595380531137003526723 12815393070796705505290085)
            ·
              refine ⟨2402886200774382282241891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12815393070796705505290085 2402886200774382282241891)
              ·
                refine ⟨3604329301161573423362837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2402886200774382282241891 3604329301161573423362837)
                ·
                  refine ⟨168952935991948754220133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3604329301161573423362837 168952935991948754220133)
                  ·
                    rfl

theorem cell21_740328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_740328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_740328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_740328 prefixEnd_740328 := by exact prefixLift 740328
  have htrace : WordTrace (prefixWord ++ tailWord_740328) baseStart_740328 baseEnd_740328 := by
    simpa [prefixWord, tailWord_740328, baseEnd_740328] using wordTrace_append hprefix tailTrace_740328
  have hstable : (prefixWord ++ tailWord_740328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740328).length < 2 ^ (prefixWord ++ tailWord_740328).sum := by decide
  have hdescent : baseEnd_740328 < baseStart_740328 := by decide
  rcases family_descends (prefixWord ++ tailWord_740328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740449 : List Nat := [1, 2, 3, 1, 1, 2, 3, 3, 5]
def baseStart_740449 : Nat := 118140960795 + 740449 * 2 ^ 59
def prefixEnd_740449 : Nat := 4983230072969 + 3 ^ 40 * 740449 * 2
def baseEnd_740449 : Nat := 168980549840479432703219

theorem tailTrace_740449 : CollatzResearch.WordTrace tailWord_740449 prefixEnd_740449 168980549840479432703219 := by
  unfold tailWord_740449
  simp only [CollatzResearch.WordTrace]
  refine ⟨27006393694487206466424401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18004262462991470977616267 27006393694487206466424401)
  ·
    refine ⟨20254795270865404849818301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27006393694487206466424401 20254795270865404849818301)
    ·
      refine ⟨7595548226574526818681863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20254795270865404849818301 7595548226574526818681863)
      ·
        refine ⟨11393322339861790228022795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7595548226574526818681863 11393322339861790228022795)
        ·
          refine ⟨17089983509792685342034193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11393322339861790228022795 17089983509792685342034193)
          ·
            refine ⟨12817487632344514006525645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17089983509792685342034193 12817487632344514006525645)
            ·
              refine ⟨4806557862129192752447117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12817487632344514006525645 4806557862129192752447117)
              ·
                refine ⟨1802459198298447282167669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4806557862129192752447117 1802459198298447282167669)
                ·
                  refine ⟨168980549840479432703219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1802459198298447282167669 168980549840479432703219)
                  ·
                    rfl

theorem cell21_740449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_740449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_740449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_740449 prefixEnd_740449 := by exact prefixLift 740449
  have htrace : WordTrace (prefixWord ++ tailWord_740449) baseStart_740449 baseEnd_740449 := by
    simpa [prefixWord, tailWord_740449, baseEnd_740449] using wordTrace_append hprefix tailTrace_740449
  have hstable : (prefixWord ++ tailWord_740449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740449).length < 2 ^ (prefixWord ++ tailWord_740449).sum := by decide
  have hdescent : baseEnd_740449 < baseStart_740449 := by decide
  rcases family_descends (prefixWord ++ tailWord_740449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740514 : List Nat := [3, 3, 1, 3, 2, 1, 1, 3, 4]
def baseStart_740514 : Nat := 118140960795 + 740514 * 2 ^ 59
def prefixEnd_740514 : Nat := 4983230072969 + 3 ^ 40 * 740514 * 2
def baseEnd_740514 : Nat := 168995383726053764119753

theorem tailTrace_740514 : CollatzResearch.WordTrace tailWord_740514 prefixEnd_740514 168995383726053764119753 := by
  unfold tailWord_740514
  simp only [CollatzResearch.WordTrace]
  refine ⟨6752191109812930641885149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18005842959501148378360397 6752191109812930641885149)
  ·
    refine ⟨2532071666179848990706931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6752191109812930641885149 2532071666179848990706931)
    ·
      refine ⟨3798107499269773486060397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2532071666179848990706931 3798107499269773486060397)
      ·
        refine ⟨1424290312226165057272649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3798107499269773486060397 1424290312226165057272649)
        ·
          refine ⟨1068217734169623792954487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1424290312226165057272649 1068217734169623792954487)
          ·
            refine ⟨1602326601254435689431731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068217734169623792954487 1602326601254435689431731)
            ·
              refine ⟨2403489901881653534147597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602326601254435689431731 2403489901881653534147597)
              ·
                refine ⟨901308713205620075305349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2403489901881653534147597 901308713205620075305349)
                ·
                  refine ⟨168995383726053764119753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 901308713205620075305349 168995383726053764119753)
                  ·
                    rfl

theorem cell21_740514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_740514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_740514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_740514 prefixEnd_740514 := by exact prefixLift 740514
  have htrace : WordTrace (prefixWord ++ tailWord_740514) baseStart_740514 baseEnd_740514 := by
    simpa [prefixWord, tailWord_740514, baseEnd_740514] using wordTrace_append hprefix tailTrace_740514
  have hstable : (prefixWord ++ tailWord_740514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740514).length < 2 ^ (prefixWord ++ tailWord_740514).sum := by decide
  have hdescent : baseEnd_740514 < baseStart_740514 := by decide
  rcases family_descends (prefixWord ++ tailWord_740514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740539 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 6]
def baseStart_740539 : Nat := 118140960795 + 740539 * 2 ^ 59
def prefixEnd_740539 : Nat := 4983230072969 + 3 ^ 40 * 740539 * 2
def baseEnd_740539 : Nat := 169001089066659276203035

theorem tailTrace_740539 : CollatzResearch.WordTrace tailWord_740539 prefixEnd_740539 169001089066659276203035 := by
  unfold tailWord_740539
  simp only [CollatzResearch.WordTrace]
  refine ⟨27009676264161151837200671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18006450842774101224800447 27009676264161151837200671)
  ·
    refine ⟨40514514396241727755801007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27009676264161151837200671 40514514396241727755801007)
    ·
      refine ⟨60771771594362591633701511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40514514396241727755801007 60771771594362591633701511)
      ·
        refine ⟨91157657391543887450552267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60771771594362591633701511 91157657391543887450552267)
        ·
          refine ⟨136736486087315831175828401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91157657391543887450552267 136736486087315831175828401)
          ·
            refine ⟨102552364565486873381871301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136736486087315831175828401 102552364565486873381871301)
            ·
              refine ⟨19228568356028788759100869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102552364565486873381871301 19228568356028788759100869)
              ·
                refine ⟨3605356566755397892331413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19228568356028788759100869 3605356566755397892331413)
                ·
                  refine ⟨169001089066659276203035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3605356566755397892331413 169001089066659276203035)
                  ·
                    rfl

theorem cell21_740539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 6].length) (baseStart_740539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_740539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_740539 prefixEnd_740539 := by exact prefixLift 740539
  have htrace : WordTrace (prefixWord ++ tailWord_740539) baseStart_740539 baseEnd_740539 := by
    simpa [prefixWord, tailWord_740539, baseEnd_740539] using wordTrace_append hprefix tailTrace_740539
  have hstable : (prefixWord ++ tailWord_740539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740539).length < 2 ^ (prefixWord ++ tailWord_740539).sum := by decide
  have hdescent : baseEnd_740539 < baseStart_740539 := by decide
  rcases family_descends (prefixWord ++ tailWord_740539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740587 : List Nat := [1, 1, 1, 1, 2, 7, 3, 5]
def baseStart_740587 : Nat := 118140960795 + 740587 * 2 ^ 59
def prefixEnd_740587 : Nat := 4983230072969 + 3 ^ 40 * 740587 * 2
def baseEnd_740587 : Nat := 56337347773540619800979

theorem tailTrace_740587 : CollatzResearch.WordTrace tailWord_740587 prefixEnd_740587 56337347773540619800979 := by
  unfold tailWord_740587
  simp only [CollatzResearch.WordTrace]
  refine ⟨27011426967987256034948015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18007617978658170689965343 27011426967987256034948015)
  ·
    refine ⟨40517140451980884052422023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27011426967987256034948015 40517140451980884052422023)
    ·
      refine ⟨60775710677971326078633035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40517140451980884052422023 60775710677971326078633035)
      ·
        refine ⟨91163566016956989117949553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60775710677971326078633035 91163566016956989117949553)
        ·
          refine ⟨68372674512717741838462165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91163566016956989117949553 68372674512717741838462165)
          ·
            refine ⟨1602484558891822074338957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 68372674512717741838462165 1602484558891822074338957)
            ·
              refine ⟨600931709584433277877109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1602484558891822074338957 600931709584433277877109)
              ·
                refine ⟨56337347773540619800979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 600931709584433277877109 56337347773540619800979)
                ·
                  rfl

theorem cell21_740587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 5].length) (baseStart_740587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_740587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_740587 prefixEnd_740587 := by exact prefixLift 740587
  have htrace : WordTrace (prefixWord ++ tailWord_740587) baseStart_740587 baseEnd_740587 := by
    simpa [prefixWord, tailWord_740587, baseEnd_740587] using wordTrace_append hprefix tailTrace_740587
  have hstable : (prefixWord ++ tailWord_740587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740587).length < 2 ^ (prefixWord ++ tailWord_740587).sum := by decide
  have hdescent : baseEnd_740587 < baseStart_740587 := by decide
  rcases family_descends (prefixWord ++ tailWord_740587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740638 : List Nat := [4, 3, 2, 1, 2, 2, 2, 5]
def baseStart_740638 : Nat := 118140960795 + 740638 * 2 ^ 59
def prefixEnd_740638 : Nat := 4983230072969 + 3 ^ 40 * 740638 * 2
def baseEnd_740638 : Nat := 56341227405152368017611

theorem tailTrace_740638 : CollatzResearch.WordTrace tailWord_740638 prefixEnd_740638 56341227405152368017611 := by
  unfold tailWord_740638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3376660886350311468131821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18008858060534994496703045 3376660886350311468131821)
  ·
    refine ⟨1266247832381366800549433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3376660886350311468131821 1266247832381366800549433)
    ·
      refine ⟨949685874286025100412075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1266247832381366800549433 949685874286025100412075)
      ·
        refine ⟨1424528811429037650618113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 949685874286025100412075 1424528811429037650618113)
        ·
          refine ⟨1068396608571778237963585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1424528811429037650618113 1068396608571778237963585)
          ·
            refine ⟨801297456428833678472689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1068396608571778237963585 801297456428833678472689)
            ·
              refine ⟨600973092321625258854517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 801297456428833678472689 600973092321625258854517)
              ·
                refine ⟨56341227405152368017611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 600973092321625258854517 56341227405152368017611)
                ·
                  rfl

theorem cell21_740638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_740638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_740638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_740638 prefixEnd_740638 := by exact prefixLift 740638
  have htrace : WordTrace (prefixWord ++ tailWord_740638) baseStart_740638 baseEnd_740638 := by
    simpa [prefixWord, tailWord_740638, baseEnd_740638] using wordTrace_append hprefix tailTrace_740638
  have hstable : (prefixWord ++ tailWord_740638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740638).length < 2 ^ (prefixWord ++ tailWord_740638).sum := by decide
  have hdescent : baseEnd_740638 < baseStart_740638 := by decide
  rcases family_descends (prefixWord ++ tailWord_740638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740669 : List Nat := [1, 4, 1, 5, 1, 1, 3, 2, 3]
def baseStart_740669 : Nat := 118140960795 + 740669 * 2 ^ 59
def prefixEnd_740669 : Nat := 4983230072969 + 3 ^ 40 * 740669 * 2
def baseEnd_740669 : Nat := 169030756837807939036103

theorem tailTrace_740669 : CollatzResearch.WordTrace tailWord_740669 prefixEnd_740669 169030756837807939036103 := by
  unfold tailWord_740669
  simp only [CollatzResearch.WordTrace]
  refine ⟨27014417753690184039433061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18009611835793456026288707 27014417753690184039433061)
  ·
    refine ⟨5065203328816909507393699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27014417753690184039433061 5065203328816909507393699)
    ·
      refine ⟨7597804993225364261090549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5065203328816909507393699 7597804993225364261090549)
      ·
        refine ⟨712294218114877899477239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7597804993225364261090549 712294218114877899477239)
        ·
          refine ⟨1068441327172316849215859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 712294218114877899477239 1068441327172316849215859)
          ·
            refine ⟨1602661990758475273823789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068441327172316849215859 1602661990758475273823789)
            ·
              refine ⟨600998246534428227683921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1602661990758475273823789 600998246534428227683921)
              ·
                refine ⟨450748684900821170762941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 600998246534428227683921 450748684900821170762941)
                ·
                  refine ⟨169030756837807939036103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 450748684900821170762941 169030756837807939036103)
                  ·
                    rfl

theorem cell21_740669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_740669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_740669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_740669 prefixEnd_740669 := by exact prefixLift 740669
  have htrace : WordTrace (prefixWord ++ tailWord_740669) baseStart_740669 baseEnd_740669 := by
    simpa [prefixWord, tailWord_740669, baseEnd_740669] using wordTrace_append hprefix tailTrace_740669
  have hstable : (prefixWord ++ tailWord_740669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740669).length < 2 ^ (prefixWord ++ tailWord_740669).sum := by decide
  have hdescent : baseEnd_740669 < baseStart_740669 := by decide
  rcases family_descends (prefixWord ++ tailWord_740669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740736 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 9]
def baseStart_740736 : Nat := 118140960795 + 740736 * 2 ^ 59
def prefixEnd_740736 : Nat := 4983230072969 + 3 ^ 40 * 740736 * 2
def baseEnd_740736 : Nat := 169046047150630711419299

theorem tailTrace_740736 : CollatzResearch.WordTrace tailWord_740736 prefixEnd_740736 169046047150630711419299 := by
  unfold tailWord_740736
  simp only [CollatzResearch.WordTrace]
  refine ⟨13508430722223727241061031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18011240962964969654748041 13508430722223727241061031)
  ·
    refine ⟨20262646083335590861591547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13508430722223727241061031 20262646083335590861591547)
    ·
      refine ⟨30393969125003386292387321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20262646083335590861591547 30393969125003386292387321)
      ·
        refine ⟨22795476843752539719290491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30393969125003386292387321 22795476843752539719290491)
        ·
          refine ⟨34193215265628809578935737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22795476843752539719290491 34193215265628809578935737)
          ·
            refine ⟨25644911449221607184201803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34193215265628809578935737 25644911449221607184201803)
            ·
              refine ⟨38467367173832410776302705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25644911449221607184201803 38467367173832410776302705)
              ·
                refine ⟨28850525380374308082227029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38467367173832410776302705 28850525380374308082227029)
                ·
                  refine ⟨169046047150630711419299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28850525380374308082227029 169046047150630711419299)
                  ·
                    rfl

theorem cell21_740736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_740736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_740736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_740736 prefixEnd_740736 := by exact prefixLift 740736
  have htrace : WordTrace (prefixWord ++ tailWord_740736) baseStart_740736 baseEnd_740736 := by
    simpa [prefixWord, tailWord_740736, baseEnd_740736] using wordTrace_append hprefix tailTrace_740736
  have hstable : (prefixWord ++ tailWord_740736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740736).length < 2 ^ (prefixWord ++ tailWord_740736).sum := by decide
  have hdescent : baseEnd_740736 < baseStart_740736 := by decide
  rcases family_descends (prefixWord ++ tailWord_740736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740739 : List Nat := [1, 1, 1, 3, 5, 3, 1, 6]
def baseStart_740739 : Nat := 118140960795 + 740739 * 2 ^ 59
def prefixEnd_740739 : Nat := 4983230072969 + 3 ^ 40 * 740739 * 2
def baseEnd_740739 : Nat := 56348910597167790956431

theorem tailTrace_740739 : CollatzResearch.WordTrace tailWord_740739 prefixEnd_740739 56348910597167790956431 := by
  unfold tailWord_740739
  simp only [CollatzResearch.WordTrace]
  refine ⟨27016970863436585994481271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18011313908957723996320847 27016970863436585994481271)
  ·
    refine ⟨40525456295154878991721907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27016970863436585994481271 40525456295154878991721907)
    ·
      refine ⟨60788184442732318487582861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40525456295154878991721907 60788184442732318487582861)
      ·
        refine ⟨22795569166024619432843573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60788184442732318487582861 22795569166024619432843573)
        ·
          refine ⟨2137084609314808071829085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22795569166024619432843573 2137084609314808071829085)
          ·
            refine ⟨801406728493053026935907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2137084609314808071829085 801406728493053026935907)
            ·
              refine ⟨1202110092739579540403861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 801406728493053026935907 1202110092739579540403861)
              ·
                refine ⟨56348910597167790956431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1202110092739579540403861 56348910597167790956431)
                ·
                  rfl

theorem cell21_740739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 6].length) (baseStart_740739 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_740739 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_740739 prefixEnd_740739 := by exact prefixLift 740739
  have htrace : WordTrace (prefixWord ++ tailWord_740739) baseStart_740739 baseEnd_740739 := by
    simpa [prefixWord, tailWord_740739, baseEnd_740739] using wordTrace_append hprefix tailTrace_740739
  have hstable : (prefixWord ++ tailWord_740739).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740739).length < 2 ^ (prefixWord ++ tailWord_740739).sum := by decide
  have hdescent : baseEnd_740739 < baseStart_740739 := by decide
  rcases family_descends (prefixWord ++ tailWord_740739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740756 : List Nat := [2, 4, 2, 1, 2, 2, 3, 5]
def baseStart_740756 : Nat := 118140960795 + 740756 * 2 ^ 59
def prefixEnd_740756 : Nat := 4983230072969 + 3 ^ 40 * 740756 * 2
def baseEnd_740756 : Nat := 56350203807705040361975

theorem tailTrace_740756 : CollatzResearch.WordTrace tailWord_740756 prefixEnd_740756 56350203807705040361975 := by
  unfold tailWord_740756
  simp only [CollatzResearch.WordTrace]
  refine ⟨13508795452187498948925061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18011727269583331931900081 13508795452187498948925061)
  ·
    refine ⟨2532899147285156052923449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13508795452187498948925061 2532899147285156052923449)
    ·
      refine ⟨1899674360463867039692587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2532899147285156052923449 1899674360463867039692587)
      ·
        refine ⟨2849511540695800559538881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1899674360463867039692587 2849511540695800559538881)
        ·
          refine ⟨2137133655521850419654161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2849511540695800559538881 2137133655521850419654161)
          ·
            refine ⟨1602850241641387814740621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2137133655521850419654161 1602850241641387814740621)
            ·
              refine ⟨601068840615520430527733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1602850241641387814740621 601068840615520430527733)
              ·
                refine ⟨56350203807705040361975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 601068840615520430527733 56350203807705040361975)
                ·
                  rfl

theorem cell21_740756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 5].length) (baseStart_740756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_740756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_740756 prefixEnd_740756 := by exact prefixLift 740756
  have htrace : WordTrace (prefixWord ++ tailWord_740756) baseStart_740756 baseEnd_740756 := by
    simpa [prefixWord, tailWord_740756, baseEnd_740756] using wordTrace_append hprefix tailTrace_740756
  have hstable : (prefixWord ++ tailWord_740756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740756).length < 2 ^ (prefixWord ++ tailWord_740756).sum := by decide
  have hdescent : baseEnd_740756 < baseStart_740756 := by decide
  rcases family_descends (prefixWord ++ tailWord_740756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740798 : List Nat := [4, 2, 1, 1, 1, 1, 1, 10]
def baseStart_740798 : Nat := 118140960795 + 740798 * 2 ^ 59
def prefixEnd_740798 : Nat := 4983230072969 + 3 ^ 40 * 740798 * 2
def baseEnd_740798 : Nat := 56353398798444127128613

theorem tailTrace_740798 : CollatzResearch.WordTrace tailWord_740798 prefixEnd_740798 56353398798444127128613 := by
  unfold tailWord_740798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3377390346277854883859881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18012748513481892713919365 3377390346277854883859881)
  ·
    refine ⟨2533042759708391162894911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3377390346277854883859881 2533042759708391162894911)
    ·
      refine ⟨3799564139562586744342367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2533042759708391162894911 3799564139562586744342367)
      ·
        refine ⟨5699346209343880116513551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3799564139562586744342367 5699346209343880116513551)
        ·
          refine ⟨8549019314015820174770327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5699346209343880116513551 8549019314015820174770327)
          ·
            refine ⟨12823528971023730262155491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8549019314015820174770327 12823528971023730262155491)
            ·
              refine ⟨19235293456535595393233237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12823528971023730262155491 19235293456535595393233237)
              ·
                refine ⟨56353398798444127128613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19235293456535595393233237 56353398798444127128613)
                ·
                  rfl

theorem cell21_740798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_740798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_740798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_740798 prefixEnd_740798 := by exact prefixLift 740798
  have htrace : WordTrace (prefixWord ++ tailWord_740798) baseStart_740798 baseEnd_740798 := by
    simpa [prefixWord, tailWord_740798, baseEnd_740798] using wordTrace_append hprefix tailTrace_740798
  have hstable : (prefixWord ++ tailWord_740798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740798).length < 2 ^ (prefixWord ++ tailWord_740798).sum := by decide
  have hdescent : baseEnd_740798 < baseStart_740798 := by decide
  rcases family_descends (prefixWord ++ tailWord_740798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740874 : List Nat := [3, 1, 2, 2, 2, 2, 2, 7]
def baseStart_740874 : Nat := 118140960795 + 740874 * 2 ^ 59
def prefixEnd_740874 : Nat := 4983230072969 + 3 ^ 40 * 740874 * 2
def baseEnd_740874 : Nat := 56359180210257712706339

theorem tailTrace_740874 : CollatzResearch.WordTrace tailWord_740874 prefixEnd_740874 56359180210257712706339 := by
  unfold tailWord_740874
  simp only [CollatzResearch.WordTrace]
  refine ⟨6755473679486876012661419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18014596478631669367097117 6755473679486876012661419)
  ·
    refine ⟨10133210519230314018992129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6755473679486876012661419 10133210519230314018992129)
    ·
      refine ⟨7599907889422735514244097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10133210519230314018992129 7599907889422735514244097)
      ·
        refine ⟨5699930917067051635683073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7599907889422735514244097 5699930917067051635683073)
        ·
          refine ⟨4274948187800288726762305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5699930917067051635683073 4274948187800288726762305)
          ·
            refine ⟨3206211140850216545071729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4274948187800288726762305 3206211140850216545071729)
            ·
              refine ⟨2404658355637662408803797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3206211140850216545071729 2404658355637662408803797)
              ·
                refine ⟨56359180210257712706339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2404658355637662408803797 56359180210257712706339)
                ·
                  rfl

theorem cell21_740874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_740874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_740874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_740874 prefixEnd_740874 := by exact prefixLift 740874
  have htrace : WordTrace (prefixWord ++ tailWord_740874) baseStart_740874 baseEnd_740874 := by
    simpa [prefixWord, tailWord_740874, baseEnd_740874] using wordTrace_append hprefix tailTrace_740874
  have hstable : (prefixWord ++ tailWord_740874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740874).length < 2 ^ (prefixWord ++ tailWord_740874).sum := by decide
  have hdescent : baseEnd_740874 < baseStart_740874 := by decide
  rcases family_descends (prefixWord ++ tailWord_740874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741015 : List Nat := [1, 1, 3, 3, 2, 3, 3, 2, 3]
def baseStart_741015 : Nat := 118140960795 + 741015 * 2 ^ 59
def prefixEnd_741015 : Nat := 4983230072969 + 3 ^ 40 * 741015 * 2
def baseEnd_741015 : Nat := 169109718751788226268729

theorem tailTrace_741015 : CollatzResearch.WordTrace tailWord_741015 prefixEnd_741015 169109718751788226268729 := by
  unfold tailWord_741015
  simp only [CollatzResearch.WordTrace]
  refine ⟨27027037410436685131528499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18018024940291123421018999 27027037410436685131528499)
  ·
    refine ⟨40540556115655027697292749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27027037410436685131528499 40540556115655027697292749)
    ·
      refine ⟨15202708543370635386484781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40540556115655027697292749 15202708543370635386484781)
      ·
        refine ⟨5701015703763988269931793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15202708543370635386484781 5701015703763988269931793)
        ·
          refine ⟨4275761777822991202448845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5701015703763988269931793 4275761777822991202448845)
          ·
            refine ⟨1603410666683621700918317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4275761777822991202448845 1603410666683621700918317)
            ·
              refine ⟨601279000006358137844369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1603410666683621700918317 601279000006358137844369)
              ·
                refine ⟨450959250004768603383277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601279000006358137844369 450959250004768603383277)
                ·
                  refine ⟨169109718751788226268729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 450959250004768603383277 169109718751788226268729)
                  ·
                    rfl

theorem cell21_741015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 3].length) (baseStart_741015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741015 prefixEnd_741015 := by exact prefixLift 741015
  have htrace : WordTrace (prefixWord ++ tailWord_741015) baseStart_741015 baseEnd_741015 := by
    simpa [prefixWord, tailWord_741015, baseEnd_741015] using wordTrace_append hprefix tailTrace_741015
  have hstable : (prefixWord ++ tailWord_741015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741015).length < 2 ^ (prefixWord ++ tailWord_741015).sum := by decide
  have hdescent : baseEnd_741015 < baseStart_741015 := by decide
  rcases family_descends (prefixWord ++ tailWord_741015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741040 : List Nat := [2, 1, 1, 1, 2, 1, 4, 4, 5]
def baseStart_741040 : Nat := 118140960795 + 741040 * 2 ^ 59
def prefixEnd_741040 : Nat := 4983230072969 + 3 ^ 40 * 741040 * 2
def baseEnd_741040 : Nat := 169115424092393738352011

theorem tailTrace_741040 : CollatzResearch.WordTrace tailWord_741040 prefixEnd_741040 169115424092393738352011 := by
  unfold tailWord_741040
  simp only [CollatzResearch.WordTrace]
  refine ⟨13513974617673057200594287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18018632823564076267459049 13513974617673057200594287)
  ·
    refine ⟨20270961926509585800891431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13513974617673057200594287 20270961926509585800891431)
    ·
      refine ⟨30406442889764378701337147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20270961926509585800891431 30406442889764378701337147)
      ·
        refine ⟨45609664334646568052005721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30406442889764378701337147 45609664334646568052005721)
        ·
          refine ⟨34207248250984926039004291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45609664334646568052005721 34207248250984926039004291)
          ·
            refine ⟨51310872376477389058506437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34207248250984926039004291 51310872376477389058506437)
            ·
              refine ⟨9620788570589510448469957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51310872376477389058506437 9620788570589510448469957)
              ·
                refine ⟨1803897856985533209088117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9620788570589510448469957 1803897856985533209088117)
                ·
                  refine ⟨169115424092393738352011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1803897856985533209088117 169115424092393738352011)
                  ·
                    rfl

theorem cell21_741040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_741040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741040 prefixEnd_741040 := by exact prefixLift 741040
  have htrace : WordTrace (prefixWord ++ tailWord_741040) baseStart_741040 baseEnd_741040 := by
    simpa [prefixWord, tailWord_741040, baseEnd_741040] using wordTrace_append hprefix tailTrace_741040
  have hstable : (prefixWord ++ tailWord_741040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741040).length < 2 ^ (prefixWord ++ tailWord_741040).sum := by decide
  have hdescent : baseEnd_741040 < baseStart_741040 := by decide
  rcases family_descends (prefixWord ++ tailWord_741040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741108 : List Nat := [2, 6, 1, 1, 1, 1, 1, 5, 3]
def baseStart_741108 : Nat := 118140960795 + 741108 * 2 ^ 59
def prefixEnd_741108 : Nat := 4983230072969 + 3 ^ 40 * 741108 * 2
def baseEnd_741108 : Nat := 169130942618840731218539

theorem tailTrace_741108 : CollatzResearch.WordTrace tailWord_741108 prefixEnd_741108 169130942618840731218539 := by
  unfold tailWord_741108
  simp only [CollatzResearch.WordTrace]
  refine ⟨13515214699549881007331989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18020286266066508009775985 13515214699549881007331989)
  ·
    refine ⟨633525689041400672218687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13515214699549881007331989 633525689041400672218687)
    ·
      refine ⟨950288533562101008328031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 633525689041400672218687 950288533562101008328031)
      ·
        refine ⟨1425432800343151512492047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 950288533562101008328031 1425432800343151512492047)
        ·
          refine ⟨2138149200514727268738071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1425432800343151512492047 2138149200514727268738071)
          ·
            refine ⟨3207223800772090903107107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2138149200514727268738071 3207223800772090903107107)
            ·
              refine ⟨4810835701158136354660661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3207223800772090903107107 4810835701158136354660661)
              ·
                refine ⟨451015846983575283249437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4810835701158136354660661 451015846983575283249437)
                ·
                  refine ⟨169130942618840731218539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451015846983575283249437 169130942618840731218539)
                  ·
                    rfl

theorem cell21_741108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_741108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741108 prefixEnd_741108 := by exact prefixLift 741108
  have htrace : WordTrace (prefixWord ++ tailWord_741108) baseStart_741108 baseEnd_741108 := by
    simpa [prefixWord, tailWord_741108, baseEnd_741108] using wordTrace_append hprefix tailTrace_741108
  have hstable : (prefixWord ++ tailWord_741108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741108).length < 2 ^ (prefixWord ++ tailWord_741108).sum := by decide
  have hdescent : baseEnd_741108 < baseStart_741108 := by decide
  rcases family_descends (prefixWord ++ tailWord_741108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741116 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 7]
def baseStart_741116 : Nat := 118140960795 + 741116 * 2 ^ 59
def prefixEnd_741116 : Nat := 4983230072969 + 3 ^ 40 * 741116 * 2
def baseEnd_741116 : Nat := 169132768327834495085189

theorem tailTrace_741116 : CollatzResearch.WordTrace tailWord_741116 prefixEnd_741116 169132768327834495085189 := by
  unfold tailWord_741116
  simp only [CollatzResearch.WordTrace]
  refine ⟨13515360591535389690477601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18020480788713852920636801 13515360591535389690477601)
  ·
    refine ⟨10136520443651542267858201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13515360591535389690477601 10136520443651542267858201)
    ·
      refine ⟨7602390332738656700893651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10136520443651542267858201 7602390332738656700893651)
      ·
        refine ⟨11403585499107985051340477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7602390332738656700893651 11403585499107985051340477)
        ·
          refine ⟨4276344562165494394252679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11403585499107985051340477 4276344562165494394252679)
          ·
            refine ⟨6414516843248241591379019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4276344562165494394252679 6414516843248241591379019)
            ·
              refine ⟨9621775264872362387068529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6414516843248241591379019 9621775264872362387068529)
              ·
                refine ⟨7216331448654271790301397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9621775264872362387068529 7216331448654271790301397)
                ·
                  refine ⟨169132768327834495085189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7216331448654271790301397 169132768327834495085189)
                  ·
                    rfl

theorem cell21_741116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_741116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741116 prefixEnd_741116 := by exact prefixLift 741116
  have htrace : WordTrace (prefixWord ++ tailWord_741116) baseStart_741116 baseEnd_741116 := by
    simpa [prefixWord, tailWord_741116, baseEnd_741116] using wordTrace_append hprefix tailTrace_741116
  have hstable : (prefixWord ++ tailWord_741116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741116).length < 2 ^ (prefixWord ++ tailWord_741116).sum := by decide
  have hdescent : baseEnd_741116 < baseStart_741116 := by decide
  rcases family_descends (prefixWord ++ tailWord_741116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741178 : List Nat := [3, 1, 1, 1, 5, 3, 7]
def baseStart_741178 : Nat := 118140960795 + 741178 * 2 ^ 59
def prefixEnd_741178 : Nat := 4983230072969 + 3 ^ 40 * 741178 * 2
def baseEnd_741178 : Nat := 18794101952504018339081

theorem tailTrace_741178 : CollatzResearch.WordTrace tailWord_741178 prefixEnd_741178 18794101952504018339081 := by
  unfold tailWord_741178
  simp only [CollatzResearch.WordTrace]
  refine ⟨6758245627211540992428047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18021988339230775979808125 6758245627211540992428047)
  ·
    refine ⟨10137368440817311488642071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6758245627211540992428047 10137368440817311488642071)
    ·
      refine ⟨15206052661225967232963107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10137368440817311488642071 15206052661225967232963107)
      ·
        refine ⟨22809078991838950849444661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15206052661225967232963107 22809078991838950849444661)
        ·
          refine ⟨2138351155484901642135437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22809078991838950849444661 2138351155484901642135437)
          ·
            refine ⟨801881683306838115800789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2138351155484901642135437 801881683306838115800789)
            ·
              refine ⟨18794101952504018339081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 801881683306838115800789 18794101952504018339081)
              ·
                rfl

theorem cell21_741178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 7].length) (baseStart_741178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741178 prefixEnd_741178 := by exact prefixLift 741178
  have htrace : WordTrace (prefixWord ++ tailWord_741178) baseStart_741178 baseEnd_741178 := by
    simpa [prefixWord, tailWord_741178, baseEnd_741178] using wordTrace_append hprefix tailTrace_741178
  have hstable : (prefixWord ++ tailWord_741178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741178).length < 2 ^ (prefixWord ++ tailWord_741178).sum := by decide
  have hdescent : baseEnd_741178 < baseStart_741178 := by decide
  rcases family_descends (prefixWord ++ tailWord_741178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741403 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 9]
def baseStart_741403 : Nat := 118140960795 + 741403 * 2 ^ 59
def prefixEnd_741403 : Nat := 4983230072969 + 3 ^ 40 * 741403 * 2
def baseEnd_741403 : Nat := 169198265637985773801269

theorem tailTrace_741403 : CollatzResearch.WordTrace tailWord_741403 prefixEnd_741403 169198265637985773801269 := by
  unfold tailWord_741403
  simp only [CollatzResearch.WordTrace]
  refine ⟨27041188933031027396652863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18027459288687351597768575 27041188933031027396652863)
  ·
    refine ⟨40561783399546541094979295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27041188933031027396652863 40561783399546541094979295)
    ·
      refine ⟨60842675099319811642468943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40561783399546541094979295 60842675099319811642468943)
      ·
        refine ⟨91264012648979717463703415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60842675099319811642468943 91264012648979717463703415)
        ·
          refine ⟨136896018973469576195555123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91264012648979717463703415 136896018973469576195555123)
          ·
            refine ⟨205344028460204364293332685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136896018973469576195555123 205344028460204364293332685)
            ·
              refine ⟨77004010672576636609999757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205344028460204364293332685 77004010672576636609999757)
              ·
                refine ⟨28876504002216238728749909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77004010672576636609999757 28876504002216238728749909)
                ·
                  refine ⟨169198265637985773801269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28876504002216238728749909 169198265637985773801269)
                  ·
                    rfl

theorem cell21_741403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 9].length) (baseStart_741403 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741403 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741403 prefixEnd_741403 := by exact prefixLift 741403
  have htrace : WordTrace (prefixWord ++ tailWord_741403) baseStart_741403 baseEnd_741403 := by
    simpa [prefixWord, tailWord_741403, baseEnd_741403] using wordTrace_append hprefix tailTrace_741403
  have hstable : (prefixWord ++ tailWord_741403).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741403).length < 2 ^ (prefixWord ++ tailWord_741403).sum := by decide
  have hdescent : baseEnd_741403 < baseStart_741403 := by decide
  rcases family_descends (prefixWord ++ tailWord_741403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741412 : List Nat := [2, 3, 1, 4, 2, 2, 2, 2, 3]
def baseStart_741412 : Nat := 118140960795 + 741412 * 2 ^ 59
def prefixEnd_741412 : Nat := 4983230072969 + 3 ^ 40 * 741412 * 2
def baseEnd_741412 : Nat := 169200319560603758151251

theorem tailTrace_741412 : CollatzResearch.WordTrace tailWord_741412 prefixEnd_741412 169200319560603758151251 := by
  unfold tailWord_741412
  simp only [CollatzResearch.WordTrace]
  refine ⟨13520758594999210966865245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18027678126665614622486993 13520758594999210966865245)
  ·
    refine ⟨5070284473124704112574467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13520758594999210966865245 5070284473124704112574467)
    ·
      refine ⟨7605426709687056168861701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5070284473124704112574467 7605426709687056168861701)
      ·
        refine ⟨1426017508066323031661569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7605426709687056168861701 1426017508066323031661569)
        ·
          refine ⟨1069513131049742273746177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1426017508066323031661569 1069513131049742273746177)
          ·
            refine ⟨802134848287306705309633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1069513131049742273746177 802134848287306705309633)
            ·
              refine ⟨601601136215480028982225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 802134848287306705309633 601601136215480028982225)
              ·
                refine ⟨451200852161610021736669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601601136215480028982225 451200852161610021736669)
                ·
                  refine ⟨169200319560603758151251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451200852161610021736669 169200319560603758151251)
                  ·
                    rfl

theorem cell21_741412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_741412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741412 prefixEnd_741412 := by exact prefixLift 741412
  have htrace : WordTrace (prefixWord ++ tailWord_741412) baseStart_741412 baseEnd_741412 := by
    simpa [prefixWord, tailWord_741412, baseEnd_741412] using wordTrace_append hprefix tailTrace_741412
  have hstable : (prefixWord ++ tailWord_741412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741412).length < 2 ^ (prefixWord ++ tailWord_741412).sum := by decide
  have hdescent : baseEnd_741412 < baseStart_741412 := by decide
  rcases family_descends (prefixWord ++ tailWord_741412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741434 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 8]
def baseStart_741434 : Nat := 118140960795 + 741434 * 2 ^ 59
def prefixEnd_741434 : Nat := 4983230072969 + 3 ^ 40 * 741434 * 2
def baseEnd_741434 : Nat := 169205340260336608784539

theorem tailTrace_741434 : CollatzResearch.WordTrace tailWord_741434 prefixEnd_741434 169205340260336608784539 := by
  unfold tailWord_741434
  simp only [CollatzResearch.WordTrace]
  refine ⟨6760579898979679922757839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18028213063945813127354237 6760579898979679922757839)
  ·
    refine ⟨10140869848469519884136759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6760579898979679922757839 10140869848469519884136759)
    ·
      refine ⟨15211304772704279826205139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10140869848469519884136759 15211304772704279826205139)
      ·
        refine ⟨22816957159056419739307709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15211304772704279826205139 22816957159056419739307709)
        ·
          refine ⟨8556358934646157402240391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22816957159056419739307709 8556358934646157402240391)
          ·
            refine ⟨12834538401969236103360587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8556358934646157402240391 12834538401969236103360587)
            ·
              refine ⟨19251807602953854155040881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12834538401969236103360587 19251807602953854155040881)
              ·
                refine ⟨14438855702215390616280661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19251807602953854155040881 14438855702215390616280661)
                ·
                  refine ⟨169205340260336608784539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14438855702215390616280661 169205340260336608784539)
                  ·
                    rfl

theorem cell21_741434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_741434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741434 prefixEnd_741434 := by exact prefixLift 741434
  have htrace : WordTrace (prefixWord ++ tailWord_741434) baseStart_741434 baseEnd_741434 := by
    simpa [prefixWord, tailWord_741434, baseEnd_741434] using wordTrace_append hprefix tailTrace_741434
  have hstable : (prefixWord ++ tailWord_741434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741434).length < 2 ^ (prefixWord ++ tailWord_741434).sum := by decide
  have hdescent : baseEnd_741434 < baseStart_741434 := by decide
  rcases family_descends (prefixWord ++ tailWord_741434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741454 : List Nat := [4, 1, 1, 1, 1, 5, 2, 3, 3]
def baseStart_741454 : Nat := 118140960795 + 741454 * 2 ^ 59
def prefixEnd_741454 : Nat := 4983230072969 + 3 ^ 40 * 741454 * 2
def baseEnd_741454 : Nat := 169209904532821018451165

theorem tailTrace_741454 : CollatzResearch.WordTrace tailWord_741454 prefixEnd_741454 169209904532821018451165 := by
  unfold tailWord_741454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3380381131980782888344927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18028699370564175404506277 3380381131980782888344927)
  ·
    refine ⟨5070571697971174332517391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3380381131980782888344927 5070571697971174332517391)
    ·
      refine ⟨7605857546956761498776087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5070571697971174332517391 7605857546956761498776087)
      ·
        refine ⟨11408786320435142248164131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7605857546956761498776087 11408786320435142248164131)
        ·
          refine ⟨17113179480652713372246197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11408786320435142248164131 17113179480652713372246197)
          ·
            refine ⟨1604360576311191878648081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17113179480652713372246197 1604360576311191878648081)
            ·
              refine ⟨1203270432233393908986061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1604360576311191878648081 1203270432233393908986061)
              ·
                refine ⟨451226412087522715869773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1203270432233393908986061 451226412087522715869773)
                ·
                  refine ⟨169209904532821018451165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451226412087522715869773 169209904532821018451165)
                  ·
                    rfl

theorem cell21_741454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_741454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741454 prefixEnd_741454 := by exact prefixLift 741454
  have htrace : WordTrace (prefixWord ++ tailWord_741454) baseStart_741454 baseEnd_741454 := by
    simpa [prefixWord, tailWord_741454, baseEnd_741454] using wordTrace_append hprefix tailTrace_741454
  have hstable : (prefixWord ++ tailWord_741454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741454).length < 2 ^ (prefixWord ++ tailWord_741454).sum := by decide
  have hdescent : baseEnd_741454 < baseStart_741454 := by decide
  rcases family_descends (prefixWord ++ tailWord_741454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741468 : List Nat := [2, 2, 4, 1, 1, 2, 3, 2, 4]
def baseStart_741468 : Nat := 118140960795 + 741468 * 2 ^ 59
def prefixEnd_741468 : Nat := 4983230072969 + 3 ^ 40 * 741468 * 2
def baseEnd_741468 : Nat := 169213099523560105217803

theorem tailTrace_741468 : CollatzResearch.WordTrace tailWord_741468 prefixEnd_741468 169213099523560105217803 := by
  unfold tailWord_741468
  simp only [CollatzResearch.WordTrace]
  refine ⟨13521779838897771748884529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18029039785197028998512705 13521779838897771748884529)
  ·
    refine ⟨10141334879173328811663397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13521779838897771748884529 10141334879173328811663397)
    ·
      refine ⟨1901500289844999152186887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10141334879173328811663397 1901500289844999152186887)
      ·
        refine ⟨2852250434767498728280331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1901500289844999152186887 2852250434767498728280331)
        ·
          refine ⟨4278375652151248092420497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2852250434767498728280331 4278375652151248092420497)
          ·
            refine ⟨3208781739113436069315373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4278375652151248092420497 3208781739113436069315373)
            ·
              refine ⟨1203293152167538525993265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3208781739113436069315373 1203293152167538525993265)
              ·
                refine ⟨902469864125653894494949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1203293152167538525993265 902469864125653894494949)
                ·
                  refine ⟨169213099523560105217803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 902469864125653894494949 169213099523560105217803)
                  ·
                    rfl

theorem cell21_741468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_741468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741468 prefixEnd_741468 := by exact prefixLift 741468
  have htrace : WordTrace (prefixWord ++ tailWord_741468) baseStart_741468 baseEnd_741468 := by
    simpa [prefixWord, tailWord_741468, baseEnd_741468] using wordTrace_append hprefix tailTrace_741468
  have hstable : (prefixWord ++ tailWord_741468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741468).length < 2 ^ (prefixWord ++ tailWord_741468).sum := by decide
  have hdescent : baseEnd_741468 < baseStart_741468 := by decide
  rcases family_descends (prefixWord ++ tailWord_741468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741530 : List Nat := [3, 1, 1, 5, 2, 2, 1, 1, 5]
def baseStart_741530 : Nat := 118140960795 + 741530 * 2 ^ 59
def prefixEnd_741530 : Nat := 4983230072969 + 3 ^ 40 * 741530 * 2
def baseEnd_741530 : Nat := 169227248768261775184343

theorem tailTrace_741530 : CollatzResearch.WordTrace tailWord_741530 prefixEnd_741530 169227248768261775184343 := by
  unfold tailWord_741530
  simp only [CollatzResearch.WordTrace]
  refine ⟨6761455250892732021631511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18030547335713952057684029 6761455250892732021631511)
  ·
    refine ⟨10142182876339098032447267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6761455250892732021631511 10142182876339098032447267)
    ·
      refine ⟨15213274314508647048670901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10142182876339098032447267 15213274314508647048670901)
      ·
        refine ⟨1426244466985185660812897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15213274314508647048670901 1426244466985185660812897)
        ·
          refine ⟨1069683350238889245609673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1426244466985185660812897 1069683350238889245609673)
          ·
            refine ⟨802262512679166934207255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1069683350238889245609673 802262512679166934207255)
            ·
              refine ⟨1203393769018750401310883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802262512679166934207255 1203393769018750401310883)
              ·
                refine ⟨1805090653528125601966325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1203393769018750401310883 1805090653528125601966325)
                ·
                  refine ⟨169227248768261775184343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1805090653528125601966325 169227248768261775184343)
                  ·
                    rfl

theorem cell21_741530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_741530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741530 prefixEnd_741530 := by exact prefixLift 741530
  have htrace : WordTrace (prefixWord ++ tailWord_741530) baseStart_741530 baseEnd_741530 := by
    simpa [prefixWord, tailWord_741530, baseEnd_741530] using wordTrace_append hprefix tailTrace_741530
  have hstable : (prefixWord ++ tailWord_741530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741530).length < 2 ^ (prefixWord ++ tailWord_741530).sum := by decide
  have hdescent : baseEnd_741530 < baseStart_741530 := by decide
  rcases family_descends (prefixWord ++ tailWord_741530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741541 : List Nat := [1, 3, 1, 2, 1, 3, 4, 6]
def baseStart_741541 : Nat := 118140960795 + 741541 * 2 ^ 59
def prefixEnd_741541 : Nat := 4983230072969 + 3 ^ 40 * 741541 * 2
def baseEnd_741541 : Nat := 56409919706042733500329

theorem tailTrace_741541 : CollatzResearch.WordTrace tailWord_741541 prefixEnd_741541 56409919706042733500329 := by
  unfold tailWord_741541
  simp only [CollatzResearch.WordTrace]
  refine ⟨27046222206531076965176477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18030814804354051310117651 27046222206531076965176477)
  ·
    refine ⟨10142333327449153861941179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27046222206531076965176477 10142333327449153861941179)
    ·
      refine ⟨15213499991173730792911769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10142333327449153861941179 15213499991173730792911769)
      ·
        refine ⟨11410124993380298094683827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15213499991173730792911769 11410124993380298094683827)
        ·
          refine ⟨17115187490070447142025741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11410124993380298094683827 17115187490070447142025741)
          ·
            refine ⟨6418195308776417678259653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17115187490070447142025741 6418195308776417678259653)
            ·
              refine ⟨1203411620395578314673685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6418195308776417678259653 1203411620395578314673685)
              ·
                refine ⟨56409919706042733500329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1203411620395578314673685 56409919706042733500329)
                ·
                  rfl

theorem cell21_741541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 6].length) (baseStart_741541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741541 prefixEnd_741541 := by exact prefixLift 741541
  have htrace : WordTrace (prefixWord ++ tailWord_741541) baseStart_741541 baseEnd_741541 := by
    simpa [prefixWord, tailWord_741541, baseEnd_741541] using wordTrace_append hprefix tailTrace_741541
  have hstable : (prefixWord ++ tailWord_741541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741541).length < 2 ^ (prefixWord ++ tailWord_741541).sum := by decide
  have hdescent : baseEnd_741541 < baseStart_741541 := by decide
  rcases family_descends (prefixWord ++ tailWord_741541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741555 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 7]
def baseStart_741555 : Nat := 118140960795 + 741555 * 2 ^ 59
def prefixEnd_741555 : Nat := 4983230072969 + 3 ^ 40 * 741555 * 2
def baseEnd_741555 : Nat := 169232954108867287267625

theorem tailTrace_741555 : CollatzResearch.WordTrace tailWord_741555 prefixEnd_741555 169232954108867287267625 := by
  unfold tailWord_741555
  simp only [CollatzResearch.WordTrace]
  refine ⟨27046732828480357356186119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18031155218986904904124079 27046732828480357356186119)
  ·
    refine ⟨40570099242720536034279179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27046732828480357356186119 40570099242720536034279179)
    ·
      refine ⟨60855148864080804051418769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40570099242720536034279179 60855148864080804051418769)
      ·
        refine ⟨45641361648060603038564077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60855148864080804051418769 45641361648060603038564077)
        ·
          refine ⟨17115510618022726139461529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45641361648060603038564077 17115510618022726139461529)
          ·
            refine ⟨12836632963517044604596147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17115510618022726139461529 12836632963517044604596147)
            ·
              refine ⟨19254949445275566906894221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12836632963517044604596147 19254949445275566906894221)
              ·
                refine ⟨7220606041978337590085333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19254949445275566906894221 7220606041978337590085333)
                ·
                  refine ⟨169232954108867287267625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7220606041978337590085333 169232954108867287267625)
                  ·
                    rfl

theorem cell21_741555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 7].length) (baseStart_741555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741555 prefixEnd_741555 := by exact prefixLift 741555
  have htrace : WordTrace (prefixWord ++ tailWord_741555) baseStart_741555 baseEnd_741555 := by
    simpa [prefixWord, tailWord_741555, baseEnd_741555] using wordTrace_append hprefix tailTrace_741555
  have hstable : (prefixWord ++ tailWord_741555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741555).length < 2 ^ (prefixWord ++ tailWord_741555).sum := by decide
  have hdescent : baseEnd_741555 < baseStart_741555 := by decide
  rcases family_descends (prefixWord ++ tailWord_741555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741631 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 7]
def baseStart_741631 : Nat := 118140960795 + 741631 * 2 ^ 59
def prefixEnd_741631 : Nat := 4983230072969 + 3 ^ 40 * 741631 * 2
def baseEnd_741631 : Nat := 169250298344308044000803

theorem tailTrace_741631 : CollatzResearch.WordTrace tailWord_741631 prefixEnd_741631 169250298344308044000803 := by
  unfold tailWord_741631
  simp only [CollatzResearch.WordTrace]
  refine ⟨27049504776205022335952747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18033003184136681557301831 27049504776205022335952747)
  ·
    refine ⟨40574257164307533503929121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27049504776205022335952747 40574257164307533503929121)
    ·
      refine ⟨30430692873230650127946841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40574257164307533503929121 30430692873230650127946841)
      ·
        refine ⟨22823019654922987595960131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30430692873230650127946841 22823019654922987595960131)
        ·
          refine ⟨34234529482384481393940197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22823019654922987595960131 34234529482384481393940197)
          ·
            refine ⟨6418974277947090261363787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34234529482384481393940197 6418974277947090261363787)
            ·
              refine ⟨9628461416920635392045681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6418974277947090261363787 9628461416920635392045681)
              ·
                refine ⟨7221346062690476544034261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9628461416920635392045681 7221346062690476544034261)
                ·
                  refine ⟨169250298344308044000803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7221346062690476544034261 169250298344308044000803)
                  ·
                    rfl

theorem cell21_741631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 7].length) (baseStart_741631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741631 prefixEnd_741631 := by exact prefixLift 741631
  have htrace : WordTrace (prefixWord ++ tailWord_741631) baseStart_741631 baseEnd_741631 := by
    simpa [prefixWord, tailWord_741631, baseEnd_741631] using wordTrace_append hprefix tailTrace_741631
  have hstable : (prefixWord ++ tailWord_741631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741631).length < 2 ^ (prefixWord ++ tailWord_741631).sum := by decide
  have hdescent : baseEnd_741631 < baseStart_741631 := by decide
  rcases family_descends (prefixWord ++ tailWord_741631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741634 : List Nat := [3, 4, 1, 1, 2, 2, 8]
def baseStart_741634 : Nat := 118140960795 + 741634 * 2 ^ 59
def prefixEnd_741634 : Nat := 4983230072969 + 3 ^ 40 * 741634 * 2
def baseEnd_741634 : Nat := 18805664776131189494533

theorem tailTrace_741634 : CollatzResearch.WordTrace tailWord_741634 prefixEnd_741634 18805664776131189494533 := by
  unfold tailWord_741634
  simp only [CollatzResearch.WordTrace]
  refine ⟨6762403548798538462077989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18033076130129435898874637 6762403548798538462077989)
  ·
    refine ⟨1267950665399725961639623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6762403548798538462077989 1267950665399725961639623)
    ·
      refine ⟨1901925998099588942459435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1267950665399725961639623 1901925998099588942459435)
      ·
        refine ⟨2852888997149383413689153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1901925998099588942459435 2852888997149383413689153)
        ·
          refine ⟨2139666747862037560266865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2852888997149383413689153 2139666747862037560266865)
          ·
            refine ⟨1604750060896528170200149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2139666747862037560266865 1604750060896528170200149)
            ·
              refine ⟨18805664776131189494533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1604750060896528170200149 18805664776131189494533)
              ·
                rfl

theorem cell21_741634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 8].length) (baseStart_741634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741634 prefixEnd_741634 := by exact prefixLift 741634
  have htrace : WordTrace (prefixWord ++ tailWord_741634) baseStart_741634 baseEnd_741634 := by
    simpa [prefixWord, tailWord_741634, baseEnd_741634] using wordTrace_append hprefix tailTrace_741634
  have hstable : (prefixWord ++ tailWord_741634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741634).length < 2 ^ (prefixWord ++ tailWord_741634).sum := by decide
  have hdescent : baseEnd_741634 < baseStart_741634 := by decide
  rcases family_descends (prefixWord ++ tailWord_741634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741707 : List Nat := [1, 1, 1, 1, 3, 1, 1, 7, 5]
def baseStart_741707 : Nat := 118140960795 + 741707 * 2 ^ 59
def prefixEnd_741707 : Nat := 4983230072969 + 3 ^ 40 * 741707 * 2
def baseEnd_741707 : Nat := 169267642579748800733981

theorem tailTrace_741707 : CollatzResearch.WordTrace tailWord_741707 prefixEnd_741707 169267642579748800733981 := by
  unfold tailWord_741707
  simp only [CollatzResearch.WordTrace]
  refine ⟨27052276723929687315719375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18034851149286458210479583 27052276723929687315719375)
  ·
    refine ⟨40578415085894530973579063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27052276723929687315719375 40578415085894530973579063)
    ·
      refine ⟨60867622628841796460368595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40578415085894530973579063 60867622628841796460368595)
      ·
        refine ⟨91301433943262694690552893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60867622628841796460368595 91301433943262694690552893)
        ·
          refine ⟨34238037728723510508957335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91301433943262694690552893 34238037728723510508957335)
          ·
            refine ⟨51357056593085265763436003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34238037728723510508957335 51357056593085265763436003)
            ·
              refine ⟨77035584889627898645154005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51357056593085265763436003 77035584889627898645154005)
              ·
                refine ⟨1805521520850653874495797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 77035584889627898645154005 1805521520850653874495797)
                ·
                  refine ⟨169267642579748800733981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1805521520850653874495797 169267642579748800733981)
                  ·
                    rfl

theorem cell21_741707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 5].length) (baseStart_741707 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741707 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741707 prefixEnd_741707 := by exact prefixLift 741707
  have htrace : WordTrace (prefixWord ++ tailWord_741707) baseStart_741707 baseEnd_741707 := by
    simpa [prefixWord, tailWord_741707, baseEnd_741707] using wordTrace_append hprefix tailTrace_741707
  have hstable : (prefixWord ++ tailWord_741707).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741707).length < 2 ^ (prefixWord ++ tailWord_741707).sum := by decide
  have hdescent : baseEnd_741707 < baseStart_741707 := by decide
  rcases family_descends (prefixWord ++ tailWord_741707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741741 : List Nat := [1, 5, 1, 1, 1, 2, 2, 5, 3]
def baseStart_741741 : Nat := 118140960795 + 741741 * 2 ^ 59
def prefixEnd_741741 : Nat := 4983230072969 + 3 ^ 40 * 741741 * 2
def baseEnd_741741 : Nat := 169275401842972297167245

theorem tailTrace_741741 : CollatzResearch.WordTrace tailWord_741741 prefixEnd_741741 169275401842972297167245 := by
  unfold tailWord_741741
  simp only [CollatzResearch.WordTrace]
  refine ⟨27053516805806511122457077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18035677870537674081638051 27053516805806511122457077)
  ·
    refine ⟨2536267200544360417730351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27053516805806511122457077 2536267200544360417730351)
    ·
      refine ⟨3804400800816540626595527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2536267200544360417730351 3804400800816540626595527)
      ·
        refine ⟨5706601201224810939893291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3804400800816540626595527 5706601201224810939893291)
        ·
          refine ⟨8559901801837216409839937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5706601201224810939893291 8559901801837216409839937)
          ·
            refine ⟨6419926351377912307379953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8559901801837216409839937 6419926351377912307379953)
            ·
              refine ⟨4814944763533434230534965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6419926351377912307379953 4814944763533434230534965)
              ·
                refine ⟨451401071581259459112653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4814944763533434230534965 451401071581259459112653)
                ·
                  refine ⟨169275401842972297167245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451401071581259459112653 169275401842972297167245)
                  ·
                    rfl

theorem cell21_741741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_741741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741741 prefixEnd_741741 := by exact prefixLift 741741
  have htrace : WordTrace (prefixWord ++ tailWord_741741) baseStart_741741 baseEnd_741741 := by
    simpa [prefixWord, tailWord_741741, baseEnd_741741] using wordTrace_append hprefix tailTrace_741741
  have hstable : (prefixWord ++ tailWord_741741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741741).length < 2 ^ (prefixWord ++ tailWord_741741).sum := by decide
  have hdescent : baseEnd_741741 < baseStart_741741 := by decide
  rcases family_descends (prefixWord ++ tailWord_741741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741755 : List Nat := [1, 1, 1, 1, 1, 8, 2, 2, 4]
def baseStart_741755 : Nat := 118140960795 + 741755 * 2 ^ 59
def prefixEnd_741755 : Nat := 4983230072969 + 3 ^ 40 * 741755 * 2
def baseEnd_741755 : Nat := 169278596833711383933883

theorem tailTrace_741755 : CollatzResearch.WordTrace tailWord_741755 prefixEnd_741755 169278596833711383933883 := by
  unfold tailWord_741755
  simp only [CollatzResearch.WordTrace]
  refine ⟨27054027427755791513466719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18036018285170527675644479 27054027427755791513466719)
  ·
    refine ⟨40581041141633687270200079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27054027427755791513466719 40581041141633687270200079)
    ·
      refine ⟨60871561712450530905300119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40581041141633687270200079 60871561712450530905300119)
      ·
        refine ⟨91307342568675796357950179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60871561712450530905300119 91307342568675796357950179)
        ·
          refine ⟨136961013853013694536925269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91307342568675796357950179 136961013853013694536925269)
          ·
            refine ⟨1605011881090004232854593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 136961013853013694536925269 1605011881090004232854593)
            ·
              refine ⟨1203758910817503174640945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1605011881090004232854593 1203758910817503174640945)
              ·
                refine ⟨902819183113127380980709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1203758910817503174640945 902819183113127380980709)
                ·
                  refine ⟨169278596833711383933883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 902819183113127380980709 169278596833711383933883)
                  ·
                    rfl

theorem cell21_741755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 4].length) (baseStart_741755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741755 prefixEnd_741755 := by exact prefixLift 741755
  have htrace : WordTrace (prefixWord ++ tailWord_741755) baseStart_741755 baseEnd_741755 := by
    simpa [prefixWord, tailWord_741755, baseEnd_741755] using wordTrace_append hprefix tailTrace_741755
  have hstable : (prefixWord ++ tailWord_741755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741755).length < 2 ^ (prefixWord ++ tailWord_741755).sum := by decide
  have hdescent : baseEnd_741755 < baseStart_741755 := by decide
  rcases family_descends (prefixWord ++ tailWord_741755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741769 : List Nat := [1, 2, 1, 1, 6, 1, 3, 6]
def baseStart_741769 : Nat := 118140960795 + 741769 * 2 ^ 59
def prefixEnd_741769 : Nat := 4983230072969 + 3 ^ 40 * 741769 * 2
def baseEnd_741769 : Nat := 56427263941483490233507

theorem tailTrace_741769 : CollatzResearch.WordTrace tailWord_741769 prefixEnd_741769 56427263941483490233507 := by
  unfold tailWord_741769
  simp only [CollatzResearch.WordTrace]
  refine ⟨27054538049705071904476361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18036358699803381269650907 27054538049705071904476361)
  ·
    refine ⟨20290903537278803928357271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27054538049705071904476361 20290903537278803928357271)
    ·
      refine ⟨30436355305918205892535907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20290903537278803928357271 30436355305918205892535907)
      ·
        refine ⟨45654532958877308838803861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30436355305918205892535907 45654532958877308838803861)
        ·
          refine ⟨2140056232447373851818931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45654532958877308838803861 2140056232447373851818931)
          ·
            refine ⟨3210084348671060777728397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2140056232447373851818931 3210084348671060777728397)
            ·
              refine ⟨1203781630751647791648149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3210084348671060777728397 1203781630751647791648149)
              ·
                refine ⟨56427263941483490233507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1203781630751647791648149 56427263941483490233507)
                ·
                  rfl

theorem cell21_741769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 6].length) (baseStart_741769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741769 prefixEnd_741769 := by exact prefixLift 741769
  have htrace : WordTrace (prefixWord ++ tailWord_741769) baseStart_741769 baseEnd_741769 := by
    simpa [prefixWord, tailWord_741769, baseEnd_741769] using wordTrace_append hprefix tailTrace_741769
  have hstable : (prefixWord ++ tailWord_741769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741769).length < 2 ^ (prefixWord ++ tailWord_741769).sum := by decide
  have hdescent : baseEnd_741769 < baseStart_741769 := by decide
  rcases family_descends (prefixWord ++ tailWord_741769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741783 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 7]
def baseStart_741783 : Nat := 118140960795 + 741783 * 2 ^ 59
def prefixEnd_741783 : Nat := 4983230072969 + 3 ^ 40 * 741783 * 2
def baseEnd_741783 : Nat := 169284986815189557467159

theorem tailTrace_741783 : CollatzResearch.WordTrace tailWord_741783 prefixEnd_741783 169284986815189557467159 := by
  unfold tailWord_741783
  simp only [CollatzResearch.WordTrace]
  refine ⟨27055048671654352295486003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18036699114436234863657335 27055048671654352295486003)
  ·
    refine ⟨40582573007481528443229005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27055048671654352295486003 40582573007481528443229005)
    ·
      refine ⟨15218464877805573166210877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40582573007481528443229005 15218464877805573166210877)
      ·
        refine ⟨5706924329177089937329079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15218464877805573166210877 5706924329177089937329079)
        ·
          refine ⟨8560386493765634905993619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5706924329177089937329079 8560386493765634905993619)
          ·
            refine ⟨12840579740648452358990429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8560386493765634905993619 12840579740648452358990429)
            ·
              refine ⟨4815217402743169634621411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12840579740648452358990429 4815217402743169634621411)
              ·
                refine ⟨7222826104114754451932117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4815217402743169634621411 7222826104114754451932117)
                ·
                  refine ⟨169284986815189557467159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7222826104114754451932117 169284986815189557467159)
                  ·
                    rfl

theorem cell21_741783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 7].length) (baseStart_741783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741783 prefixEnd_741783 := by exact prefixLift 741783
  have htrace : WordTrace (prefixWord ++ tailWord_741783) baseStart_741783 baseEnd_741783 := by
    simpa [prefixWord, tailWord_741783, baseEnd_741783] using wordTrace_append hprefix tailTrace_741783
  have hstable : (prefixWord ++ tailWord_741783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741783).length < 2 ^ (prefixWord ++ tailWord_741783).sum := by decide
  have hdescent : baseEnd_741783 < baseStart_741783 := by decide
  rcases family_descends (prefixWord ++ tailWord_741783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741786 : List Nat := [3, 1, 1, 4, 1, 3, 3, 5]
def baseStart_741786 : Nat := 118140960795 + 741786 * 2 ^ 59
def prefixEnd_741786 : Nat := 4983230072969 + 3 ^ 40 * 741786 * 2
def baseEnd_741786 : Nat := 56428557152020739639051

theorem tailTrace_741786 : CollatzResearch.WordTrace tailWord_741786 prefixEnd_741786 56428557152020739639051 := by
  unfold tailWord_741786
  simp only [CollatzResearch.WordTrace]
  refine ⟨6763789522660870951961303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18036772060428989205230141 6763789522660870951961303)
  ·
    refine ⟨10145684283991306427941955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6763789522660870951961303 10145684283991306427941955)
    ·
      refine ⟨15218526425986959641912933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10145684283991306427941955 15218526425986959641912933)
      ·
        refine ⟨2853473704872554932858675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15218526425986959641912933 2853473704872554932858675)
        ·
          refine ⟨4280210557308832399288013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2853473704872554932858675 4280210557308832399288013)
          ·
            refine ⟨1605078958990812149733005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4280210557308832399288013 1605078958990812149733005)
            ·
              refine ⟨601904609621554556149877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1605078958990812149733005 601904609621554556149877)
              ·
                refine ⟨56428557152020739639051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 601904609621554556149877 56428557152020739639051)
                ·
                  rfl

theorem cell21_741786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_741786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741786 prefixEnd_741786 := by exact prefixLift 741786
  have htrace : WordTrace (prefixWord ++ tailWord_741786) baseStart_741786 baseEnd_741786 := by
    simpa [prefixWord, tailWord_741786, baseEnd_741786] using wordTrace_append hprefix tailTrace_741786
  have hstable : (prefixWord ++ tailWord_741786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741786).length < 2 ^ (prefixWord ++ tailWord_741786).sum := by decide
  have hdescent : baseEnd_741786 < baseStart_741786 := by decide
  rcases family_descends (prefixWord ++ tailWord_741786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741817 : List Nat := [1, 2, 1, 4, 3, 1, 2, 4, 3]
def baseStart_741817 : Nat := 118140960795 + 741817 * 2 ^ 59
def prefixEnd_741817 : Nat := 4983230072969 + 3 ^ 40 * 741817 * 2
def baseEnd_741817 : Nat := 169292746078413053900423

theorem tailTrace_741817 : CollatzResearch.WordTrace tailWord_741817 prefixEnd_741817 169292746078413053900423 := by
  unfold tailWord_741817
  simp only [CollatzResearch.WordTrace]
  refine ⟨27056288753531176102223705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18037525835687450734815803 27056288753531176102223705)
  ·
    refine ⟨20292216565148382076667779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27056288753531176102223705 20292216565148382076667779)
    ·
      refine ⟨30438324847722573115001669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20292216565148382076667779 30438324847722573115001669)
      ·
        refine ⟨5707185908947982459062813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30438324847722573115001669 5707185908947982459062813)
        ·
          refine ⟨2140194715855493422148555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5707185908947982459062813 2140194715855493422148555)
          ·
            refine ⟨3210292073783240133222833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2140194715855493422148555 3210292073783240133222833)
            ·
              refine ⟨2407719055337430099917125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3210292073783240133222833 2407719055337430099917125)
              ·
                refine ⟨451447322875768143734461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2407719055337430099917125 451447322875768143734461)
                ·
                  refine ⟨169292746078413053900423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451447322875768143734461 169292746078413053900423)
                  ·
                    rfl

theorem cell21_741817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 3].length) (baseStart_741817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741817 prefixEnd_741817 := by exact prefixLift 741817
  have htrace : WordTrace (prefixWord ++ tailWord_741817) baseStart_741817 baseEnd_741817 := by
    simpa [prefixWord, tailWord_741817, baseEnd_741817] using wordTrace_append hprefix tailTrace_741817
  have hstable : (prefixWord ++ tailWord_741817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741817).length < 2 ^ (prefixWord ++ tailWord_741817).sum := by decide
  have hdescent : baseEnd_741817 < baseStart_741817 := by decide
  rcases family_descends (prefixWord ++ tailWord_741817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741845 : List Nat := [1, 3, 2, 3, 1, 3, 1, 7]
def baseStart_741845 : Nat := 118140960795 + 741845 * 2 ^ 59
def prefixEnd_741845 : Nat := 4983230072969 + 3 ^ 40 * 741845 * 2
def baseEnd_741845 : Nat := 56433045353297075811233

theorem tailTrace_741845 : CollatzResearch.WordTrace tailWord_741845 prefixEnd_741845 56433045353297075811233 := by
  unfold tailWord_741845
  simp only [CollatzResearch.WordTrace]
  refine ⟨27057309997429736884242989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18038206664953157922828659 27057309997429736884242989)
  ·
    refine ⟨10146491249036151331591121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27057309997429736884242989 10146491249036151331591121)
    ·
      refine ⟨7609868436777113498693341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10146491249036151331591121 7609868436777113498693341)
      ·
        refine ⟨2853700663791417562010003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7609868436777113498693341 2853700663791417562010003)
        ·
          refine ⟨4280550995687126343015005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2853700663791417562010003 4280550995687126343015005)
          ·
            refine ⟨1605206623382672378630627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4280550995687126343015005 1605206623382672378630627)
            ·
              refine ⟨2407809935074008567945941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1605206623382672378630627 2407809935074008567945941)
              ·
                refine ⟨56433045353297075811233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2407809935074008567945941 56433045353297075811233)
                ·
                  rfl

theorem cell21_741845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 7].length) (baseStart_741845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741845 prefixEnd_741845 := by exact prefixLift 741845
  have htrace : WordTrace (prefixWord ++ tailWord_741845) baseStart_741845 baseEnd_741845 := by
    simpa [prefixWord, tailWord_741845, baseEnd_741845] using wordTrace_append hprefix tailTrace_741845
  have hstable : (prefixWord ++ tailWord_741845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741845).length < 2 ^ (prefixWord ++ tailWord_741845).sum := by decide
  have hdescent : baseEnd_741845 < baseStart_741845 := by decide
  rcases family_descends (prefixWord ++ tailWord_741845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741927 : List Nat := [1, 1, 7, 2, 1, 1, 1, 4, 3]
def baseStart_741927 : Nat := 118140960795 + 741927 * 2 ^ 59
def prefixEnd_741927 : Nat := 4983230072969 + 3 ^ 40 * 741927 * 2
def baseEnd_741927 : Nat := 169317849577077307066865

theorem tailTrace_741927 : CollatzResearch.WordTrace tailWord_741927 prefixEnd_741927 169317849577077307066865 := by
  unfold tailWord_741927
  simp only [CollatzResearch.WordTrace]
  refine ⟨27060300783132664888728035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18040200522088443259152023 27060300783132664888728035)
  ·
    refine ⟨40590451174698997333092053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27060300783132664888728035 40590451174698997333092053)
    ·
      refine ⟨951338699407007749994345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 40590451174698997333092053 951338699407007749994345)
      ·
        refine ⟨713504024555255812495759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 951338699407007749994345 713504024555255812495759)
        ·
          refine ⟨1070256036832883718743639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713504024555255812495759 1070256036832883718743639)
          ·
            refine ⟨1605384055249325578115459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070256036832883718743639 1605384055249325578115459)
            ·
              refine ⟨2408076082873988367173189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1605384055249325578115459 2408076082873988367173189)
              ·
                refine ⟨451514265538872818844973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2408076082873988367173189 451514265538872818844973)
                ·
                  refine ⟨169317849577077307066865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451514265538872818844973 169317849577077307066865)
                  ·
                    rfl

theorem cell21_741927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 3].length) (baseStart_741927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741927 prefixEnd_741927 := by exact prefixLift 741927
  have htrace : WordTrace (prefixWord ++ tailWord_741927) baseStart_741927 baseEnd_741927 := by
    simpa [prefixWord, tailWord_741927, baseEnd_741927] using wordTrace_append hprefix tailTrace_741927
  have hstable : (prefixWord ++ tailWord_741927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741927).length < 2 ^ (prefixWord ++ tailWord_741927).sum := by decide
  have hdescent : baseEnd_741927 < baseStart_741927 := by decide
  rcases family_descends (prefixWord ++ tailWord_741927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741969 : List Nat := [1, 2, 2, 1, 3, 4, 2, 3, 3]
def baseStart_741969 : Nat := 118140960795 + 741969 * 2 ^ 59
def prefixEnd_741969 : Nat := 4983230072969 + 3 ^ 40 * 741969 * 2
def baseEnd_741969 : Nat := 169327434549294567366779

theorem tailTrace_741969 : CollatzResearch.WordTrace tailWord_741969 prefixEnd_741969 169327434549294567366779 := by
  unfold tailWord_741969
  simp only [CollatzResearch.WordTrace]
  refine ⟨27061832648980506061756961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18041221765987004041171307 27061832648980506061756961)
  ·
    refine ⟨20296374486735379546317721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27061832648980506061756961 20296374486735379546317721)
    ·
      refine ⟨15222280865051534659738291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20296374486735379546317721 15222280865051534659738291)
      ·
        refine ⟨22833421297577301989607437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15222280865051534659738291 22833421297577301989607437)
        ·
          refine ⟨8562532986591488246102789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22833421297577301989607437 8562532986591488246102789)
          ·
            refine ⟨1605474934985904046144273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8562532986591488246102789 1605474934985904046144273)
            ·
              refine ⟨1204106201239428034608205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1605474934985904046144273 1204106201239428034608205)
              ·
                refine ⟨451539825464785512978077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1204106201239428034608205 451539825464785512978077)
                ·
                  refine ⟨169327434549294567366779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451539825464785512978077 169327434549294567366779)
                  ·
                    rfl

theorem cell21_741969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 3].length) (baseStart_741969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741969 prefixEnd_741969 := by exact prefixLift 741969
  have htrace : WordTrace (prefixWord ++ tailWord_741969) baseStart_741969 baseEnd_741969 := by
    simpa [prefixWord, tailWord_741969, baseEnd_741969] using wordTrace_append hprefix tailTrace_741969
  have hstable : (prefixWord ++ tailWord_741969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741969).length < 2 ^ (prefixWord ++ tailWord_741969).sum := by decide
  have hdescent : baseEnd_741969 < baseStart_741969 := by decide
  rcases family_descends (prefixWord ++ tailWord_741969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_741986 : List Nat := [3, 3, 2, 3, 1, 1, 2, 1, 5]
def baseStart_741986 : Nat := 118140960795 + 741986 * 2 ^ 59
def prefixEnd_741986 : Nat := 4983230072969 + 3 ^ 40 * 741986 * 2
def baseEnd_741986 : Nat := 169331314180906315583411

theorem tailTrace_741986 : CollatzResearch.WordTrace tailWord_741986 prefixEnd_741986 169331314180906315583411 := by
  unfold tailWord_741986
  simp only [CollatzResearch.WordTrace]
  refine ⟨6765613172479729491281453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18041635126612611976750541 6765613172479729491281453)
  ·
    refine ⟨2537104939679898559230545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6765613172479729491281453 2537104939679898559230545)
    ·
      refine ⟨1902828704759923919422909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2537104939679898559230545 1902828704759923919422909)
      ·
        refine ⟨713560764284971469783591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1902828704759923919422909 713560764284971469783591)
        ·
          refine ⟨1070341146427457204675387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713560764284971469783591 1070341146427457204675387)
          ·
            refine ⟨1605511719641185807013081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070341146427457204675387 1605511719641185807013081)
            ·
              refine ⟨1204133789730889355259811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1605511719641185807013081 1204133789730889355259811)
              ·
                refine ⟨1806200684596334032889717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204133789730889355259811 1806200684596334032889717)
                ·
                  refine ⟨169331314180906315583411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1806200684596334032889717 169331314180906315583411)
                  ·
                    rfl

theorem cell21_741986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_741986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_741986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_741986 prefixEnd_741986 := by exact prefixLift 741986
  have htrace : WordTrace (prefixWord ++ tailWord_741986) baseStart_741986 baseEnd_741986 := by
    simpa [prefixWord, tailWord_741986, baseEnd_741986] using wordTrace_append hprefix tailTrace_741986
  have hstable : (prefixWord ++ tailWord_741986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_741986).length < 2 ^ (prefixWord ++ tailWord_741986).sum := by decide
  have hdescent : baseEnd_741986 < baseStart_741986 := by decide
  rcases family_descends (prefixWord ++ tailWord_741986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742000 : List Nat := [2, 1, 1, 1, 7, 1, 3, 1, 4]
def baseStart_742000 : Nat := 118140960795 + 742000 * 2 ^ 59
def prefixEnd_742000 : Nat := 4983230072969 + 3 ^ 40 * 742000 * 2
def baseEnd_742000 : Nat := 169334509171645402350049

theorem tailTrace_742000 : CollatzResearch.WordTrace tailWord_742000 prefixEnd_742000 169334509171645402350049 := by
  unfold tailWord_742000
  simp only [CollatzResearch.WordTrace]
  refine ⟨13531481655934099178067727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18041975541245465570756969 13531481655934099178067727)
  ·
    refine ⟨20297222483901148767101591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13531481655934099178067727 20297222483901148767101591)
    ·
      refine ⟨30445833725851723150652387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20297222483901148767101591 30445833725851723150652387)
      ·
        refine ⟨45668750588777584725978581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30445833725851723150652387 45668750588777584725978581)
        ·
          refine ⟨1070361341924474642015123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 45668750588777584725978581 1070361341924474642015123)
          ·
            refine ⟨1605542012886711963022685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070361341924474642015123 1605542012886711963022685)
            ·
              refine ⟨602078254832516986133507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1605542012886711963022685 602078254832516986133507)
              ·
                refine ⟨903117382248775479200261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602078254832516986133507 903117382248775479200261)
                ·
                  refine ⟨169334509171645402350049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 903117382248775479200261 169334509171645402350049)
                  ·
                    rfl

theorem cell21_742000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 4].length) (baseStart_742000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742000 prefixEnd_742000 := by exact prefixLift 742000
  have htrace : WordTrace (prefixWord ++ tailWord_742000) baseStart_742000 baseEnd_742000 := by
    simpa [prefixWord, tailWord_742000, baseEnd_742000] using wordTrace_append hprefix tailTrace_742000
  have hstable : (prefixWord ++ tailWord_742000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742000).length < 2 ^ (prefixWord ++ tailWord_742000).sum := by decide
  have hdescent : baseEnd_742000 < baseStart_742000 := by decide
  rcases family_descends (prefixWord ++ tailWord_742000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742028 : List Nat := [2, 2, 1, 2, 1, 1, 2, 7, 3]
def baseStart_742028 : Nat := 118140960795 + 742028 * 2 ^ 59
def prefixEnd_742028 : Nat := 4983230072969 + 3 ^ 40 * 742028 * 2
def baseEnd_742028 : Nat := 169340899153123575883325

theorem tailTrace_742028 : CollatzResearch.WordTrace tailWord_742028 prefixEnd_742028 169340899153123575883325 := by
  unfold tailWord_742028
  simp only [CollatzResearch.WordTrace]
  refine ⟨13531992277883379569077369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18042656370511172758769825 13531992277883379569077369)
  ·
    refine ⟨10148994208412534676808027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13531992277883379569077369 10148994208412534676808027)
    ·
      refine ⟨15223491312618802015212041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10148994208412534676808027 15223491312618802015212041)
      ·
        refine ⟨11417618484464101511409031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15223491312618802015212041 11417618484464101511409031)
        ·
          refine ⟨17126427726696152267113547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11417618484464101511409031 17126427726696152267113547)
          ·
            refine ⟨25689641590044228400670321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17126427726696152267113547 25689641590044228400670321)
            ·
              refine ⟨19267231192533171300502741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25689641590044228400670321 19267231192533171300502741)
              ·
                refine ⟨451575731074996202355533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19267231192533171300502741 451575731074996202355533)
                ·
                  refine ⟨169340899153123575883325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451575731074996202355533 169340899153123575883325)
                  ·
                    rfl

theorem cell21_742028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 3].length) (baseStart_742028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742028 prefixEnd_742028 := by exact prefixLift 742028
  have htrace : WordTrace (prefixWord ++ tailWord_742028) baseStart_742028 baseEnd_742028 := by
    simpa [prefixWord, tailWord_742028, baseEnd_742028] using wordTrace_append hprefix tailTrace_742028
  have hstable : (prefixWord ++ tailWord_742028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742028).length < 2 ^ (prefixWord ++ tailWord_742028).sum := by decide
  have hdescent : baseEnd_742028 < baseStart_742028 := by decide
  rcases family_descends (prefixWord ++ tailWord_742028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742093 : List Nat := [1, 6, 2, 1, 2, 1, 2, 2, 4]
def baseStart_742093 : Nat := 118140960795 + 742093 * 2 ^ 59
def prefixEnd_742093 : Nat := 4983230072969 + 3 ^ 40 * 742093 * 2
def baseEnd_742093 : Nat := 169355733038697907299859

theorem tailTrace_742093 : CollatzResearch.WordTrace tailWord_742093 prefixEnd_742093 169355733038697907299859 := by
  unfold tailWord_742093
  simp only [CollatzResearch.WordTrace]
  refine ⟨27066355300531275239270933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18044236867020850159513955 27066355300531275239270933)
  ·
    refine ⟨1268735404712403526840825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27066355300531275239270933 1268735404712403526840825)
    ·
      refine ⟨951551553534302645130619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1268735404712403526840825 951551553534302645130619)
      ·
        refine ⟨1427327330301453967695929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 951551553534302645130619 1427327330301453967695929)
        ·
          refine ⟨1070495497726090475771947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1427327330301453967695929 1070495497726090475771947)
          ·
            refine ⟨1605743246589135713657921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070495497726090475771947 1605743246589135713657921)
            ·
              refine ⟨1204307434941851785243441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1605743246589135713657921 1204307434941851785243441)
              ·
                refine ⟨903230576206388838932581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1204307434941851785243441 903230576206388838932581)
                ·
                  refine ⟨169355733038697907299859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 903230576206388838932581 169355733038697907299859)
                  ·
                    rfl

theorem cell21_742093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_742093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742093 prefixEnd_742093 := by exact prefixLift 742093
  have htrace : WordTrace (prefixWord ++ tailWord_742093) baseStart_742093 baseEnd_742093 := by
    simpa [prefixWord, tailWord_742093, baseEnd_742093] using wordTrace_append hprefix tailTrace_742093
  have hstable : (prefixWord ++ tailWord_742093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742093).length < 2 ^ (prefixWord ++ tailWord_742093).sum := by decide
  have hdescent : baseEnd_742093 < baseStart_742093 := by decide
  rcases family_descends (prefixWord ++ tailWord_742093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742163 : List Nat := [1, 1, 1, 2, 1, 3, 6, 1, 5]
def baseStart_742163 : Nat := 118140960795 + 742163 * 2 ^ 59
def prefixEnd_742163 : Nat := 4983230072969 + 3 ^ 40 * 742163 * 2
def baseEnd_742163 : Nat := 169371707992393341133049

theorem tailTrace_742163 : CollatzResearch.WordTrace tailWord_742163 prefixEnd_742163 169371707992393341133049 := by
  unfold tailWord_742163
  simp only [CollatzResearch.WordTrace]
  refine ⟨27068908410277677194319143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18045938940185118129546095 27068908410277677194319143)
  ·
    refine ⟨40603362615416515791478715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27068908410277677194319143 40603362615416515791478715)
    ·
      refine ⟨60905043923124773687218073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40603362615416515791478715 60905043923124773687218073)
      ·
        refine ⟨45678782942343580265413555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60905043923124773687218073 45678782942343580265413555)
        ·
          refine ⟨68518174413515370398120333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45678782942343580265413555 68518174413515370398120333)
          ·
            refine ⟨25694315405068263899295125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68518174413515370398120333 25694315405068263899295125)
            ·
              refine ⟨1204421034612574870279459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25694315405068263899295125 1204421034612574870279459)
              ·
                refine ⟨1806631551918862305419189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204421034612574870279459 1806631551918862305419189)
                ·
                  refine ⟨169371707992393341133049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1806631551918862305419189 169371707992393341133049)
                  ·
                    rfl

theorem cell21_742163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 5].length) (baseStart_742163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742163 prefixEnd_742163 := by exact prefixLift 742163
  have htrace : WordTrace (prefixWord ++ tailWord_742163) baseStart_742163 baseEnd_742163 := by
    simpa [prefixWord, tailWord_742163, baseEnd_742163] using wordTrace_append hprefix tailTrace_742163
  have hstable : (prefixWord ++ tailWord_742163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742163).length < 2 ^ (prefixWord ++ tailWord_742163).sum := by decide
  have hdescent : baseEnd_742163 < baseStart_742163 := by decide
  rcases family_descends (prefixWord ++ tailWord_742163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742197 : List Nat := [1, 3, 3, 1, 3, 1, 3, 3, 3]
def baseStart_742197 : Nat := 118140960795 + 742197 * 2 ^ 59
def prefixEnd_742197 : Nat := 4983230072969 + 3 ^ 40 * 742197 * 2
def baseEnd_742197 : Nat := 169379467255616837566313

theorem tailTrace_742197 : CollatzResearch.WordTrace tailWord_742197 prefixEnd_742197 169379467255616837566313 := by
  unfold tailWord_742197
  simp only [CollatzResearch.WordTrace]
  refine ⟨27070148492154501001056845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18046765661436334000704563 27070148492154501001056845)
  ·
    refine ⟨10151305684557937875396317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27070148492154501001056845 10151305684557937875396317)
    ·
      refine ⟨3806739631709226703273619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10151305684557937875396317 3806739631709226703273619)
      ·
        refine ⟨5710109447563840054910429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3806739631709226703273619 5710109447563840054910429)
        ·
          refine ⟨2141291042836440020591411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5710109447563840054910429 2141291042836440020591411)
          ·
            refine ⟨3211936564254660030887117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2141291042836440020591411 3211936564254660030887117)
            ·
              refine ⟨1204476211595497511582669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3211936564254660030887117 1204476211595497511582669)
              ·
                refine ⟨451678579348311566843501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1204476211595497511582669 451678579348311566843501)
                ·
                  refine ⟨169379467255616837566313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451678579348311566843501 169379467255616837566313)
                  ·
                    rfl

theorem cell21_742197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 3].length) (baseStart_742197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742197 prefixEnd_742197 := by exact prefixLift 742197
  have htrace : WordTrace (prefixWord ++ tailWord_742197) baseStart_742197 baseEnd_742197 := by
    simpa [prefixWord, tailWord_742197, baseEnd_742197] using wordTrace_append hprefix tailTrace_742197
  have hstable : (prefixWord ++ tailWord_742197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742197).length < 2 ^ (prefixWord ++ tailWord_742197).sum := by decide
  have hdescent : baseEnd_742197 < baseStart_742197 := by decide
  rcases family_descends (prefixWord ++ tailWord_742197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742225 : List Nat := [1, 2, 2, 1, 6, 1, 2, 6]
def baseStart_742225 : Nat := 118140960795 + 742225 * 2 ^ 59
def prefixEnd_742225 : Nat := 4983230072969 + 3 ^ 40 * 742225 * 2
def baseEnd_742225 : Nat := 56461952412365003699863

theorem tailTrace_742225 : CollatzResearch.WordTrace tailWord_742225 prefixEnd_742225 56461952412365003699863 := by
  unfold tailWord_742225
  simp only [CollatzResearch.WordTrace]
  refine ⟨27071169736053061783076129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18047446490702041188717419 27071169736053061783076129)
  ·
    refine ⟨20303377302039796337307097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27071169736053061783076129 20303377302039796337307097)
    ·
      refine ⟨15227532976529847252980323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20303377302039796337307097 15227532976529847252980323)
      ·
        refine ⟨22841299464794770879470485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15227532976529847252980323 22841299464794770879470485)
        ·
          refine ⟨1070685912412254884975179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22841299464794770879470485 1070685912412254884975179)
          ·
            refine ⟨1606028868618382327462769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070685912412254884975179 1606028868618382327462769)
            ·
              refine ⟨1204521651463786745597077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1606028868618382327462769 1204521651463786745597077)
              ·
                refine ⟨56461952412365003699863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1204521651463786745597077 56461952412365003699863)
                ·
                  rfl

theorem cell21_742225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 6].length) (baseStart_742225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742225 prefixEnd_742225 := by exact prefixLift 742225
  have htrace : WordTrace (prefixWord ++ tailWord_742225) baseStart_742225 baseEnd_742225 := by
    simpa [prefixWord, tailWord_742225, baseEnd_742225] using wordTrace_append hprefix tailTrace_742225
  have hstable : (prefixWord ++ tailWord_742225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742225).length < 2 ^ (prefixWord ++ tailWord_742225).sum := by decide
  have hdescent : baseEnd_742225 < baseStart_742225 := by decide
  rcases family_descends (prefixWord ++ tailWord_742225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742284 : List Nat := [2, 2, 1, 2, 1, 2, 5, 6]
def baseStart_742284 : Nat := 118140960795 + 742284 * 2 ^ 59
def prefixEnd_742284 : Nat := 4983230072969 + 3 ^ 40 * 742284 * 2
def baseEnd_742284 : Nat := 56466440613641339872045

theorem tailTrace_742284 : CollatzResearch.WordTrace tailWord_742284 prefixEnd_742284 56466440613641339872045 := by
  unfold tailWord_742284
  simp only [CollatzResearch.WordTrace]
  refine ⟨13536660821419657429736953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18048881095226209906315937 13536660821419657429736953)
  ·
    refine ⟨10152495616064743072302715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13536660821419657429736953 10152495616064743072302715)
    ·
      refine ⟨15228743424097114608454073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10152495616064743072302715 15228743424097114608454073)
      ·
        refine ⟨11421557568072835956340555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15228743424097114608454073 11421557568072835956340555)
        ·
          refine ⟨17132336352109253934510833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11421557568072835956340555 17132336352109253934510833)
          ·
            refine ⟨12849252264081940450883125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17132336352109253934510833 12849252264081940450883125)
            ·
              refine ⟨1204617399757681917270293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12849252264081940450883125 1204617399757681917270293)
              ·
                refine ⟨56466440613641339872045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1204617399757681917270293 56466440613641339872045)
                ·
                  rfl

theorem cell21_742284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 6].length) (baseStart_742284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742284 prefixEnd_742284 := by exact prefixLift 742284
  have htrace : WordTrace (prefixWord ++ tailWord_742284) baseStart_742284 baseEnd_742284 := by
    simpa [prefixWord, tailWord_742284, baseEnd_742284] using wordTrace_append hprefix tailTrace_742284
  have hstable : (prefixWord ++ tailWord_742284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742284).length < 2 ^ (prefixWord ++ tailWord_742284).sum := by decide
  have hdescent : baseEnd_742284 < baseStart_742284 := by decide
  rcases family_descends (prefixWord ++ tailWord_742284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742301 : List Nat := [1, 4, 2, 1, 2, 1, 5, 5]
def baseStart_742301 : Nat := 118140960795 + 742301 * 2 ^ 59
def prefixEnd_742301 : Nat := 4983230072969 + 3 ^ 40 * 742301 * 2
def baseEnd_742301 : Nat := 56467733824178589277589

theorem tailTrace_742301 : CollatzResearch.WordTrace tailWord_742301 prefixEnd_742301 56467733824178589277589 := by
  unfold tailWord_742301
  simp only [CollatzResearch.WordTrace]
  refine ⟨27073941683777726762842757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18049294455851817841895171 27073941683777726762842757)
  ·
    refine ⟨5076364065708323768033017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27073941683777726762842757 5076364065708323768033017)
    ·
      refine ⟨3807273049281242826024763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5076364065708323768033017 3807273049281242826024763)
      ·
        refine ⟨5710909573921864239037145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3807273049281242826024763 5710909573921864239037145)
        ·
          refine ⟨4283182180441398179277859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5710909573921864239037145 4283182180441398179277859)
          ·
            refine ⟨6424773270662097268916789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4283182180441398179277859 6424773270662097268916789)
            ·
              refine ⟨602322494124571618960949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6424773270662097268916789 602322494124571618960949)
              ·
                refine ⟨56467733824178589277589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 602322494124571618960949 56467733824178589277589)
                ·
                  rfl

theorem cell21_742301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 5].length) (baseStart_742301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742301 prefixEnd_742301 := by exact prefixLift 742301
  have htrace : WordTrace (prefixWord ++ tailWord_742301) baseStart_742301 baseEnd_742301 := by
    simpa [prefixWord, tailWord_742301, baseEnd_742301] using wordTrace_append hprefix tailTrace_742301
  have hstable : (prefixWord ++ tailWord_742301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742301).length < 2 ^ (prefixWord ++ tailWord_742301).sum := by decide
  have hdescent : baseEnd_742301 < baseStart_742301 := by decide
  rcases family_descends (prefixWord ++ tailWord_742301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742360 : List Nat := [2, 1, 2, 2, 2, 4, 1, 7]
def baseStart_742360 : Nat := 118140960795 + 742360 * 2 ^ 59
def prefixEnd_742360 : Nat := 4983230072969 + 3 ^ 40 * 742360 * 2
def baseEnd_742360 : Nat := 56472222025454925449771

theorem tailTrace_742360 : CollatzResearch.WordTrace tailWord_742360 prefixEnd_742360 56472222025454925449771 := by
  unfold tailWord_742360
  simp only [CollatzResearch.WordTrace]
  refine ⟨13538046795281989919620267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18050729060375986559493689 13538046795281989919620267)
  ·
    refine ⟨20307070192922984879430401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13538046795281989919620267 20307070192922984879430401)
    ·
      refine ⟨15230302644692238659572801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20307070192922984879430401 15230302644692238659572801)
      ·
        refine ⟨11422726983519178994679601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15230302644692238659572801 11422726983519178994679601)
        ·
          refine ⟨8567045237639384246009701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11422726983519178994679601 8567045237639384246009701)
          ·
            refine ⟨1606320982057384546126819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8567045237639384246009701 1606320982057384546126819)
            ·
              refine ⟨2409481473086076819190229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1606320982057384546126819 2409481473086076819190229)
              ·
                refine ⟨56472222025454925449771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2409481473086076819190229 56472222025454925449771)
                ·
                  rfl

theorem cell21_742360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 7].length) (baseStart_742360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742360 prefixEnd_742360 := by exact prefixLift 742360
  have htrace : WordTrace (prefixWord ++ tailWord_742360) baseStart_742360 baseEnd_742360 := by
    simpa [prefixWord, tailWord_742360, baseEnd_742360] using wordTrace_append hprefix tailTrace_742360
  have hstable : (prefixWord ++ tailWord_742360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742360).length < 2 ^ (prefixWord ++ tailWord_742360).sum := by decide
  have hdescent : baseEnd_742360 < baseStart_742360 := by decide
  rcases family_descends (prefixWord ++ tailWord_742360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742436 : List Nat := [2, 3, 1, 4, 1, 10]
def baseStart_742436 : Nat := 118140960795 + 742436 * 2 ^ 59
def prefixEnd_742436 : Nat := 4983230072969 + 3 ^ 40 * 742436 * 2
def baseEnd_742436 : Nat := 6275333715252056780833

theorem tailTrace_742436 : CollatzResearch.WordTrace tailWord_742436 prefixEnd_742436 6275333715252056780833 := by
  unfold tailWord_742436
  simp only [CollatzResearch.WordTrace]
  refine ⟨13539432769144322409503581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18052577025525763212671441 13539432769144322409503581)
  ·
    refine ⟨5077287288429120903563843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13539432769144322409503581 5077287288429120903563843)
    ·
      refine ⟨7615930932643681355345765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5077287288429120903563843 7615930932643681355345765)
      ·
        refine ⟨1427987049870690254127331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7615930932643681355345765 1427987049870690254127331)
        ·
          refine ⟨2141980574806035381190997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1427987049870690254127331 2141980574806035381190997)
          ·
            refine ⟨6275333715252056780833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2141980574806035381190997 6275333715252056780833)
            ·
              rfl

theorem cell21_742436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 10].length) (baseStart_742436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742436 prefixEnd_742436 := by exact prefixLift 742436
  have htrace : WordTrace (prefixWord ++ tailWord_742436) baseStart_742436 baseEnd_742436 := by
    simpa [prefixWord, tailWord_742436, baseEnd_742436] using wordTrace_append hprefix tailTrace_742436
  have hstable : (prefixWord ++ tailWord_742436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742436).length < 2 ^ (prefixWord ++ tailWord_742436).sum := by decide
  have hdescent : baseEnd_742436 < baseStart_742436 := by decide
  rcases family_descends (prefixWord ++ tailWord_742436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742439 : List Nat := [1, 1, 7, 1, 1, 1, 1, 4, 4]
def baseStart_742439 : Nat := 118140960795 + 742439 * 2 ^ 59
def prefixEnd_742439 : Nat := 4983230072969 + 3 ^ 40 * 742439 * 2
def baseEnd_742439 : Nat := 169434694952678194532485

theorem tailTrace_742439 : CollatzResearch.WordTrace tailWord_742439 prefixEnd_742439 169434694952678194532485 := by
  unfold tailWord_742439
  simp only [CollatzResearch.WordTrace]
  refine ⟨27078974957277776331366371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18052649971518517554244247 27078974957277776331366371)
  ·
    refine ⟨40618462435916664497049557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27078974957277776331366371 40618462435916664497049557)
    ·
      refine ⟨951995213341796824149599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 40618462435916664497049557 951995213341796824149599)
      ·
        refine ⟨1427992820012695236224399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 951995213341796824149599 1427992820012695236224399)
        ·
          refine ⟨2141989230019042854336599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1427992820012695236224399 2141989230019042854336599)
          ·
            refine ⟨3212983845028564281504899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2141989230019042854336599 3212983845028564281504899)
            ·
              refine ⟨4819475767542846422257349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3212983845028564281504899 4819475767542846422257349)
              ·
                refine ⟨903651706414283704173253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4819475767542846422257349 903651706414283704173253)
                ·
                  refine ⟨169434694952678194532485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 903651706414283704173253 169434694952678194532485)
                  ·
                    rfl

theorem cell21_742439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 4].length) (baseStart_742439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742439 prefixEnd_742439 := by exact prefixLift 742439
  have htrace : WordTrace (prefixWord ++ tailWord_742439) baseStart_742439 baseEnd_742439 := by
    simpa [prefixWord, tailWord_742439, baseEnd_742439] using wordTrace_append hprefix tailTrace_742439
  have hstable : (prefixWord ++ tailWord_742439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742439).length < 2 ^ (prefixWord ++ tailWord_742439).sum := by decide
  have hdescent : baseEnd_742439 < baseStart_742439 := by decide
  rcases family_descends (prefixWord ++ tailWord_742439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742484 : List Nat := [2, 4, 1, 1, 1, 1, 3, 5, 3]
def baseStart_742484 : Nat := 118140960795 + 742484 * 2 ^ 59
def prefixEnd_742484 : Nat := 4983230072969 + 3 ^ 40 * 742484 * 2
def baseEnd_742484 : Nat := 169444964565768116282393

theorem tailTrace_742484 : CollatzResearch.WordTrace tailWord_742484 prefixEnd_742484 169444964565768116282393 := by
  unfold tailWord_742484
  simp only [CollatzResearch.WordTrace]
  refine ⟨13540308121057374508377253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18053744161409832677836337 13540308121057374508377253)
  ·
    refine ⟨2538807772698257720320735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13540308121057374508377253 2538807772698257720320735)
    ·
      refine ⟨3808211659047386580481103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2538807772698257720320735 3808211659047386580481103)
      ·
        refine ⟨5712317488571079870721655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3808211659047386580481103 5712317488571079870721655)
        ·
          refine ⟨8568476232856619806082483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5712317488571079870721655 8568476232856619806082483)
          ·
            refine ⟨12852714349284929709123725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8568476232856619806082483 12852714349284929709123725)
            ·
              refine ⟨4819767880981848640921397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12852714349284929709123725 4819767880981848640921397)
              ·
                refine ⟨451853238842048310086381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4819767880981848640921397 451853238842048310086381)
                ·
                  refine ⟨169444964565768116282393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 451853238842048310086381 169444964565768116282393)
                  ·
                    rfl

theorem cell21_742484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_742484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742484 prefixEnd_742484 := by exact prefixLift 742484
  have htrace : WordTrace (prefixWord ++ tailWord_742484) baseStart_742484 baseEnd_742484 := by
    simpa [prefixWord, tailWord_742484, baseEnd_742484] using wordTrace_append hprefix tailTrace_742484
  have hstable : (prefixWord ++ tailWord_742484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742484).length < 2 ^ (prefixWord ++ tailWord_742484).sum := by decide
  have hdescent : baseEnd_742484 < baseStart_742484 := by decide
  rcases family_descends (prefixWord ++ tailWord_742484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742495 : List Nat := [1, 1, 2, 3, 1, 1, 12]
def baseStart_742495 : Nat := 118140960795 + 742495 * 2 ^ 59
def prefixEnd_742495 : Nat := 4983230072969 + 3 ^ 40 * 742495 * 2
def baseEnd_742495 : Nat := 18827497212848282399893

theorem tailTrace_742495 : CollatzResearch.WordTrace tailWord_742495 prefixEnd_742495 18827497212848282399893 := by
  unfold tailWord_742495
  simp only [CollatzResearch.WordTrace]
  refine ⟨27081017445074897895404939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18054011630049931930269959 27081017445074897895404939)
  ·
    refine ⟨40621526167612346843107409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27081017445074897895404939 40621526167612346843107409)
    ·
      refine ⟨30466144625709260132330557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40621526167612346843107409 30466144625709260132330557)
      ·
        refine ⟨11424804234640972549623959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30466144625709260132330557 11424804234640972549623959)
        ·
          refine ⟨17137206351961458824435939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11424804234640972549623959 17137206351961458824435939)
          ·
            refine ⟨25705809527942188236653909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17137206351961458824435939 25705809527942188236653909)
            ·
              refine ⟨18827497212848282399893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 25705809527942188236653909 18827497212848282399893)
              ·
                rfl

theorem cell21_742495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 12].length) (baseStart_742495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742495 prefixEnd_742495 := by exact prefixLift 742495
  have htrace : WordTrace (prefixWord ++ tailWord_742495) baseStart_742495 baseEnd_742495 := by
    simpa [prefixWord, tailWord_742495, baseEnd_742495] using wordTrace_append hprefix tailTrace_742495
  have hstable : (prefixWord ++ tailWord_742495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742495).length < 2 ^ (prefixWord ++ tailWord_742495).sum := by decide
  have hdescent : baseEnd_742495 < baseStart_742495 := by decide
  rcases family_descends (prefixWord ++ tailWord_742495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742529 : List Nat := [1, 2, 4, 2, 2, 1, 4, 5]
def baseStart_742529 : Nat := 118140960795 + 742529 * 2 ^ 59
def prefixEnd_742529 : Nat := 4983230072969 + 3 ^ 40 * 742529 * 2
def baseEnd_742529 : Nat := 56485078059619346010767

theorem tailTrace_742529 : CollatzResearch.WordTrace tailWord_742529 prefixEnd_742529 56485078059619346010767 := by
  unfold tailWord_742529
  simp only [CollatzResearch.WordTrace]
  refine ⟨27082257526951721702142641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18054838351301147801428427 27082257526951721702142641)
  ·
    refine ⟨20311693145213791276606981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27082257526951721702142641 20311693145213791276606981)
    ·
      refine ⟨3808442464727585864363809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20311693145213791276606981 3808442464727585864363809)
      ·
        refine ⟨2856331848545689398272857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3808442464727585864363809 2856331848545689398272857)
        ·
          refine ⟨2142248886409267048704643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2856331848545689398272857 2142248886409267048704643)
          ·
            refine ⟨3213373329613900573056965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2142248886409267048704643 3213373329613900573056965)
            ·
              refine ⟨602507499302606357448181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3213373329613900573056965 602507499302606357448181)
              ·
                refine ⟨56485078059619346010767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 602507499302606357448181 56485078059619346010767)
                ·
                  rfl

theorem cell21_742529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 5].length) (baseStart_742529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742529 prefixEnd_742529 := by exact prefixLift 742529
  have htrace : WordTrace (prefixWord ++ tailWord_742529) baseStart_742529 baseEnd_742529 := by
    simpa [prefixWord, tailWord_742529, baseEnd_742529] using wordTrace_append hprefix tailTrace_742529
  have hstable : (prefixWord ++ tailWord_742529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742529).length < 2 ^ (prefixWord ++ tailWord_742529).sum := by decide
  have hdescent : baseEnd_742529 < baseStart_742529 := by decide
  rcases family_descends (prefixWord ++ tailWord_742529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742557 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 6]
def baseStart_742557 : Nat := 118140960795 + 742557 * 2 ^ 59
def prefixEnd_742557 : Nat := 4983230072969 + 3 ^ 40 * 742557 * 2
def baseEnd_742557 : Nat := 169461624160336211565577

theorem tailTrace_742557 : CollatzResearch.WordTrace tailWord_742557 prefixEnd_742557 169461624160336211565577 := by
  unfold tailWord_742557
  simp only [CollatzResearch.WordTrace]
  refine ⟨27083278770850282484161925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18055519180566854989441283 27083278770850282484161925)
  ·
    refine ⟨5078114769534427965780361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27083278770850282484161925 5078114769534427965780361)
    ·
      refine ⟨3808586077150820974335271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5078114769534427965780361 3808586077150820974335271)
      ·
        refine ⟨5712879115726231461502907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3808586077150820974335271 5712879115726231461502907)
        ·
          refine ⟨8569318673589347192254361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5712879115726231461502907 8569318673589347192254361)
          ·
            refine ⟨6426989005192010394190771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8569318673589347192254361 6426989005192010394190771)
            ·
              refine ⟨9640483507788015591286157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6426989005192010394190771 9640483507788015591286157)
              ·
                refine ⟨3615181315420505846732309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9640483507788015591286157 3615181315420505846732309)
                ·
                  refine ⟨169461624160336211565577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3615181315420505846732309 169461624160336211565577)
                  ·
                    rfl

theorem cell21_742557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_742557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742557 prefixEnd_742557 := by exact prefixLift 742557
  have htrace : WordTrace (prefixWord ++ tailWord_742557) baseStart_742557 baseEnd_742557 := by
    simpa [prefixWord, tailWord_742557, baseEnd_742557] using wordTrace_append hprefix tailTrace_742557
  have hstable : (prefixWord ++ tailWord_742557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742557).length < 2 ^ (prefixWord ++ tailWord_742557).sum := by decide
  have hdescent : baseEnd_742557 < baseStart_742557 := by decide
  rcases family_descends (prefixWord ++ tailWord_742557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742588 : List Nat := [2, 2, 2, 3, 2, 1, 2, 7]
def baseStart_742588 : Nat := 118140960795 + 742588 * 2 ^ 59
def prefixEnd_742588 : Nat := 4983230072969 + 3 ^ 40 * 742588 * 2
def baseEnd_742588 : Nat := 56489566260895682182949

theorem tailTrace_742588 : CollatzResearch.WordTrace tailWord_742588 prefixEnd_742588 56489566260895682182949 := by
  unfold tailWord_742588
  simp only [CollatzResearch.WordTrace]
  refine ⟨13542204716868987389270209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18056272955825316519026945 13542204716868987389270209)
  ·
    refine ⟨10156653537651740541952657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13542204716868987389270209 10156653537651740541952657)
    ·
      refine ⟨7617490153238805406464493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10156653537651740541952657 7617490153238805406464493)
      ·
        refine ⟨2856558807464552027424185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7617490153238805406464493 2856558807464552027424185)
        ·
          refine ⟨2142419105598414020568139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2856558807464552027424185 2142419105598414020568139)
          ·
            refine ⟨3213628658397621030852209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2142419105598414020568139 3213628658397621030852209)
            ·
              refine ⟨2410221493798215773139157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3213628658397621030852209 2410221493798215773139157)
              ·
                refine ⟨56489566260895682182949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2410221493798215773139157 56489566260895682182949)
                ·
                  rfl

theorem cell21_742588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 7].length) (baseStart_742588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742588 prefixEnd_742588 := by exact prefixLift 742588
  have htrace : WordTrace (prefixWord ++ tailWord_742588) baseStart_742588 baseEnd_742588 := by
    simpa [prefixWord, tailWord_742588, baseEnd_742588] using wordTrace_append hprefix tailTrace_742588
  have hstable : (prefixWord ++ tailWord_742588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742588).length < 2 ^ (prefixWord ++ tailWord_742588).sum := by decide
  have hdescent : baseEnd_742588 < baseStart_742588 := by decide
  rcases family_descends (prefixWord ++ tailWord_742588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742605 : List Nat := [1, 6, 2, 2, 10]
def baseStart_742605 : Nat := 118140960795 + 742605 * 2 ^ 59
def prefixEnd_742605 : Nat := 4983230072969 + 3 ^ 40 * 742605 * 2
def baseEnd_742605 : Nat := 2092254054497515984759

theorem tailTrace_742605 : CollatzResearch.WordTrace tailWord_742605 prefixEnd_742605 2092254054497515984759 := by
  unfold tailWord_742605
  simp only [CollatzResearch.WordTrace]
  refine ⟨27085029474676386681909269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18056686316450924454606179 27085029474676386681909269)
  ·
    refine ⟨1269610756625455625714497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27085029474676386681909269 1269610756625455625714497)
    ·
      refine ⟨952208067469091719285873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1269610756625455625714497 952208067469091719285873)
      ·
        refine ⟨714156050601818789464405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 952208067469091719285873 714156050601818789464405)
        ·
          refine ⟨2092254054497515984759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 714156050601818789464405 2092254054497515984759)
          ·
            rfl

theorem cell21_742605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 10].length) (baseStart_742605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742605 prefixEnd_742605 := by exact prefixLift 742605
  have htrace : WordTrace (prefixWord ++ tailWord_742605) baseStart_742605 baseEnd_742605 := by
    simpa [prefixWord, tailWord_742605, baseEnd_742605] using wordTrace_append hprefix tailTrace_742605
  have hstable : (prefixWord ++ tailWord_742605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742605).length < 2 ^ (prefixWord ++ tailWord_742605).sum := by decide
  have hdescent : baseEnd_742605 < baseStart_742605 := by decide
  rcases family_descends (prefixWord ++ tailWord_742605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742664 : List Nat := [2, 1, 3, 2, 4, 1, 8]
def baseStart_742664 : Nat := 118140960795 + 742664 * 2 ^ 59
def prefixEnd_742664 : Nat := 4983230072969 + 3 ^ 40 * 742664 * 2
def baseEnd_742664 : Nat := 18831782557569755920225

theorem tailTrace_742664 : CollatzResearch.WordTrace tailWord_742664 prefixEnd_742664 18831782557569755920225 := by
  unfold tailWord_742664
  simp only [CollatzResearch.WordTrace]
  refine ⟨13543590690731319879153523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18058120920975093172204697 13543590690731319879153523)
  ·
    refine ⟨20315386036096979818730285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13543590690731319879153523 20315386036096979818730285)
    ·
      refine ⟨7618269763536367432023857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20315386036096979818730285 7618269763536367432023857)
      ·
        refine ⟨5713702322652275574017893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7618269763536367432023857 5713702322652275574017893)
        ·
          refine ⟨1071319185497301670128355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5713702322652275574017893 1071319185497301670128355)
          ·
            refine ⟨1606978778245952505192533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1071319185497301670128355 1606978778245952505192533)
            ·
              refine ⟨18831782557569755920225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1606978778245952505192533 18831782557569755920225)
              ·
                rfl

theorem cell21_742664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 8].length) (baseStart_742664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742664 prefixEnd_742664 := by exact prefixLift 742664
  have htrace : WordTrace (prefixWord ++ tailWord_742664) baseStart_742664 baseEnd_742664 := by
    simpa [prefixWord, tailWord_742664, baseEnd_742664] using wordTrace_append hprefix tailTrace_742664
  have hstable : (prefixWord ++ tailWord_742664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742664).length < 2 ^ (prefixWord ++ tailWord_742664).sum := by decide
  have hdescent : baseEnd_742664 < baseStart_742664 := by decide
  rcases family_descends (prefixWord ++ tailWord_742664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742698 : List Nat := [3, 1, 4, 2, 1, 3, 2, 5]
def baseStart_742698 : Nat := 118140960795 + 742698 * 2 ^ 59
def prefixEnd_742698 : Nat := 4983230072969 + 3 ^ 40 * 742698 * 2
def baseEnd_742698 : Nat := 56497934093783766571763

theorem tailTrace_742698 : CollatzResearch.WordTrace tailWord_742698 prefixEnd_742698 56497934093783766571763 := by
  unfold tailWord_742698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6772105365834865891261187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18058947642226309043363165 6772105365834865891261187)
  ·
    refine ⟨10158158048752298836891781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6772105365834865891261187 10158158048752298836891781)
    ·
      refine ⟨1904654634141056031917209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10158158048752298836891781 1904654634141056031917209)
      ·
        refine ⟨1428490975605792023937907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1904654634141056031917209 1428490975605792023937907)
        ·
          refine ⟨2142736463408688035906861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1428490975605792023937907 2142736463408688035906861)
          ·
            refine ⟨803526173778258013465073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2142736463408688035906861 803526173778258013465073)
            ·
              refine ⟨602644630333693510098805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 803526173778258013465073 602644630333693510098805)
              ·
                refine ⟨56497934093783766571763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 602644630333693510098805 56497934093783766571763)
                ·
                  rfl

theorem cell21_742698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_742698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742698 prefixEnd_742698 := by exact prefixLift 742698
  have htrace : WordTrace (prefixWord ++ tailWord_742698) baseStart_742698 baseEnd_742698 := by
    simpa [prefixWord, tailWord_742698, baseEnd_742698] using wordTrace_append hprefix tailTrace_742698
  have hstable : (prefixWord ++ tailWord_742698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742698).length < 2 ^ (prefixWord ++ tailWord_742698).sum := by decide
  have hdescent : baseEnd_742698 < baseStart_742698 := by decide
  rcases family_descends (prefixWord ++ tailWord_742698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742709 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 6]
def baseStart_742709 : Nat := 118140960795 + 742709 * 2 ^ 59
def prefixEnd_742709 : Nat := 4983230072969 + 3 ^ 40 * 742709 * 2
def baseEnd_742709 : Nat := 169496312631217725031933

theorem tailTrace_742709 : CollatzResearch.WordTrace tailWord_742709 prefixEnd_742709 169496312631217725031933 := by
  unfold tailWord_742709
  simp only [CollatzResearch.WordTrace]
  refine ⟨27088822666299612443695181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18059215110866408295796787 27088822666299612443695181)
  ·
    refine ⟨10158308499862354666385693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27088822666299612443695181 10158308499862354666385693)
    ·
      refine ⟨3809365687448382999894635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10158308499862354666385693 3809365687448382999894635)
      ·
        refine ⟨5714048531172574499841953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3809365687448382999894635 5714048531172574499841953)
        ·
          refine ⟨4285536398379430874881465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5714048531172574499841953 4285536398379430874881465)
          ·
            refine ⟨3214152298784573156161099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4285536398379430874881465 3214152298784573156161099)
            ·
              refine ⟨4821228448176859734241649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3214152298784573156161099 4821228448176859734241649)
              ·
                refine ⟨3615921336132644800681237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4821228448176859734241649 3615921336132644800681237)
                ·
                  refine ⟨169496312631217725031933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3615921336132644800681237 169496312631217725031933)
                  ·
                    rfl

theorem cell21_742709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_742709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742709 prefixEnd_742709 := by exact prefixLift 742709
  have htrace : WordTrace (prefixWord ++ tailWord_742709) baseStart_742709 baseEnd_742709 := by
    simpa [prefixWord, tailWord_742709, baseEnd_742709] using wordTrace_append hprefix tailTrace_742709
  have hstable : (prefixWord ++ tailWord_742709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742709).length < 2 ^ (prefixWord ++ tailWord_742709).sum := by decide
  have hdescent : baseEnd_742709 < baseStart_742709 := by decide
  rcases family_descends (prefixWord ++ tailWord_742709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742740 : List Nat := [2, 4, 1, 1, 2, 1, 4, 6]
def baseStart_742740 : Nat := 118140960795 + 742740 * 2 ^ 59
def prefixEnd_742740 : Nat := 4983230072969 + 3 ^ 40 * 742740 * 2
def baseEnd_742740 : Nat := 56501129084522853338401

theorem tailTrace_742740 : CollatzResearch.WordTrace tailWord_742740 prefixEnd_742740 56501129084522853338401 := by
  unfold tailWord_742740
  simp only [CollatzResearch.WordTrace]
  refine ⟨13544976664593652369036837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18059968886124869825382449 13544976664593652369036837)
  ·
    refine ⟨2539683124611309819194407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13544976664593652369036837 2539683124611309819194407)
    ·
      refine ⟨3809524686916964728791611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2539683124611309819194407 3809524686916964728791611)
      ·
        refine ⟨5714287030375447093187417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3809524686916964728791611 5714287030375447093187417)
        ·
          refine ⟨4285715272781585319890563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5714287030375447093187417 4285715272781585319890563)
          ·
            refine ⟨6428572909172377979835845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4285715272781585319890563 6428572909172377979835845)
            ·
              refine ⟨1205357420469820871219221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6428572909172377979835845 1205357420469820871219221)
              ·
                refine ⟨56501129084522853338401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1205357420469820871219221 56501129084522853338401)
                ·
                  rfl

theorem cell21_742740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 6].length) (baseStart_742740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742740 prefixEnd_742740 := by exact prefixLift 742740
  have htrace : WordTrace (prefixWord ++ tailWord_742740) baseStart_742740 baseEnd_742740 := by
    simpa [prefixWord, tailWord_742740, baseEnd_742740] using wordTrace_append hprefix tailTrace_742740
  have hstable : (prefixWord ++ tailWord_742740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742740).length < 2 ^ (prefixWord ++ tailWord_742740).sum := by decide
  have hdescent : baseEnd_742740 < baseStart_742740 := by decide
  rcases family_descends (prefixWord ++ tailWord_742740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742743 : List Nat := [1, 1, 3, 2, 3, 4, 2, 1, 4]
def baseStart_742743 : Nat := 118140960795 + 742743 * 2 ^ 59
def prefixEnd_742743 : Nat := 4983230072969 + 3 ^ 40 * 742743 * 2
def baseEnd_742743 : Nat := 169504071894441221465197

theorem tailTrace_742743 : CollatzResearch.WordTrace tailWord_742743 prefixEnd_742743 169504071894441221465197 := by
  unfold tailWord_742743
  simp only [CollatzResearch.WordTrace]
  refine ⟨27090062748176436250432883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18060041832117624166955255 27090062748176436250432883)
  ·
    refine ⟨40635094122264654375649325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27090062748176436250432883 40635094122264654375649325)
    ·
      refine ⟨15238160295849245390868497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40635094122264654375649325 15238160295849245390868497)
      ·
        refine ⟨11428620221886934043151373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15238160295849245390868497 11428620221886934043151373)
        ·
          refine ⟨4285732583207600266181765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11428620221886934043151373 4285732583207600266181765)
          ·
            refine ⟨803574859351425049909081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4285732583207600266181765 803574859351425049909081)
            ·
              refine ⟨602681144513568787431811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 803574859351425049909081 602681144513568787431811)
              ·
                refine ⟨904021716770353181147717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602681144513568787431811 904021716770353181147717)
                ·
                  refine ⟨169504071894441221465197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 904021716770353181147717 169504071894441221465197)
                  ·
                    rfl

theorem cell21_742743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 4].length) (baseStart_742743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742743 prefixEnd_742743 := by exact prefixLift 742743
  have htrace : WordTrace (prefixWord ++ tailWord_742743) baseStart_742743 baseEnd_742743 := by
    simpa [prefixWord, tailWord_742743, baseEnd_742743] using wordTrace_append hprefix tailTrace_742743
  have hstable : (prefixWord ++ tailWord_742743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742743).length < 2 ^ (prefixWord ++ tailWord_742743).sum := by decide
  have hdescent : baseEnd_742743 < baseStart_742743 := by decide
  rcases family_descends (prefixWord ++ tailWord_742743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742788 : List Nat := [2, 3, 2, 1, 1, 4, 1, 4, 3]
def baseStart_742788 : Nat := 118140960795 + 742788 * 2 ^ 59
def prefixEnd_742788 : Nat := 4983230072969 + 3 ^ 40 * 742788 * 2
def baseEnd_742788 : Nat := 169514341507531143215105

theorem tailTrace_742788 : CollatzResearch.WordTrace tailWord_742788 prefixEnd_742788 169514341507531143215105 := by
  unfold tailWord_742788
  simp only [CollatzResearch.WordTrace]
  refine ⟨13545852016506704467910509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18061136022008939290547345 13545852016506704467910509)
  ·
    refine ⟨5079694506190014175466441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13545852016506704467910509 5079694506190014175466441)
    ·
      refine ⟨3809770879642510631599831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5079694506190014175466441 3809770879642510631599831)
      ·
        refine ⟨5714656319463765947399747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3809770879642510631599831 5714656319463765947399747)
        ·
          refine ⟨8571984479195648921099621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5714656319463765947399747 8571984479195648921099621)
          ·
            refine ⟨1607247089849184172706179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8571984479195648921099621 1607247089849184172706179)
            ·
              refine ⟨2410870634773776259059269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607247089849184172706179 2410870634773776259059269)
              ·
                refine ⟨452038244020083048573613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2410870634773776259059269 452038244020083048573613)
                ·
                  refine ⟨169514341507531143215105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 452038244020083048573613 169514341507531143215105)
                  ·
                    rfl

theorem cell21_742788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_742788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742788 prefixEnd_742788 := by exact prefixLift 742788
  have htrace : WordTrace (prefixWord ++ tailWord_742788) baseStart_742788 baseEnd_742788 := by
    simpa [prefixWord, tailWord_742788, baseEnd_742788] using wordTrace_append hprefix tailTrace_742788
  have hstable : (prefixWord ++ tailWord_742788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742788).length < 2 ^ (prefixWord ++ tailWord_742788).sum := by decide
  have hdescent : baseEnd_742788 < baseStart_742788 := by decide
  rcases family_descends (prefixWord ++ tailWord_742788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742816 : List Nat := [2, 1, 1, 4, 1, 2, 5, 5]
def baseStart_742816 : Nat := 118140960795 + 742816 * 2 ^ 59
def prefixEnd_742816 : Nat := 4983230072969 + 3 ^ 40 * 742816 * 2
def baseEnd_742816 : Nat := 56506910496336438916127

theorem tailTrace_742816 : CollatzResearch.WordTrace tailWord_742816 prefixEnd_742816 56506910496336438916127 := by
  unfold tailWord_742816
  simp only [CollatzResearch.WordTrace]
  refine ⟨13546362638455984858920151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18061816851274646478560201 13546362638455984858920151)
  ·
    refine ⟨20319543957683977288380227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13546362638455984858920151 20319543957683977288380227)
    ·
      refine ⟨30479315936525965932570341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20319543957683977288380227 30479315936525965932570341)
      ·
        refine ⟨5714871738098618612356939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30479315936525965932570341 5714871738098618612356939)
        ·
          refine ⟨8572307607147927918535409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5714871738098618612356939 8572307607147927918535409)
          ·
            refine ⟨6429230705360945938901557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8572307607147927918535409 6429230705360945938901557)
            ·
              refine ⟨602740378627588681772021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6429230705360945938901557 602740378627588681772021)
              ·
                refine ⟨56506910496336438916127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 602740378627588681772021 56506910496336438916127)
                ·
                  rfl

theorem cell21_742816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 5].length) (baseStart_742816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742816 prefixEnd_742816 := by exact prefixLift 742816
  have htrace : WordTrace (prefixWord ++ tailWord_742816) baseStart_742816 baseEnd_742816 := by
    simpa [prefixWord, tailWord_742816, baseEnd_742816] using wordTrace_append hprefix tailTrace_742816
  have hstable : (prefixWord ++ tailWord_742816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742816).length < 2 ^ (prefixWord ++ tailWord_742816).sum := by decide
  have hdescent : baseEnd_742816 < baseStart_742816 := by decide
  rcases family_descends (prefixWord ++ tailWord_742816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742951 : List Nat := [1, 1, 7, 12]
def baseStart_742951 : Nat := 118140960795 + 742951 * 2 ^ 59
def prefixEnd_742951 : Nat := 4983230072969 + 3 ^ 40 * 742951 * 2
def baseEnd_742951 : Nat := 697742964313905687235

theorem tailTrace_742951 : CollatzResearch.WordTrace tailWord_742951 prefixEnd_742951 697742964313905687235 := by
  unfold tailWord_742951
  simp only [CollatzResearch.WordTrace]
  refine ⟨27097649131422887774004707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18065099420948591849336471 27097649131422887774004707)
  ·
    refine ⟨40646473697134331661007061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27097649131422887774004707 40646473697134331661007061)
    ·
      refine ⟨952651727276585898304853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 40646473697134331661007061 952651727276585898304853)
      ·
        refine ⟨697742964313905687235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 952651727276585898304853 697742964313905687235)
        ·
          rfl

theorem cell21_742951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 12].length) (baseStart_742951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742951 prefixEnd_742951 := by exact prefixLift 742951
  have htrace : WordTrace (prefixWord ++ tailWord_742951) baseStart_742951 baseEnd_742951 := by
    simpa [prefixWord, tailWord_742951, baseEnd_742951] using wordTrace_append hprefix tailTrace_742951
  have hstable : (prefixWord ++ tailWord_742951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742951).length < 2 ^ (prefixWord ++ tailWord_742951).sum := by decide
  have hdescent : baseEnd_742951 < baseStart_742951 := by decide
  rcases family_descends (prefixWord ++ tailWord_742951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742954 : List Nat := [3, 1, 4, 1, 1, 1, 4, 2, 4]
def baseStart_742954 : Nat := 118140960795 + 742954 * 2 ^ 59
def prefixEnd_742954 : Nat := 4983230072969 + 3 ^ 40 * 742954 * 2
def baseEnd_742954 : Nat := 169552224969151743448099

theorem tailTrace_742954 : CollatzResearch.WordTrace tailWord_742954 prefixEnd_742954 169552224969151743448099 := by
  unfold tailWord_742954
  simp only [CollatzResearch.WordTrace]
  refine ⟨6774439637603004821590979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18065172366941346190909277 6774439637603004821590979)
  ·
    refine ⟨10161659456404507232386469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6774439637603004821590979 10161659456404507232386469)
    ·
      refine ⟨1905311148075845106072463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10161659456404507232386469 1905311148075845106072463)
      ·
        refine ⟨2857966722113767659108695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1905311148075845106072463 2857966722113767659108695)
        ·
          refine ⟨4286950083170651488663043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2857966722113767659108695 4286950083170651488663043)
          ·
            refine ⟨6430425124755977232994565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4286950083170651488663043 6430425124755977232994565)
            ·
              refine ⟨1205704710891745731186481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6430425124755977232994565 1205704710891745731186481)
              ·
                refine ⟨904278533168809298389861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1205704710891745731186481 904278533168809298389861)
                ·
                  refine ⟨169552224969151743448099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 904278533168809298389861 169552224969151743448099)
                  ·
                    rfl

theorem cell21_742954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_742954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742954 prefixEnd_742954 := by exact prefixLift 742954
  have htrace : WordTrace (prefixWord ++ tailWord_742954) baseStart_742954 baseEnd_742954 := by
    simpa [prefixWord, tailWord_742954, baseEnd_742954] using wordTrace_append hprefix tailTrace_742954
  have hstable : (prefixWord ++ tailWord_742954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742954).length < 2 ^ (prefixWord ++ tailWord_742954).sum := by decide
  have hdescent : baseEnd_742954 < baseStart_742954 := by decide
  rcases family_descends (prefixWord ++ tailWord_742954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742968 : List Nat := [2, 1, 2, 1, 4, 4, 1, 6]
def baseStart_742968 : Nat := 118140960795 + 742968 * 2 ^ 59
def prefixEnd_742968 : Nat := 4983230072969 + 3 ^ 40 * 742968 * 2
def baseEnd_742968 : Nat := 56518473319963610071579

theorem tailTrace_742968 : CollatzResearch.WordTrace tailWord_742968 prefixEnd_742968 56518473319963610071579 := by
  unfold tailWord_742968
  simp only [CollatzResearch.WordTrace]
  refine ⟨13549134586180649838686779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18065512781574199784915705 13549134586180649838686779)
  ·
    refine ⟨20323701879270974758030169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13549134586180649838686779 20323701879270974758030169)
    ·
      refine ⟨15242776409453231068522627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20323701879270974758030169 15242776409453231068522627)
      ·
        refine ⟨22864164614179846602783941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15242776409453231068522627 22864164614179846602783941)
        ·
          refine ⟨4287030865158721238021989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22864164614179846602783941 4287030865158721238021989)
          ·
            refine ⟨803818287217260232129123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4287030865158721238021989 803818287217260232129123)
            ·
              refine ⟨1205727430825890348193685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803818287217260232129123 1205727430825890348193685)
              ·
                refine ⟨56518473319963610071579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1205727430825890348193685 56518473319963610071579)
                ·
                  rfl

theorem cell21_742968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 6].length) (baseStart_742968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742968 prefixEnd_742968 := by exact prefixLift 742968
  have htrace : WordTrace (prefixWord ++ tailWord_742968) baseStart_742968 baseEnd_742968 := by
    simpa [prefixWord, tailWord_742968, baseEnd_742968] using wordTrace_append hprefix tailTrace_742968
  have hstable : (prefixWord ++ tailWord_742968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742968).length < 2 ^ (prefixWord ++ tailWord_742968).sum := by decide
  have hdescent : baseEnd_742968 < baseStart_742968 := by decide
  rcases family_descends (prefixWord ++ tailWord_742968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_742999 : List Nat := [1, 1, 3, 2, 2, 3, 1, 5, 3]
def baseStart_742999 : Nat := 118140960795 + 742999 * 2 ^ 59
def prefixEnd_742999 : Nat := 4983230072969 + 3 ^ 40 * 742999 * 2
def baseEnd_742999 : Nat := 169562494582241665198007

theorem tailTrace_742999 : CollatzResearch.WordTrace tailWord_742999 prefixEnd_742999 169562494582241665198007 := by
  unfold tailWord_742999
  simp only [CollatzResearch.WordTrace]
  refine ⟨27099399835248991971752051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18066266556832661314501367 27099399835248991971752051)
  ·
    refine ⟨40649099752873487957628077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27099399835248991971752051 40649099752873487957628077)
    ·
      refine ⟨15243412407327557984110529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40649099752873487957628077 15243412407327557984110529)
      ·
        refine ⟨11432559305495668488082897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15243412407327557984110529 11432559305495668488082897)
        ·
          refine ⟨8574419479121751366062173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11432559305495668488082897 8574419479121751366062173)
          ·
            refine ⟨3215407304670656762273315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8574419479121751366062173 3215407304670656762273315)
            ·
              refine ⟨4823110957005985143409973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3215407304670656762273315 4823110957005985143409973)
              ·
                refine ⟨452166652219311107194685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4823110957005985143409973 452166652219311107194685)
                ·
                  refine ⟨169562494582241665198007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 452166652219311107194685 169562494582241665198007)
                  ·
                    rfl

theorem cell21_742999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 3].length) (baseStart_742999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_742999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_742999 prefixEnd_742999 := by exact prefixLift 742999
  have htrace : WordTrace (prefixWord ++ tailWord_742999) baseStart_742999 baseEnd_742999 := by
    simpa [prefixWord, tailWord_742999, baseEnd_742999] using wordTrace_append hprefix tailTrace_742999
  have hstable : (prefixWord ++ tailWord_742999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_742999).length < 2 ^ (prefixWord ++ tailWord_742999).sum := by decide
  have hdescent : baseEnd_742999 < baseStart_742999 := by decide
  rcases family_descends (prefixWord ++ tailWord_742999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743005 : List Nat := [1, 4, 4, 2, 2, 1, 1, 2, 4]
def baseStart_743005 : Nat := 118140960795 + 743005 * 2 ^ 59
def prefixEnd_743005 : Nat := 4983230072969 + 3 ^ 40 * 743005 * 2
def baseEnd_743005 : Nat := 169563863863986988097995

theorem tailTrace_743005 : CollatzResearch.WordTrace tailWord_743005 prefixEnd_743005 169563863863986988097995 := by
  unfold tailWord_743005
  simp only [CollatzResearch.WordTrace]
  refine ⟨27099618673227254996470469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18066412448818169997646979 27099618673227254996470469)
  ·
    refine ⟨5081178501230110311838213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27099618673227254996470469 5081178501230110311838213)
    ·
      refine ⟨952720968980645683469665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5081178501230110311838213 952720968980645683469665)
      ·
        refine ⟨714540726735484262602249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 952720968980645683469665 714540726735484262602249)
        ·
          refine ⟨535905545051613196951687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 714540726735484262602249 535905545051613196951687)
          ·
            refine ⟨803858317577419795427531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535905545051613196951687 803858317577419795427531)
            ·
              refine ⟨1205787476366129693141297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803858317577419795427531 1205787476366129693141297)
              ·
                refine ⟨904340607274597269855973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1205787476366129693141297 904340607274597269855973)
                ·
                  refine ⟨169563863863986988097995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 904340607274597269855973 169563863863986988097995)
                  ·
                    rfl

theorem cell21_743005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_743005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743005 prefixEnd_743005 := by exact prefixLift 743005
  have htrace : WordTrace (prefixWord ++ tailWord_743005) baseStart_743005 baseEnd_743005 := by
    simpa [prefixWord, tailWord_743005, baseEnd_743005] using wordTrace_append hprefix tailTrace_743005
  have hstable : (prefixWord ++ tailWord_743005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743005).length < 2 ^ (prefixWord ++ tailWord_743005).sum := by decide
  have hdescent : baseEnd_743005 < baseStart_743005 := by decide
  rcases family_descends (prefixWord ++ tailWord_743005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743013 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 6]
def baseStart_743013 : Nat := 118140960795 + 743013 * 2 ^ 59
def prefixEnd_743013 : Nat := 4983230072969 + 3 ^ 40 * 743013 * 2
def baseEnd_743013 : Nat := 169565689572980751964645

theorem tailTrace_743013 : CollatzResearch.WordTrace tailWord_743013 prefixEnd_743013 169565689572980751964645 := by
  unfold tailWord_743013
  simp only [CollatzResearch.WordTrace]
  refine ⟨27099910457198272362761693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18066606971465514908507795 27099910457198272362761693)
  ·
    refine ⟨10162466421449352136035635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27099910457198272362761693 10162466421449352136035635)
    ·
      refine ⟨15243699632174028204053453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10162466421449352136035635 15243699632174028204053453)
      ·
        refine ⟨5716387362065260576520045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15243699632174028204053453 5716387362065260576520045)
        ·
          refine ⟨2143645260774472716195017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5716387362065260576520045 2143645260774472716195017)
          ·
            refine ⟨1607733945580854537146263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2143645260774472716195017 1607733945580854537146263)
            ·
              refine ⟨2411600918371281805719395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607733945580854537146263 2411600918371281805719395)
              ·
                refine ⟨3617401377556922708579093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2411600918371281805719395 3617401377556922708579093)
                ·
                  refine ⟨169565689572980751964645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3617401377556922708579093 169565689572980751964645)
                  ·
                    rfl

theorem cell21_743013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_743013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743013 prefixEnd_743013 := by exact prefixLift 743013
  have htrace : WordTrace (prefixWord ++ tailWord_743013) baseStart_743013 baseEnd_743013 := by
    simpa [prefixWord, tailWord_743013, baseEnd_743013] using wordTrace_append hprefix tailTrace_743013
  have hstable : (prefixWord ++ tailWord_743013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743013).length < 2 ^ (prefixWord ++ tailWord_743013).sum := by decide
  have hdescent : baseEnd_743013 < baseStart_743013 := by decide
  rcases family_descends (prefixWord ++ tailWord_743013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743016 : List Nat := [2, 1, 4, 3, 1, 1, 2, 4, 3]
def baseStart_743016 : Nat := 118140960795 + 743016 * 2 ^ 59
def prefixEnd_743016 : Nat := 4983230072969 + 3 ^ 40 * 743016 * 2
def baseEnd_743016 : Nat := 169566374213853413414639

theorem tailTrace_743016 : CollatzResearch.WordTrace tailWord_743016 prefixEnd_743016 169566374213853413414639 := by
  unfold tailWord_743016
  simp only [CollatzResearch.WordTrace]
  refine ⟨13550009938093701937560451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18066679917458269250080601 13550009938093701937560451)
  ·
    refine ⟨20325014907140552906340677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13550009938093701937560451 20325014907140552906340677)
    ·
      refine ⟨3810940295088853669938877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20325014907140552906340677 3810940295088853669938877)
      ·
        refine ⟨1429102610658320126227079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3810940295088853669938877 1429102610658320126227079)
        ·
          refine ⟨2143653915987480189340619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1429102610658320126227079 2143653915987480189340619)
          ·
            refine ⟨3215480873981220284010929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2143653915987480189340619 3215480873981220284010929)
            ·
              refine ⟨2411610655485915213008197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3215480873981220284010929 2411610655485915213008197)
              ·
                refine ⟨452176997903609102439037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2411610655485915213008197 452176997903609102439037)
                ·
                  refine ⟨169566374213853413414639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 452176997903609102439037 169566374213853413414639)
                  ·
                    rfl

theorem cell21_743016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 3].length) (baseStart_743016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743016 prefixEnd_743016 := by exact prefixLift 743016
  have htrace : WordTrace (prefixWord ++ tailWord_743016) baseStart_743016 baseEnd_743016 := by
    simpa [prefixWord, tailWord_743016, baseEnd_743016] using wordTrace_append hprefix tailTrace_743016
  have hstable : (prefixWord ++ tailWord_743016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743016).length < 2 ^ (prefixWord ++ tailWord_743016).sum := by decide
  have hdescent : baseEnd_743016 < baseStart_743016 := by decide
  rcases family_descends (prefixWord ++ tailWord_743016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743044 : List Nat := [2, 3, 2, 1, 4, 1, 1, 7]
def baseStart_743044 : Nat := 118140960795 + 743044 * 2 ^ 59
def prefixEnd_743044 : Nat := 4983230072969 + 3 ^ 40 * 743044 * 2
def baseEnd_743044 : Nat := 56524254731777195649305

theorem tailTrace_743044 : CollatzResearch.WordTrace tailWord_743044 prefixEnd_743044 56524254731777195649305 := by
  unfold tailWord_743044
  simp only [CollatzResearch.WordTrace]
  refine ⟨13550520560042982328570093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18067360746723976438093457 13550520560042982328570093)
  ·
    refine ⟨5081445210016118373213785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13550520560042982328570093 5081445210016118373213785)
    ·
      refine ⟨3811083907512088779910339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5081445210016118373213785 3811083907512088779910339)
      ·
        refine ⟨5716625861268133169865509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3811083907512088779910339 5716625861268133169865509)
        ·
          refine ⟨1071867348987774969349783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5716625861268133169865509 1071867348987774969349783)
          ·
            refine ⟨1607801023481662454024675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1071867348987774969349783 1607801023481662454024675)
            ·
              refine ⟨2411701535222493681037013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607801023481662454024675 2411701535222493681037013)
              ·
                refine ⟨56524254731777195649305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2411701535222493681037013 56524254731777195649305)
                ·
                  rfl

theorem cell21_743044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 7].length) (baseStart_743044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743044 prefixEnd_743044 := by exact prefixLift 743044
  have htrace : WordTrace (prefixWord ++ tailWord_743044) baseStart_743044 baseEnd_743044 := by
    simpa [prefixWord, tailWord_743044, baseEnd_743044] using wordTrace_append hprefix tailTrace_743044
  have hstable : (prefixWord ++ tailWord_743044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743044).length < 2 ^ (prefixWord ++ tailWord_743044).sum := by decide
  have hdescent : baseEnd_743044 < baseStart_743044 := by decide
  rcases family_descends (prefixWord ++ tailWord_743044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743126 : List Nat := [5, 2, 1, 3, 1, 1, 1, 4, 3]
def baseStart_743126 : Nat := 118140960795 + 743126 * 2 ^ 59
def prefixEnd_743126 : Nat := 4983230072969 + 3 ^ 40 * 743126 * 2
def baseEnd_743126 : Nat := 169591477712517666581081

theorem tailTrace_743126 : CollatzResearch.WordTrace tailWord_743126 prefixEnd_743126 169591477712517666581081 := by
  unfold tailWord_743126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1694001994111805791351577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18069354603859261774416821 1694001994111805791351577)
  ·
    refine ⟨1270501495583854343513683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1694001994111805791351577 1270501495583854343513683)
    ·
      refine ⟨1905752243375781515270525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1270501495583854343513683 1905752243375781515270525)
      ·
        refine ⟨714657091265918068226447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1905752243375781515270525 714657091265918068226447)
        ·
          refine ⟨1071985636898877102339671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 714657091265918068226447 1071985636898877102339671)
          ·
            refine ⟨1607978455348315653509507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1071985636898877102339671 1607978455348315653509507)
            ·
              refine ⟨2411967683022473480264261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607978455348315653509507 2411967683022473480264261)
              ·
                refine ⟨452243940566713777549549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2411967683022473480264261 452243940566713777549549)
                ·
                  refine ⟨169591477712517666581081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 452243940566713777549549 169591477712517666581081)
                  ·
                    rfl

theorem cell21_743126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_743126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743126 prefixEnd_743126 := by exact prefixLift 743126
  have htrace : WordTrace (prefixWord ++ tailWord_743126) baseStart_743126 baseEnd_743126 := by
    simpa [prefixWord, tailWord_743126, baseEnd_743126] using wordTrace_append hprefix tailTrace_743126
  have hstable : (prefixWord ++ tailWord_743126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743126).length < 2 ^ (prefixWord ++ tailWord_743126).sum := by decide
  have hdescent : baseEnd_743126 < baseStart_743126 := by decide
  rcases family_descends (prefixWord ++ tailWord_743126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743137 : List Nat := [1, 2, 3, 1, 6, 1, 1, 6]
def baseStart_743137 : Nat := 118140960795 + 743137 * 2 ^ 59
def prefixEnd_743137 : Nat := 4983230072969 + 3 ^ 40 * 743137 * 2
def baseEnd_743137 : Nat := 56531329354128030632575

theorem tailTrace_743137 : CollatzResearch.WordTrace tailWord_743137 prefixEnd_743137 56531329354128030632575 := by
  unfold tailWord_743137
  simp only [CollatzResearch.WordTrace]
  refine ⟨27104433108749041540275665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18069622072499361026850443 27104433108749041540275665)
  ·
    refine ⟨20328324831561781155206749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27104433108749041540275665 20328324831561781155206749)
    ·
      refine ⟨7623121811835667933202531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20328324831561781155206749 7623121811835667933202531)
      ·
        refine ⟨11434682717753501899803797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7623121811835667933202531 11434682717753501899803797)
        ·
          refine ⟨536000752394695401553303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11434682717753501899803797 536000752394695401553303)
          ·
            refine ⟨804001128592043102329955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536000752394695401553303 804001128592043102329955)
            ·
              refine ⟨1206001692888064653494933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804001128592043102329955 1206001692888064653494933)
              ·
                refine ⟨56531329354128030632575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1206001692888064653494933 56531329354128030632575)
                ·
                  rfl

theorem cell21_743137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 6].length) (baseStart_743137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743137 prefixEnd_743137 := by exact prefixLift 743137
  have htrace : WordTrace (prefixWord ++ tailWord_743137) baseStart_743137 baseEnd_743137 := by
    simpa [prefixWord, tailWord_743137, baseEnd_743137] using wordTrace_append hprefix tailTrace_743137
  have hstable : (prefixWord ++ tailWord_743137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743137).length < 2 ^ (prefixWord ++ tailWord_743137).sum := by decide
  have hdescent : baseEnd_743137 < baseStart_743137 := by decide
  rcases family_descends (prefixWord ++ tailWord_743137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743224 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 6]
def baseStart_743224 : Nat := 118140960795 + 743224 * 2 ^ 59
def prefixEnd_743224 : Nat := 4983230072969 + 3 ^ 40 * 743224 * 2
def baseEnd_743224 : Nat := 169613842647691273947547

theorem tailTrace_743224 : CollatzResearch.WordTrace tailWord_743224 prefixEnd_743224 169613842647691273947547 := by
  unfold tailWord_743224
  simp only [CollatzResearch.WordTrace]
  refine ⟨13553803129716927699346363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18071737506289236932461817 13553803129716927699346363)
  ·
    refine ⟨20330704694575391549019545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13553803129716927699346363 20330704694575391549019545)
    ·
      refine ⟨15248028520931543661764659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20330704694575391549019545 15248028520931543661764659)
      ·
        refine ⟨22872042781397315492646989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15248028520931543661764659 22872042781397315492646989)
        ·
          refine ⟨8577016043023993309742621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22872042781397315492646989 8577016043023993309742621)
          ·
            refine ⟨3216381016133997491153483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8577016043023993309742621 3216381016133997491153483)
            ·
              refine ⟨4824571524200996236730225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3216381016133997491153483 4824571524200996236730225)
              ·
                refine ⟨3618428643150747177547669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4824571524200996236730225 3618428643150747177547669)
                ·
                  refine ⟨169613842647691273947547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3618428643150747177547669 169613842647691273947547)
                  ·
                    rfl

theorem cell21_743224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_743224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743224 prefixEnd_743224 := by exact prefixLift 743224
  have htrace : WordTrace (prefixWord ++ tailWord_743224) baseStart_743224 baseEnd_743224 := by
    simpa [prefixWord, tailWord_743224, baseEnd_743224] using wordTrace_append hprefix tailTrace_743224
  have hstable : (prefixWord ++ tailWord_743224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743224).length < 2 ^ (prefixWord ++ tailWord_743224).sum := by decide
  have hdescent : baseEnd_743224 < baseStart_743224 := by decide
  rcases family_descends (prefixWord ++ tailWord_743224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743244 : List Nat := [2, 2, 1, 3, 5, 1, 1, 1, 5]
def baseStart_743244 : Nat := 118140960795 + 743244 * 2 ^ 59
def prefixEnd_743244 : Nat := 4983230072969 + 3 ^ 40 * 743244 * 2
def baseEnd_743244 : Nat := 169618406920175683614173

theorem tailTrace_743244 : CollatzResearch.WordTrace tailWord_743244 prefixEnd_743244 169618406920175683614173 := by
  unfold tailWord_743244
  simp only [CollatzResearch.WordTrace]
  refine ⟨13554167859680699407210393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18072223812907599209613857 13554167859680699407210393)
  ·
    refine ⟨10165625894760524555407795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13554167859680699407210393 10165625894760524555407795)
    ·
      refine ⟨15248438842140786833111693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10165625894760524555407795 15248438842140786833111693)
      ·
        refine ⟨5718164565802795062416885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15248438842140786833111693 5718164565802795062416885)
        ·
          refine ⟨536077928044012037101583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5718164565802795062416885 536077928044012037101583)
          ·
            refine ⟨804116892066018055652375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536077928044012037101583 804116892066018055652375)
            ·
              refine ⟨1206175338099027083478563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804116892066018055652375 1206175338099027083478563)
              ·
                refine ⟨1809263007148540625217845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1206175338099027083478563 1809263007148540625217845)
                ·
                  refine ⟨169618406920175683614173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1809263007148540625217845 169618406920175683614173)
                  ·
                    rfl

theorem cell21_743244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 5].length) (baseStart_743244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743244 prefixEnd_743244 := by exact prefixLift 743244
  have htrace : WordTrace (prefixWord ++ tailWord_743244) baseStart_743244 baseEnd_743244 := by
    simpa [prefixWord, tailWord_743244, baseEnd_743244] using wordTrace_append hprefix tailTrace_743244
  have hstable : (prefixWord ++ tailWord_743244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743244).length < 2 ^ (prefixWord ++ tailWord_743244).sum := by decide
  have hdescent : baseEnd_743244 < baseStart_743244 := by decide
  rcases family_descends (prefixWord ++ tailWord_743244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743269 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 7]
def baseStart_743269 : Nat := 118140960795 + 743269 * 2 ^ 59
def prefixEnd_743269 : Nat := 4983230072969 + 3 ^ 40 * 743269 * 2
def baseEnd_743269 : Nat := 169624112260781195697455

theorem tailTrace_743269 : CollatzResearch.WordTrace tailWord_743269 prefixEnd_743269 169624112260781195697455 := by
  unfold tailWord_743269
  simp only [CollatzResearch.WordTrace]
  refine ⟨27109247544270828084080861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18072831696180552056053907 27109247544270828084080861)
  ·
    refine ⟨10165967829101560531530323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27109247544270828084080861 10165967829101560531530323)
    ·
      refine ⟨15248951743652340797295485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10165967829101560531530323 15248951743652340797295485)
      ·
        refine ⟨5718356903869627798985807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15248951743652340797295485 5718356903869627798985807)
        ·
          refine ⟨8577535355804441698478711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5718356903869627798985807 8577535355804441698478711)
          ·
            refine ⟨12866303033706662547718067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8577535355804441698478711 12866303033706662547718067)
            ·
              refine ⟨19299454550559993821577101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12866303033706662547718067 19299454550559993821577101)
              ·
                refine ⟨7237295456459997683091413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19299454550559993821577101 7237295456459997683091413)
                ·
                  refine ⟨169624112260781195697455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7237295456459997683091413 169624112260781195697455)
                  ·
                    rfl

theorem cell21_743269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_743269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743269 prefixEnd_743269 := by exact prefixLift 743269
  have htrace : WordTrace (prefixWord ++ tailWord_743269) baseStart_743269 baseEnd_743269 := by
    simpa [prefixWord, tailWord_743269, baseEnd_743269] using wordTrace_append hprefix tailTrace_743269
  have hstable : (prefixWord ++ tailWord_743269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743269).length < 2 ^ (prefixWord ++ tailWord_743269).sum := by decide
  have hdescent : baseEnd_743269 < baseStart_743269 := by decide
  rcases family_descends (prefixWord ++ tailWord_743269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743300 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 6]
def baseStart_743300 : Nat := 118140960795 + 743300 * 2 ^ 59
def prefixEnd_743300 : Nat := 4983230072969 + 3 ^ 40 * 743300 * 2
def baseEnd_743300 : Nat := 169631186883132030680725

theorem tailTrace_743300 : CollatzResearch.WordTrace tailWord_743300 prefixEnd_743300 169631186883132030680725 := by
  unfold tailWord_743300
  simp only [CollatzResearch.WordTrace]
  refine ⟨13555189103579260189229677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18073585471439013585639569 13555189103579260189229677)
  ·
    refine ⟨5083195913842222570961129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13555189103579260189229677 5083195913842222570961129)
    ·
      refine ⟨3812396935381666928220847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5083195913842222570961129 3812396935381666928220847)
      ·
        refine ⟨5718595403072500392331271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3812396935381666928220847 5718595403072500392331271)
        ·
          refine ⟨8577893104608750588496907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5718595403072500392331271 8577893104608750588496907)
          ·
            refine ⟨12866839656913125882745361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8577893104608750588496907 12866839656913125882745361)
            ·
              refine ⟨9650129742684844412059021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12866839656913125882745361 9650129742684844412059021)
              ·
                refine ⟨3618798653506816654522133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9650129742684844412059021 3618798653506816654522133)
                ·
                  refine ⟨169631186883132030680725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3618798653506816654522133 169631186883132030680725)
                  ·
                    rfl

theorem cell21_743300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_743300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743300 prefixEnd_743300 := by exact prefixLift 743300
  have htrace : WordTrace (prefixWord ++ tailWord_743300) baseStart_743300 baseEnd_743300 := by
    simpa [prefixWord, tailWord_743300, baseEnd_743300] using wordTrace_append hprefix tailTrace_743300
  have hstable : (prefixWord ++ tailWord_743300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743300).length < 2 ^ (prefixWord ++ tailWord_743300).sum := by decide
  have hdescent : baseEnd_743300 < baseStart_743300 := by decide
  rcases family_descends (prefixWord ++ tailWord_743300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743376 : List Nat := [2, 1, 1, 1, 1, 2, 4, 5, 4]
def baseStart_743376 : Nat := 118140960795 + 743376 * 2 ^ 59
def prefixEnd_743376 : Nat := 4983230072969 + 3 ^ 40 * 743376 * 2
def baseEnd_743376 : Nat := 169648531118572787413903

theorem tailTrace_743376 : CollatzResearch.WordTrace tailWord_743376 prefixEnd_743376 169648531118572787413903 := by
  unfold tailWord_743376
  simp only [CollatzResearch.WordTrace]
  refine ⟨13556575077441592679112991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18075433436588790238817321 13556575077441592679112991)
  ·
    refine ⟨20334862616162389018669487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13556575077441592679112991 20334862616162389018669487)
    ·
      refine ⟨30502293924243583528004231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20334862616162389018669487 30502293924243583528004231)
      ·
        refine ⟨45753440886365375292006347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30502293924243583528004231 45753440886365375292006347)
        ·
          refine ⟨68630161329548062938009521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45753440886365375292006347 68630161329548062938009521)
          ·
            refine ⟨51472620997161047203507141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68630161329548062938009521 51472620997161047203507141)
            ·
              refine ⟨9651116436967696350657589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51472620997161047203507141 9651116436967696350657589)
              ·
                refine ⟨904792165965721532874149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9651116436967696350657589 904792165965721532874149)
                ·
                  refine ⟨169648531118572787413903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 904792165965721532874149 169648531118572787413903)
                  ·
                    rfl

theorem cell21_743376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 4].length) (baseStart_743376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743376 prefixEnd_743376 := by exact prefixLift 743376
  have htrace : WordTrace (prefixWord ++ tailWord_743376) baseStart_743376 baseEnd_743376 := by
    simpa [prefixWord, tailWord_743376, baseEnd_743376] using wordTrace_append hprefix tailTrace_743376
  have hstable : (prefixWord ++ tailWord_743376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743376).length < 2 ^ (prefixWord ++ tailWord_743376).sum := by decide
  have hdescent : baseEnd_743376 < baseStart_743376 := by decide
  rcases family_descends (prefixWord ++ tailWord_743376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743382 : List Nat := [5, 2, 1, 1, 3, 2, 2, 5]
def baseStart_743382 : Nat := 118140960795 + 743382 * 2 ^ 59
def prefixEnd_743382 : Nat := 4983230072969 + 3 ^ 40 * 743382 * 2
def baseEnd_743382 : Nat := 56549966800106036771297

theorem tailTrace_743382 : CollatzResearch.WordTrace tailWord_743382 prefixEnd_743382 56549966800106036771297 := by
  unfold tailWord_743382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1694585562053840523934025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18075579328574298921962933 1694585562053840523934025)
  ·
    refine ⟨1270939171540380392950519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1694585562053840523934025 1270939171540380392950519)
    ·
      refine ⟨1906408757310570589425779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1270939171540380392950519 1906408757310570589425779)
      ·
        refine ⟨2859613135965855884138669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1906408757310570589425779 2859613135965855884138669)
        ·
          refine ⟨1072354925987195956552001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2859613135965855884138669 1072354925987195956552001)
          ·
            refine ⟨804266194490396967414001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1072354925987195956552001 804266194490396967414001)
            ·
              refine ⟨603199645867797725560501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 804266194490396967414001 603199645867797725560501)
              ·
                refine ⟨56549966800106036771297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 603199645867797725560501 56549966800106036771297)
                ·
                  rfl

theorem cell21_743382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_743382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743382 prefixEnd_743382 := by exact prefixLift 743382
  have htrace : WordTrace (prefixWord ++ tailWord_743382) baseStart_743382 baseEnd_743382 := by
    simpa [prefixWord, tailWord_743382, baseEnd_743382] using wordTrace_append hprefix tailTrace_743382
  have hstable : (prefixWord ++ tailWord_743382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743382).length < 2 ^ (prefixWord ++ tailWord_743382).sum := by decide
  have hdescent : baseEnd_743382 < baseStart_743382 := by decide
  rcases family_descends (prefixWord ++ tailWord_743382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743472 : List Nat := [2, 1, 1, 1, 2, 7, 2, 2, 3]
def baseStart_743472 : Nat := 118140960795 + 743472 * 2 ^ 59
def prefixEnd_743472 : Nat := 4983230072969 + 3 ^ 40 * 743472 * 2
def baseEnd_743472 : Nat := 169670439626497953813707

theorem tailTrace_743472 : CollatzResearch.WordTrace tailWord_743472 prefixEnd_743472 169670439626497953813707 := by
  unfold tailWord_743472
  simp only [CollatzResearch.WordTrace]
  refine ⟨13558325781267696876860335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18077767708356929169147113 13558325781267696876860335)
  ·
    refine ⟨20337488671901545315290503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13558325781267696876860335 20337488671901545315290503)
    ·
      refine ⟨30506233007852317972935755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20337488671901545315290503 30506233007852317972935755)
      ·
        refine ⟨45759349511778476959403633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30506233007852317972935755 45759349511778476959403633)
        ·
          refine ⟨34319512133833857719552725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45759349511778476959403633 34319512133833857719552725)
          ·
            refine ⟨804363565636731040302017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 34319512133833857719552725 804363565636731040302017)
            ·
              refine ⟨603272674227548280226513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 804363565636731040302017 603272674227548280226513)
              ·
                refine ⟨452454505670661210169885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 603272674227548280226513 452454505670661210169885)
                ·
                  refine ⟨169670439626497953813707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 452454505670661210169885 169670439626497953813707)
                  ·
                    rfl

theorem cell21_743472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 3].length) (baseStart_743472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743472 prefixEnd_743472 := by exact prefixLift 743472
  have htrace : WordTrace (prefixWord ++ tailWord_743472) baseStart_743472 baseEnd_743472 := by
    simpa [prefixWord, tailWord_743472, baseEnd_743472] using wordTrace_append hprefix tailTrace_743472
  have hstable : (prefixWord ++ tailWord_743472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743472).length < 2 ^ (prefixWord ++ tailWord_743472).sum := by decide
  have hdescent : baseEnd_743472 < baseStart_743472 := by decide
  rcases family_descends (prefixWord ++ tailWord_743472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743497 : List Nat := [1, 2, 1, 1, 2, 2, 5, 2, 5]
def baseStart_743497 : Nat := 118140960795 + 743497 * 2 ^ 59
def prefixEnd_743497 : Nat := 4983230072969 + 3 ^ 40 * 743497 * 2
def baseEnd_743497 : Nat := 169676144967103465896989

theorem tailTrace_743497 : CollatzResearch.WordTrace tailWord_743497 prefixEnd_743497 169676144967103465896989 := by
  unfold tailWord_743497
  simp only [CollatzResearch.WordTrace]
  refine ⟨27117563387444823023380745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18078375591629882015587163 27117563387444823023380745)
  ·
    refine ⟨20338172540583617267535559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27117563387444823023380745 20338172540583617267535559)
    ·
      refine ⟨30507258810875425901303339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20338172540583617267535559 30507258810875425901303339)
      ·
        refine ⟨45760888216313138851955009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30507258810875425901303339 45760888216313138851955009)
        ·
          refine ⟨34320666162234854138966257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45760888216313138851955009 34320666162234854138966257)
          ·
            refine ⟨25740499621676140604224693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34320666162234854138966257 25740499621676140604224693)
            ·
              refine ⟨2413171839532138181646065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25740499621676140604224693 2413171839532138181646065)
              ·
                refine ⟨1809878879649103636234549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2413171839532138181646065 1809878879649103636234549)
                ·
                  refine ⟨169676144967103465896989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1809878879649103636234549 169676144967103465896989)
                  ·
                    rfl

theorem cell21_743497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_743497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743497 prefixEnd_743497 := by exact prefixLift 743497
  have htrace : WordTrace (prefixWord ++ tailWord_743497) baseStart_743497 baseEnd_743497 := by
    simpa [prefixWord, tailWord_743497, baseEnd_743497] using wordTrace_append hprefix tailTrace_743497
  have hstable : (prefixWord ++ tailWord_743497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743497).length < 2 ^ (prefixWord ++ tailWord_743497).sum := by decide
  have hdescent : baseEnd_743497 < baseStart_743497 := by decide
  rcases family_descends (prefixWord ++ tailWord_743497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743559 : List Nat := [1, 1, 4, 2, 1, 1, 6, 5]
def baseStart_743559 : Nat := 118140960795 + 743559 * 2 ^ 59
def prefixEnd_743559 : Nat := 4983230072969 + 3 ^ 40 * 743559 * 2
def baseEnd_743559 : Nat := 56563431403935045287843

theorem tailTrace_743559 : CollatzResearch.WordTrace tailWord_743559 prefixEnd_743559 56563431403935045287843 := by
  unfold tailWord_743559
  simp only [CollatzResearch.WordTrace]
  refine ⟨27119824713220207612137731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18079883142146805074758487 27119824713220207612137731)
  ·
    refine ⟨40679737069830311418206597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27119824713220207612137731 40679737069830311418206597)
    ·
      refine ⟨7627450700593183390913737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40679737069830311418206597 7627450700593183390913737)
      ·
        refine ⟨5720588025444887543185303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7627450700593183390913737 5720588025444887543185303)
        ·
          refine ⟨8580882038167331314777955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5720588025444887543185303 8580882038167331314777955)
          ·
            refine ⟨12871323057250996972166933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8580882038167331314777955 12871323057250996972166933)
            ·
              refine ⟨603343268308640483070325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12871323057250996972166933 603343268308640483070325)
              ·
                refine ⟨56563431403935045287843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 603343268308640483070325 56563431403935045287843)
                ·
                  rfl

theorem cell21_743559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 5].length) (baseStart_743559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743559 prefixEnd_743559 := by exact prefixLift 743559
  have htrace : WordTrace (prefixWord ++ tailWord_743559) baseStart_743559 baseEnd_743559 := by
    simpa [prefixWord, tailWord_743559, baseEnd_743559] using wordTrace_append hprefix tailTrace_743559
  have hstable : (prefixWord ++ tailWord_743559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743559).length < 2 ^ (prefixWord ++ tailWord_743559).sum := by decide
  have hdescent : baseEnd_743559 < baseStart_743559 := by decide
  rcases family_descends (prefixWord ++ tailWord_743559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743576 : List Nat := [2, 1, 2, 4, 4, 1, 7]
def baseStart_743576 : Nat := 118140960795 + 743576 * 2 ^ 59
def prefixEnd_743576 : Nat := 4983230072969 + 3 ^ 40 * 743576 * 2
def baseEnd_743576 : Nat := 18854908204824098231129

theorem tailTrace_743576 : CollatzResearch.WordTrace tailWord_743576 prefixEnd_743576 18854908204824098231129 := by
  unfold tailWord_743576
  simp only [CollatzResearch.WordTrace]
  refine ⟨13560222377079309757753291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18080296502772413010337721 13560222377079309757753291)
  ·
    refine ⟨20340333565618964636629937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13560222377079309757753291 20340333565618964636629937)
    ·
      refine ⟨15255250174214223477472453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20340333565618964636629937 15255250174214223477472453)
      ·
        refine ⟨2860359407665166902026085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15255250174214223477472453 2860359407665166902026085)
        ·
          refine ⟨536317388937218794129891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2860359407665166902026085 536317388937218794129891)
          ·
            refine ⟨804476083405828191194837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536317388937218794129891 804476083405828191194837)
            ·
              refine ⟨18854908204824098231129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 804476083405828191194837 18854908204824098231129)
              ·
                rfl

theorem cell21_743576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 7].length) (baseStart_743576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743576 prefixEnd_743576 := by exact prefixLift 743576
  have htrace : WordTrace (prefixWord ++ tailWord_743576) baseStart_743576 baseEnd_743576 := by
    simpa [prefixWord, tailWord_743576, baseEnd_743576] using wordTrace_append hprefix tailTrace_743576
  have hstable : (prefixWord ++ tailWord_743576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743576).length < 2 ^ (prefixWord ++ tailWord_743576).sum := by decide
  have hdescent : baseEnd_743576 < baseStart_743576 := by decide
  rcases family_descends (prefixWord ++ tailWord_743576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743638 : List Nat := [5, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_743638 : Nat := 118140960795 + 743638 * 2 ^ 59
def prefixEnd_743638 : Nat := 4983230072969 + 3 ^ 40 * 743638 * 2
def baseEnd_743638 : Nat := 169708323088118554046701

theorem tailTrace_743638 : CollatzResearch.WordTrace tailWord_743638 prefixEnd_743638 169708323088118554046701 := by
  unfold tailWord_743638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1695169129995875256516473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18081804053289336069509045 1695169129995875256516473)
  ·
    refine ⟨1271376847496906442387355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1695169129995875256516473 1271376847496906442387355)
    ·
      refine ⟨1907065271245359663581033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1271376847496906442387355 1907065271245359663581033)
      ·
        refine ⟨1430298953434019747685775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1907065271245359663581033 1430298953434019747685775)
        ·
          refine ⟨2145448430151029621528663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1430298953434019747685775 2145448430151029621528663)
          ·
            refine ⟨3218172645226544432292995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2145448430151029621528663 3218172645226544432292995)
            ·
              refine ⟨4827258967839816648439493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3218172645226544432292995 4827258967839816648439493)
              ·
                refine ⟨905111056469965621582405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4827258967839816648439493 905111056469965621582405)
                ·
                  refine ⟨169708323088118554046701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 905111056469965621582405 169708323088118554046701)
                  ·
                    rfl

theorem cell21_743638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_743638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743638 prefixEnd_743638 := by exact prefixLift 743638
  have htrace : WordTrace (prefixWord ++ tailWord_743638) baseStart_743638 baseEnd_743638 := by
    simpa [prefixWord, tailWord_743638, baseEnd_743638] using wordTrace_append hprefix tailTrace_743638
  have hstable : (prefixWord ++ tailWord_743638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743638).length < 2 ^ (prefixWord ++ tailWord_743638).sum := by decide
  have hdescent : baseEnd_743638 < baseStart_743638 := by decide
  rcases family_descends (prefixWord ++ tailWord_743638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743649 : List Nat := [1, 2, 3, 1, 3, 1, 2, 3, 5]
def baseStart_743649 : Nat := 118140960795 + 743649 * 2 ^ 59
def prefixEnd_743649 : Nat := 4983230072969 + 3 ^ 40 * 743649 * 2
def baseEnd_743649 : Nat := 169710833437984979363345

theorem tailTrace_743649 : CollatzResearch.WordTrace tailWord_743649 prefixEnd_743649 169710833437984979363345 := by
  unfold tailWord_743649
  simp only [CollatzResearch.WordTrace]
  refine ⟨27123107282894152982914001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18082071521929435321942667 27123107282894152982914001)
  ·
    refine ⟨20342330462170614737185501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27123107282894152982914001 20342330462170614737185501)
    ·
      refine ⟨7628373923313980526444563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20342330462170614737185501 7628373923313980526444563)
      ·
        refine ⟨11442560884970970789666845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7628373923313980526444563 11442560884970970789666845)
        ·
          refine ⟨4290960331864114046125067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11442560884970970789666845 4290960331864114046125067)
          ·
            refine ⟨6436440497796171069187601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4290960331864114046125067 6436440497796171069187601)
            ·
              refine ⟨4827330373347128301890701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6436440497796171069187601 4827330373347128301890701)
              ·
                refine ⟨1810248890005173113209013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4827330373347128301890701 1810248890005173113209013)
                ·
                  refine ⟨169710833437984979363345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1810248890005173113209013 169710833437984979363345)
                  ·
                    rfl

theorem cell21_743649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_743649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743649 prefixEnd_743649 := by exact prefixLift 743649
  have htrace : WordTrace (prefixWord ++ tailWord_743649) baseStart_743649 baseEnd_743649 := by
    simpa [prefixWord, tailWord_743649, baseEnd_743649] using wordTrace_append hprefix tailTrace_743649
  have hstable : (prefixWord ++ tailWord_743649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743649).length < 2 ^ (prefixWord ++ tailWord_743649).sum := by decide
  have hdescent : baseEnd_743649 < baseStart_743649 := by decide
  rcases family_descends (prefixWord ++ tailWord_743649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743666 : List Nat := [3, 2, 1, 3, 2, 2, 1, 2, 5]
def baseStart_743666 : Nat := 118140960795 + 743666 * 2 ^ 59
def prefixEnd_743666 : Nat := 4983230072969 + 3 ^ 40 * 743666 * 2
def baseEnd_743666 : Nat := 169714713069596727579977

theorem tailTrace_743666 : CollatzResearch.WordTrace tailWord_743666 prefixEnd_743666 169714713069596727579977 := by
  unfold tailWord_743666
  simp only [CollatzResearch.WordTrace]
  refine ⟨6780931830958141221570713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18082484882555043257521901 6780931830958141221570713)
  ·
    refine ⟨5085698873218605916178035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6780931830958141221570713 5085698873218605916178035)
    ·
      refine ⟨7628548309827908874267053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5085698873218605916178035 7628548309827908874267053)
      ·
        refine ⟨2860705616185465827850145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7628548309827908874267053 2860705616185465827850145)
        ·
          refine ⟨2145529212139099370887609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2860705616185465827850145 2145529212139099370887609)
          ·
            refine ⟨1609146909104324528165707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2145529212139099370887609 1609146909104324528165707)
            ·
              refine ⟨2413720363656486792248561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609146909104324528165707 2413720363656486792248561)
              ·
                refine ⟨1810290272742365094186421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2413720363656486792248561 1810290272742365094186421)
                ·
                  refine ⟨169714713069596727579977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1810290272742365094186421 169714713069596727579977)
                  ·
                    rfl

theorem cell21_743666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_743666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743666 prefixEnd_743666 := by exact prefixLift 743666
  have htrace : WordTrace (prefixWord ++ tailWord_743666) baseStart_743666 baseEnd_743666 := by
    simpa [prefixWord, tailWord_743666, baseEnd_743666] using wordTrace_append hprefix tailTrace_743666
  have hstable : (prefixWord ++ tailWord_743666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743666).length < 2 ^ (prefixWord ++ tailWord_743666).sum := by decide
  have hdescent : baseEnd_743666 < baseStart_743666 := by decide
  rcases family_descends (prefixWord ++ tailWord_743666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743694 : List Nat := [4, 1, 1, 2, 1, 2, 10]
def baseStart_743694 : Nat := 118140960795 + 743694 * 2 ^ 59
def prefixEnd_743694 : Nat := 4983230072969 + 3 ^ 40 * 743694 * 2
def baseEnd_743694 : Nat := 18857900339008322345917

theorem tailTrace_743694 : CollatzResearch.WordTrace tailWord_743694 prefixEnd_743694 18857900339008322345917 := by
  unfold tailWord_743694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3390593570966390708537767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18083165711820750445534757 3390593570966390708537767)
  ·
    refine ⟨5085890356449586062806651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3390593570966390708537767 5085890356449586062806651)
    ·
      refine ⟨7628835534674379094209977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5085890356449586062806651 7628835534674379094209977)
      ·
        refine ⟨5721626651005784320657483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7628835534674379094209977 5721626651005784320657483)
        ·
          refine ⟨8582439976508676480986225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5721626651005784320657483 8582439976508676480986225)
          ·
            refine ⟨6436829982381507360739669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8582439976508676480986225 6436829982381507360739669)
            ·
              refine ⟨18857900339008322345917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6436829982381507360739669 18857900339008322345917)
              ·
                rfl

theorem cell21_743694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 10].length) (baseStart_743694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743694 prefixEnd_743694 := by exact prefixLift 743694
  have htrace : WordTrace (prefixWord ++ tailWord_743694) baseStart_743694 baseEnd_743694 := by
    simpa [prefixWord, tailWord_743694, baseEnd_743694] using wordTrace_append hprefix tailTrace_743694
  have hstable : (prefixWord ++ tailWord_743694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743694).length < 2 ^ (prefixWord ++ tailWord_743694).sum := by decide
  have hdescent : baseEnd_743694 < baseStart_743694 := by decide
  rcases family_descends (prefixWord ++ tailWord_743694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743697 : List Nat := [1, 2, 2, 1, 1, 7, 1, 2, 4]
def baseStart_743697 : Nat := 118140960795 + 743697 * 2 ^ 59
def prefixEnd_743697 : Nat := 4983230072969 + 3 ^ 40 * 743697 * 2
def baseEnd_743697 : Nat := 169721787691947562563247

theorem tailTrace_743697 : CollatzResearch.WordTrace tailWord_743697 prefixEnd_743697 169721787691947562563247 := by
  unfold tailWord_743697
  simp only [CollatzResearch.WordTrace]
  refine ⟨27124857986720257180661345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18083238657813504787107563 27124857986720257180661345)
  ·
    refine ⟨20343643490040192885496009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27124857986720257180661345 20343643490040192885496009)
    ·
      refine ⟨15257732617530144664122007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20343643490040192885496009 15257732617530144664122007)
      ·
        refine ⟨22886598926295216996183011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15257732617530144664122007 22886598926295216996183011)
        ·
          refine ⟨34329898389442825494274517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22886598926295216996183011 34329898389442825494274517)
          ·
            refine ⟨804606993502566222522059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 34329898389442825494274517 804606993502566222522059)
            ·
              refine ⟨1206910490253849333783089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804606993502566222522059 1206910490253849333783089)
              ·
                refine ⟨905182867690387000337317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1206910490253849333783089 905182867690387000337317)
                ·
                  refine ⟨169721787691947562563247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 905182867690387000337317 169721787691947562563247)
                  ·
                    rfl

theorem cell21_743697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 4].length) (baseStart_743697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743697 prefixEnd_743697 := by exact prefixLift 743697
  have htrace : WordTrace (prefixWord ++ tailWord_743697) baseStart_743697 baseEnd_743697 := by
    simpa [prefixWord, tailWord_743697, baseEnd_743697] using wordTrace_append hprefix tailTrace_743697
  have hstable : (prefixWord ++ tailWord_743697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743697).length < 2 ^ (prefixWord ++ tailWord_743697).sum := by decide
  have hdescent : baseEnd_743697 < baseStart_743697 := by decide
  rcases family_descends (prefixWord ++ tailWord_743697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743714 : List Nat := [3, 3, 1, 1, 3, 2, 3, 1, 4]
def baseStart_743714 : Nat := 118140960795 + 743714 * 2 ^ 59
def prefixEnd_743714 : Nat := 4983230072969 + 3 ^ 40 * 743714 * 2
def baseEnd_743714 : Nat := 169725667323559310779879

theorem tailTrace_743714 : CollatzResearch.WordTrace tailWord_743714 prefixEnd_743714 169725667323559310779879 := by
  unfold tailWord_743714
  simp only [CollatzResearch.WordTrace]
  refine ⟨6781369506914667271007549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18083652018439112722686797 6781369506914667271007549)
  ·
    refine ⟨2543013565093000226627831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6781369506914667271007549 2543013565093000226627831)
    ·
      refine ⟨3814520347639500339941747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2543013565093000226627831 3814520347639500339941747)
      ·
        refine ⟨5721780521459250509912621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3814520347639500339941747 5721780521459250509912621)
        ·
          refine ⟨2145667695547218941217233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5721780521459250509912621 2145667695547218941217233)
          ·
            refine ⟨1609250771660414205912925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2145667695547218941217233 1609250771660414205912925)
            ·
              refine ⟨603469039372655327217347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1609250771660414205912925 603469039372655327217347)
              ·
                refine ⟨905203559058982990826021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603469039372655327217347 905203559058982990826021)
                ·
                  refine ⟨169725667323559310779879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 905203559058982990826021 169725667323559310779879)
                  ·
                    rfl

theorem cell21_743714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_743714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743714 prefixEnd_743714 := by exact prefixLift 743714
  have htrace : WordTrace (prefixWord ++ tailWord_743714) baseStart_743714 baseEnd_743714 := by
    simpa [prefixWord, tailWord_743714, baseEnd_743714] using wordTrace_append hprefix tailTrace_743714
  have hstable : (prefixWord ++ tailWord_743714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743714).length < 2 ^ (prefixWord ++ tailWord_743714).sum := by decide
  have hdescent : baseEnd_743714 < baseStart_743714 := by decide
  rcases family_descends (prefixWord ++ tailWord_743714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743756 : List Nat := [2, 2, 1, 3, 2, 1, 2, 4, 4]
def baseStart_743756 : Nat := 118140960795 + 743756 * 2 ^ 59
def prefixEnd_743756 : Nat := 4983230072969 + 3 ^ 40 * 743756 * 2
def baseEnd_743756 : Nat := 169735252295776571079793

theorem tailTrace_743756 : CollatzResearch.WordTrace tailWord_743756 prefixEnd_743756 169735252295776571079793 := by
  unfold tailWord_743756
  simp only [CollatzResearch.WordTrace]
  refine ⟨13563504946753255128529561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18084673262337673504706081 13563504946753255128529561)
  ·
    refine ⟨10172628710064941346397171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13563504946753255128529561 10172628710064941346397171)
    ·
      refine ⟨15258943065097412019595757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10172628710064941346397171 15258943065097412019595757)
      ·
        refine ⟨5722103649411529507348409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15258943065097412019595757 5722103649411529507348409)
        ·
          refine ⟨4291577737058647130511307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5722103649411529507348409 4291577737058647130511307)
          ·
            refine ⟨6437366605587970695766961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4291577737058647130511307 6437366605587970695766961)
            ·
              refine ⟨4828024954190978021825221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6437366605587970695766961 4828024954190978021825221)
              ·
                refine ⟨905254678910808379092229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4828024954190978021825221 905254678910808379092229)
                ·
                  refine ⟨169735252295776571079793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 905254678910808379092229 169735252295776571079793)
                  ·
                    rfl

theorem cell21_743756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_743756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743756 prefixEnd_743756 := by exact prefixLift 743756
  have htrace : WordTrace (prefixWord ++ tailWord_743756) baseStart_743756 baseEnd_743756 := by
    simpa [prefixWord, tailWord_743756, baseEnd_743756] using wordTrace_append hprefix tailTrace_743756
  have hstable : (prefixWord ++ tailWord_743756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743756).length < 2 ^ (prefixWord ++ tailWord_743756).sum := by decide
  have hdescent : baseEnd_743756 < baseStart_743756 := by decide
  rcases family_descends (prefixWord ++ tailWord_743756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743810 : List Nat := [3, 4, 2, 1, 2, 2, 2, 2, 3]
def baseStart_743810 : Nat := 118140960795 + 743810 * 2 ^ 59
def prefixEnd_743810 : Nat := 4983230072969 + 3 ^ 40 * 743810 * 2
def baseEnd_743810 : Nat := 169747575831484477179683

theorem tailTrace_743810 : CollatzResearch.WordTrace tailWord_743810 prefixEnd_743810 169747575831484477179683 := by
  unfold tailWord_743810
  simp only [CollatzResearch.WordTrace]
  refine ⟨6782244858827719369881221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18085986290207251653016589 6782244858827719369881221)
  ·
    refine ⟨1271670911030197381852729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6782244858827719369881221 1271670911030197381852729)
    ·
      refine ⟨953753183272648036389547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1271670911030197381852729 953753183272648036389547)
      ·
        refine ⟨1430629774908972054584321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 953753183272648036389547 1430629774908972054584321)
        ·
          refine ⟨1072972331181729040938241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1430629774908972054584321 1072972331181729040938241)
          ·
            refine ⟨804729248386296780703681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1072972331181729040938241 804729248386296780703681)
            ·
              refine ⟨603546936289722585527761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 804729248386296780703681 603546936289722585527761)
              ·
                refine ⟨452660202217291939145821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 603546936289722585527761 452660202217291939145821)
                ·
                  refine ⟨169747575831484477179683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 452660202217291939145821 169747575831484477179683)
                  ·
                    rfl

theorem cell21_743810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_743810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743810 prefixEnd_743810 := by exact prefixLift 743810
  have htrace : WordTrace (prefixWord ++ tailWord_743810) baseStart_743810 baseEnd_743810 := by
    simpa [prefixWord, tailWord_743810, baseEnd_743810] using wordTrace_append hprefix tailTrace_743810
  have hstable : (prefixWord ++ tailWord_743810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743810).length < 2 ^ (prefixWord ++ tailWord_743810).sum := by decide
  have hdescent : baseEnd_743810 < baseStart_743810 := by decide
  rcases family_descends (prefixWord ++ tailWord_743810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743894 : List Nat := [5, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_743894 : Nat := 118140960795 + 743894 * 2 ^ 59
def prefixEnd_743894 : Nat := 4983230072969 + 3 ^ 40 * 743894 * 2
def baseEnd_743894 : Nat := 169766745775918997779511

theorem tailTrace_743894 : CollatzResearch.WordTrace tailWord_743894 prefixEnd_743894 169766745775918997779511 := by
  unfold tailWord_743894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1695752697937909989098921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18088028778004373217055157 1695752697937909989098921)
  ·
    refine ⟨1271814523453432491824191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1695752697937909989098921 1271814523453432491824191)
    ·
      refine ⟨1907721785180148737736287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1271814523453432491824191 1907721785180148737736287)
      ·
        refine ⟨2861582677770223106604431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1907721785180148737736287 2861582677770223106604431)
        ·
          refine ⟨4292374016655334659906647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2861582677770223106604431 4292374016655334659906647)
          ·
            refine ⟨6438561024983001989859971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4292374016655334659906647 6438561024983001989859971)
            ·
              refine ⟨9657841537474502984789957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6438561024983001989859971 9657841537474502984789957)
              ·
                refine ⟨1810845288276469309648117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9657841537474502984789957 1810845288276469309648117)
                ·
                  refine ⟨169766745775918997779511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1810845288276469309648117 169766745775918997779511)
                  ·
                    rfl

theorem cell21_743894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_743894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743894 prefixEnd_743894 := by exact prefixLift 743894
  have htrace : WordTrace (prefixWord ++ tailWord_743894) baseStart_743894 baseEnd_743894 := by
    simpa [prefixWord, tailWord_743894, baseEnd_743894] using wordTrace_append hprefix tailTrace_743894
  have hstable : (prefixWord ++ tailWord_743894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743894).length < 2 ^ (prefixWord ++ tailWord_743894).sum := by decide
  have hdescent : baseEnd_743894 < baseStart_743894 := by decide
  rcases family_descends (prefixWord ++ tailWord_743894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_743970 : List Nat := [3, 3, 1, 1, 1, 1, 1, 7, 3]
def baseStart_743970 : Nat := 118140960795 + 743970 * 2 ^ 59
def prefixEnd_743970 : Nat := 4983230072969 + 3 ^ 40 * 743970 * 2
def baseEnd_743970 : Nat := 169784090011359754512689

theorem tailTrace_743970 : CollatzResearch.WordTrace tailWord_743970 prefixEnd_743970 169784090011359754512689 := by
  unfold tailWord_743970
  simp only [CollatzResearch.WordTrace]
  refine ⟨6783703778682806201337341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18089876743154149870232909 6783703778682806201337341)
  ·
    refine ⟨2543888917006052325501503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6783703778682806201337341 2543888917006052325501503)
    ·
      refine ⟨3815833375509078488252255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2543888917006052325501503 3815833375509078488252255)
      ·
        refine ⟨5723750063263617732378383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3815833375509078488252255 5723750063263617732378383)
        ·
          refine ⟨8585625094895426598567575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5723750063263617732378383 8585625094895426598567575)
          ·
            refine ⟨12878437642343139897851363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8585625094895426598567575 12878437642343139897851363)
            ·
              refine ⟨19317656463514709846777045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12878437642343139897851363 19317656463514709846777045)
              ·
                refine ⟨452757573363626012033837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19317656463514709846777045 452757573363626012033837)
                ·
                  refine ⟨169784090011359754512689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 452757573363626012033837 169784090011359754512689)
                  ·
                    rfl

theorem cell21_743970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_743970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_743970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_743970 prefixEnd_743970 := by exact prefixLift 743970
  have htrace : WordTrace (prefixWord ++ tailWord_743970) baseStart_743970 baseEnd_743970 := by
    simpa [prefixWord, tailWord_743970, baseEnd_743970] using wordTrace_append hprefix tailTrace_743970
  have hstable : (prefixWord ++ tailWord_743970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_743970).length < 2 ^ (prefixWord ++ tailWord_743970).sum := by decide
  have hdescent : baseEnd_743970 < baseStart_743970 := by decide
  rcases family_descends (prefixWord ++ tailWord_743970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744004 : List Nat := [2, 3, 5, 1, 1, 1, 1, 2, 5]
def baseStart_744004 : Nat := 118140960795 + 744004 * 2 ^ 59
def prefixEnd_744004 : Nat := 4983230072969 + 3 ^ 40 * 744004 * 2
def baseEnd_744004 : Nat := 169791849274583250945953

theorem tailTrace_744004 : CollatzResearch.WordTrace tailWord_744004 prefixEnd_744004 169791849274583250945953 := by
  unfold tailWord_744004
  simp only [CollatzResearch.WordTrace]
  refine ⟨13568027598304024306043533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18090703464405365741391377 13568027598304024306043533)
  ·
    refine ⟨5088010349364009114766325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13568027598304024306043533 5088010349364009114766325)
    ·
      refine ⟨477000970252875854509343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5088010349364009114766325 477000970252875854509343)
      ·
        refine ⟨715501455379313781764015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 477000970252875854509343 715501455379313781764015)
        ·
          refine ⟨1073252183068970672646023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715501455379313781764015 1073252183068970672646023)
          ·
            refine ⟨1609878274603456008969035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1073252183068970672646023 1609878274603456008969035)
            ·
              refine ⟨2414817411905184013453553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609878274603456008969035 2414817411905184013453553)
              ·
                refine ⟨1811113058928888010090165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2414817411905184013453553 1811113058928888010090165)
                ·
                  refine ⟨169791849274583250945953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1811113058928888010090165 169791849274583250945953)
                  ·
                    rfl

theorem cell21_744004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_744004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_744004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_744004 prefixEnd_744004 := by exact prefixLift 744004
  have htrace : WordTrace (prefixWord ++ tailWord_744004) baseStart_744004 baseEnd_744004 := by
    simpa [prefixWord, tailWord_744004, baseEnd_744004] using wordTrace_append hprefix tailTrace_744004
  have hstable : (prefixWord ++ tailWord_744004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744004).length < 2 ^ (prefixWord ++ tailWord_744004).sum := by decide
  have hdescent : baseEnd_744004 < baseStart_744004 := by decide
  rcases family_descends (prefixWord ++ tailWord_744004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744043 : List Nat := [1, 1, 1, 1, 2, 2, 1, 8, 4]
def baseStart_744043 : Nat := 118140960795 + 744043 * 2 ^ 59
def prefixEnd_744043 : Nat := 4983230072969 + 3 ^ 40 * 744043 * 2
def baseEnd_744043 : Nat := 169800749605927849795873

theorem tailTrace_744043 : CollatzResearch.WordTrace tailWord_744043 prefixEnd_744043 169800749605927849795873 := by
  unfold tailWord_744043
  simp only [CollatzResearch.WordTrace]
  refine ⟨27137477643466758272756783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18091651762311172181837855 27137477643466758272756783)
  ·
    refine ⟨40706216465200137409135175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27137477643466758272756783 40706216465200137409135175)
    ·
      refine ⟨61059324697800206113702763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40706216465200137409135175 61059324697800206113702763)
      ·
        refine ⟨91588987046700309170554145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61059324697800206113702763 91588987046700309170554145)
        ·
          refine ⟨68691740285025231877915609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91588987046700309170554145 68691740285025231877915609)
          ·
            refine ⟨51518805213768923908436707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68691740285025231877915609 51518805213768923908436707)
            ·
              refine ⟨77278207820653385862655061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51518805213768923908436707 77278207820653385862655061)
              ·
                refine ⟨905603997898281865577989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 77278207820653385862655061 905603997898281865577989)
                ·
                  refine ⟨169800749605927849795873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 905603997898281865577989 169800749605927849795873)
                  ·
                    rfl

theorem cell21_744043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 4].length) (baseStart_744043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_744043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_744043 prefixEnd_744043 := by exact prefixLift 744043
  have htrace : WordTrace (prefixWord ++ tailWord_744043) baseStart_744043 baseEnd_744043 := by
    simpa [prefixWord, tailWord_744043, baseEnd_744043] using wordTrace_append hprefix tailTrace_744043
  have hstable : (prefixWord ++ tailWord_744043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744043).length < 2 ^ (prefixWord ++ tailWord_744043).sum := by decide
  have hdescent : baseEnd_744043 < baseStart_744043 := by decide
  rcases family_descends (prefixWord ++ tailWord_744043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744046 : List Nat := [4, 1, 2, 2, 2, 2, 2, 1, 5]
def baseStart_744046 : Nat := 118140960795 + 744046 * 2 ^ 59
def prefixEnd_744046 : Nat := 4983230072969 + 3 ^ 40 * 744046 * 2
def baseEnd_744046 : Nat := 169801434246800511245867

theorem tailTrace_744046 : CollatzResearch.WordTrace tailWord_744046 prefixEnd_744046 169801434246800511245867 := by
  unfold tailWord_744046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3392198382806986223139499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18091724708303926523410661 3392198382806986223139499)
  ·
    refine ⟨5088297574210479334709249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3392198382806986223139499 5088297574210479334709249)
    ·
      refine ⟨3816223180657859501031937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5088297574210479334709249 3816223180657859501031937)
      ·
        refine ⟨2862167385493394625773953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3816223180657859501031937 2862167385493394625773953)
        ·
          refine ⟨2146625539120045969330465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2862167385493394625773953 2146625539120045969330465)
          ·
            refine ⟨1609969154340034476997849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2146625539120045969330465 1609969154340034476997849)
            ·
              refine ⟨1207476865755025857748387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1609969154340034476997849 1207476865755025857748387)
              ·
                refine ⟨1811215298632538786622581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207476865755025857748387 1811215298632538786622581)
                ·
                  refine ⟨169801434246800511245867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1811215298632538786622581 169801434246800511245867)
                  ·
                    rfl

theorem cell21_744046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_744046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_744046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_744046 prefixEnd_744046 := by exact prefixLift 744046
  have htrace : WordTrace (prefixWord ++ tailWord_744046) baseStart_744046 baseEnd_744046 := by
    simpa [prefixWord, tailWord_744046, baseEnd_744046] using wordTrace_append hprefix tailTrace_744046
  have hstable : (prefixWord ++ tailWord_744046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744046).length < 2 ^ (prefixWord ++ tailWord_744046).sum := by decide
  have hdescent : baseEnd_744046 < baseStart_744046 := by decide
  rcases family_descends (prefixWord ++ tailWord_744046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744150 : List Nat := [5, 2, 1, 13]
def baseStart_744150 : Nat := 118140960795 + 744150 * 2 ^ 59
def prefixEnd_744150 : Nat := 4983230072969 + 3 ^ 40 * 744150 * 2
def baseEnd_744150 : Nat := 698869006023536796347

theorem tailTrace_744150 : CollatzResearch.WordTrace tailWord_744150 prefixEnd_744150 698869006023536796347 := by
  unfold tailWord_744150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1696336265879944721681369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18094253502719410364601269 1696336265879944721681369)
  ·
    refine ⟨1272252199409958541261027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1696336265879944721681369 1272252199409958541261027)
    ·
      refine ⟨1908378299114937811891541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1272252199409958541261027 1908378299114937811891541)
      ·
        refine ⟨698869006023536796347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 1908378299114937811891541 698869006023536796347)
        ·
          rfl

theorem cell21_744150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 13].length) (baseStart_744150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_744150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_744150 prefixEnd_744150 := by exact prefixLift 744150
  have htrace : WordTrace (prefixWord ++ tailWord_744150) baseStart_744150 baseEnd_744150 := by
    simpa [prefixWord, tailWord_744150, baseEnd_744150] using wordTrace_append hprefix tailTrace_744150
  have hstable : (prefixWord ++ tailWord_744150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744150).length < 2 ^ (prefixWord ++ tailWord_744150).sum := by decide
  have hdescent : baseEnd_744150 < baseStart_744150 := by decide
  rcases family_descends (prefixWord ++ tailWord_744150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744156 : List Nat := [2, 2, 5, 1, 1, 1, 4, 2, 3]
def baseStart_744156 : Nat := 118140960795 + 744156 * 2 ^ 59
def prefixEnd_744156 : Nat := 4983230072969 + 3 ^ 40 * 744156 * 2
def baseEnd_744156 : Nat := 169826537745464764412309

theorem tailTrace_744156 : CollatzResearch.WordTrace tailWord_744156 prefixEnd_744156 169826537745464764412309 := by
  unfold tailWord_744156
  simp only [CollatzResearch.WordTrace]
  refine ⟨13570799546028689285810161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18094399394704919047746881 13570799546028689285810161)
  ·
    refine ⟨10178099659521516964357621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13570799546028689285810161 10178099659521516964357621)
    ·
      refine ⟨954196843080142215408527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10178099659521516964357621 954196843080142215408527)
      ·
        refine ⟨1431295264620213323112791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 954196843080142215408527 1431295264620213323112791)
        ·
          refine ⟨2146942896930319984669187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1431295264620213323112791 2146942896930319984669187)
          ·
            refine ⟨3220414345395479977003781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2146942896930319984669187 3220414345395479977003781)
            ·
              refine ⟨603827689761652495688209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3220414345395479977003781 603827689761652495688209)
              ·
                refine ⟨452870767321239371766157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 603827689761652495688209 452870767321239371766157)
                ·
                  refine ⟨169826537745464764412309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 452870767321239371766157 169826537745464764412309)
                  ·
                    rfl

theorem cell21_744156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 3].length) (baseStart_744156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_744156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_744156 prefixEnd_744156 := by exact prefixLift 744156
  have htrace : WordTrace (prefixWord ++ tailWord_744156) baseStart_744156 baseEnd_744156 := by
    simpa [prefixWord, tailWord_744156, baseEnd_744156] using wordTrace_append hprefix tailTrace_744156
  have hstable : (prefixWord ++ tailWord_744156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744156).length < 2 ^ (prefixWord ++ tailWord_744156).sum := by decide
  have hdescent : baseEnd_744156 < baseStart_744156 := by decide
  rcases family_descends (prefixWord ++ tailWord_744156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744243 : List Nat := [1, 1, 1, 2, 6, 3, 2, 5]
def baseStart_744243 : Nat := 118140960795 + 744243 * 2 ^ 59
def prefixEnd_744243 : Nat := 4983230072969 + 3 ^ 40 * 744243 * 2
def baseEnd_744243 : Nat := 56615464110257315487377

theorem tailTrace_744243 : CollatzResearch.WordTrace tailWord_744243 prefixEnd_744243 56615464110257315487377 := by
  unfold tailWord_744243
  simp only [CollatzResearch.WordTrace]
  refine ⟨27144772242742192430037383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18096514828494794953358255 27144772242742192430037383)
  ·
    refine ⟨40717158364113288645056075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27144772242742192430037383 40717158364113288645056075)
    ·
      refine ⟨61075737546169932967584113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40717158364113288645056075 61075737546169932967584113)
      ·
        refine ⟨45806803159627449725688085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61075737546169932967584113 45806803159627449725688085)
        ·
          refine ⟨2147193898107536705891629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45806803159627449725688085 2147193898107536705891629)
          ·
            refine ⟨805197711790326264709361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2147193898107536705891629 805197711790326264709361)
            ·
              refine ⟨603898283842744698532021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 805197711790326264709361 603898283842744698532021)
              ·
                refine ⟨56615464110257315487377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 603898283842744698532021 56615464110257315487377)
                ·
                  rfl

theorem cell21_744243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 5].length) (baseStart_744243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_744243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_744243 prefixEnd_744243 := by exact prefixLift 744243
  have htrace : WordTrace (prefixWord ++ tailWord_744243) baseStart_744243 baseEnd_744243 := by
    simpa [prefixWord, tailWord_744243, baseEnd_744243] using wordTrace_append hprefix tailTrace_744243
  have hstable : (prefixWord ++ tailWord_744243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744243).length < 2 ^ (prefixWord ++ tailWord_744243).sum := by decide
  have hdescent : baseEnd_744243 < baseStart_744243 := by decide
  rcases family_descends (prefixWord ++ tailWord_744243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744260 : List Nat := [2, 3, 4, 2, 1, 2, 7]
def baseStart_744260 : Nat := 118140960795 + 744260 * 2 ^ 59
def prefixEnd_744260 : Nat := 4983230072969 + 3 ^ 40 * 744260 * 2
def baseEnd_744260 : Nat := 18872252440264854964307

theorem tailTrace_744260 : CollatzResearch.WordTrace tailWord_744260 prefixEnd_744260 18872252440264854964307 := by
  unfold tailWord_744260
  simp only [CollatzResearch.WordTrace]
  refine ⟨13572696141840302166703117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18096928189120402888937489 13572696141840302166703117)
  ·
    refine ⟨5089761053190113312513669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13572696141840302166703117 5089761053190113312513669)
    ·
      refine ⟨954330197473146246096313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5089761053190113312513669 954330197473146246096313)
      ·
        refine ⟨715747648104859684572235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 954330197473146246096313 715747648104859684572235)
        ·
          refine ⟨1073621472157289526858353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715747648104859684572235 1073621472157289526858353)
          ·
            refine ⟨805216104117967145143765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1073621472157289526858353 805216104117967145143765)
            ·
              refine ⟨18872252440264854964307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 805216104117967145143765 18872252440264854964307)
              ·
                rfl

theorem cell21_744260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 7].length) (baseStart_744260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_744260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_744260 prefixEnd_744260 := by exact prefixLift 744260
  have htrace : WordTrace (prefixWord ++ tailWord_744260) baseStart_744260 baseEnd_744260 := by
    simpa [prefixWord, tailWord_744260, baseEnd_744260] using wordTrace_append hprefix tailTrace_744260
  have hstable : (prefixWord ++ tailWord_744260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744260).length < 2 ^ (prefixWord ++ tailWord_744260).sum := by decide
  have hdescent : baseEnd_744260 < baseStart_744260 := by decide
  rcases family_descends (prefixWord ++ tailWord_744260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744381 : List Nat := [1, 4, 1, 2, 4, 2, 1, 2, 4]
def baseStart_744381 : Nat := 118140960795 + 744381 * 2 ^ 59
def prefixEnd_744381 : Nat := 4983230072969 + 3 ^ 40 * 744381 * 2
def baseEnd_744381 : Nat := 169877885810914373161849

theorem tailTrace_744381 : CollatzResearch.WordTrace tailWord_744381 prefixEnd_744381 169877885810914373161849 := by
  unfold tailWord_744381
  simp only [CollatzResearch.WordTrace]
  refine ⟨27149805516242241998560997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18099870344161494665707331 27149805516242241998560997)
  ·
    refine ⟨5090588534295420374730187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27149805516242241998560997 5090588534295420374730187)
    ·
      refine ⟨7635882801443130562095281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5090588534295420374730187 7635882801443130562095281)
      ·
        refine ⟨5726912101082347921571461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7635882801443130562095281 5726912101082347921571461)
        ·
          refine ⟨1073796018952940235294649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5726912101082347921571461 1073796018952940235294649)
          ·
            refine ⟨805347014214705176470987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1073796018952940235294649 805347014214705176470987)
            ·
              refine ⟨1208020521322057764706481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 805347014214705176470987 1208020521322057764706481)
              ·
                refine ⟨906015390991543323529861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1208020521322057764706481 906015390991543323529861)
                ·
                  refine ⟨169877885810914373161849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 906015390991543323529861 169877885810914373161849)
                  ·
                    rfl

theorem cell21_744381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_744381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_744381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_744381 prefixEnd_744381 := by exact prefixLift 744381
  have htrace : WordTrace (prefixWord ++ tailWord_744381) baseStart_744381 baseEnd_744381 := by
    simpa [prefixWord, tailWord_744381, baseEnd_744381] using wordTrace_append hprefix tailTrace_744381
  have hstable : (prefixWord ++ tailWord_744381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744381).length < 2 ^ (prefixWord ++ tailWord_744381).sum := by decide
  have hdescent : baseEnd_744381 < baseStart_744381 := by decide
  rcases family_descends (prefixWord ++ tailWord_744381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744423 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 6]
def baseStart_744423 : Nat := 118140960795 + 744423 * 2 ^ 59
def prefixEnd_744423 : Nat := 4983230072969 + 3 ^ 40 * 744423 * 2
def baseEnd_744423 : Nat := 169887470783131633461763

theorem tailTrace_744423 : CollatzResearch.WordTrace tailWord_744423 prefixEnd_744423 169887470783131633461763 := by
  unfold tailWord_744423
  simp only [CollatzResearch.WordTrace]
  refine ⟨27151337382090083171589923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18100891588060055447726615 27151337382090083171589923)
  ·
    refine ⟨40727006073135124757384885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27151337382090083171589923 40727006073135124757384885)
    ·
      refine ⟨3818156819356417946004833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40727006073135124757384885 3818156819356417946004833)
      ·
        refine ⟨2863617614517313459503625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3818156819356417946004833 2863617614517313459503625)
        ·
          refine ⟨2147713210887985094627719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2863617614517313459503625 2147713210887985094627719)
          ·
            refine ⟨3221569816331977641941579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2147713210887985094627719 3221569816331977641941579)
            ·
              refine ⟨4832354724497966462912369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3221569816331977641941579 4832354724497966462912369)
              ·
                refine ⟨3624266043373474847184277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4832354724497966462912369 3624266043373474847184277)
                ·
                  refine ⟨169887470783131633461763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3624266043373474847184277 169887470783131633461763)
                  ·
                    rfl

theorem cell21_744423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 6].length) (baseStart_744423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_744423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_744423 prefixEnd_744423 := by exact prefixLift 744423
  have htrace : WordTrace (prefixWord ++ tailWord_744423) baseStart_744423 baseEnd_744423 := by
    simpa [prefixWord, tailWord_744423, baseEnd_744423] using wordTrace_append hprefix tailTrace_744423
  have hstable : (prefixWord ++ tailWord_744423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744423).length < 2 ^ (prefixWord ++ tailWord_744423).sum := by decide
  have hdescent : baseEnd_744423 < baseStart_744423 := by decide
  rcases family_descends (prefixWord ++ tailWord_744423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744426 : List Nat := [3, 1, 3, 1, 2, 2, 3, 3, 3]
def baseStart_744426 : Nat := 118140960795 + 744426 * 2 ^ 59
def prefixEnd_744426 : Nat := 4983230072969 + 3 ^ 40 * 744426 * 2
def baseEnd_744426 : Nat := 169888155424004294911757

theorem tailTrace_744426 : CollatzResearch.WordTrace tailWord_744426 prefixEnd_744426 169888155424004294911757 := by
  unfold tailWord_744426
  simp only [CollatzResearch.WordTrace]
  refine ⟨6787861700269803670987283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18100964534052809789299421 6787861700269803670987283)
  ·
    refine ⟨10181792550404705506480925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6787861700269803670987283 10181792550404705506480925)
    ·
      refine ⟨3818172206401764564930347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10181792550404705506480925 3818172206401764564930347)
      ·
        refine ⟨5727258309602646847395521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3818172206401764564930347 5727258309602646847395521)
        ·
          refine ⟨4295443732201985135546641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5727258309602646847395521 4295443732201985135546641)
          ·
            refine ⟨3221582799151488851659981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4295443732201985135546641 3221582799151488851659981)
            ·
              refine ⟨1208093549681808319372493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3221582799151488851659981 1208093549681808319372493)
              ·
                refine ⟨453035081130678119764685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1208093549681808319372493 453035081130678119764685)
                ·
                  refine ⟨169888155424004294911757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453035081130678119764685 169888155424004294911757)
                  ·
                    rfl

theorem cell21_744426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 3].length) (baseStart_744426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_744426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_744426 prefixEnd_744426 := by exact prefixLift 744426
  have htrace : WordTrace (prefixWord ++ tailWord_744426) baseStart_744426 baseEnd_744426 := by
    simpa [prefixWord, tailWord_744426, baseEnd_744426] using wordTrace_append hprefix tailTrace_744426
  have hstable : (prefixWord ++ tailWord_744426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744426).length < 2 ^ (prefixWord ++ tailWord_744426).sum := by decide
  have hdescent : baseEnd_744426 < baseStart_744426 := by decide
  rcases family_descends (prefixWord ++ tailWord_744426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744485 : List Nat := [1, 3, 1, 2, 2, 2, 2, 5, 3]
def baseStart_744485 : Nat := 118140960795 + 744485 * 2 ^ 59
def prefixEnd_744485 : Nat := 4983230072969 + 3 ^ 40 * 744485 * 2
def baseEnd_744485 : Nat := 169901620027833303428303

theorem tailTrace_744485 : CollatzResearch.WordTrace tailWord_744485 prefixEnd_744485 169901620027833303428303 := by
  unfold tailWord_744485
  simp only [CollatzResearch.WordTrace]
  refine ⟨27153598707865467760346909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18102399138576978506897939 27153598707865467760346909)
  ·
    refine ⟨10182599515449550410130091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27153598707865467760346909 10182599515449550410130091)
    ·
      refine ⟨15273899273174325615195137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10182599515449550410130091 15273899273174325615195137)
      ·
        refine ⟨11455424454880744211396353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15273899273174325615195137 11455424454880744211396353)
        ·
          refine ⟨8591568341160558158547265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11455424454880744211396353 8591568341160558158547265)
          ·
            refine ⟨6443676255870418618910449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8591568341160558158547265 6443676255870418618910449)
            ·
              refine ⟨4832757191902813964182837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6443676255870418618910449 4832757191902813964182837)
              ·
                refine ⟨453070986740888809142141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4832757191902813964182837 453070986740888809142141)
                ·
                  refine ⟨169901620027833303428303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453070986740888809142141 169901620027833303428303)
                  ·
                    rfl

theorem cell21_744485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 3].length) (baseStart_744485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_744485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_744485 prefixEnd_744485 := by exact prefixLift 744485
  have htrace : WordTrace (prefixWord ++ tailWord_744485) baseStart_744485 baseEnd_744485 := by
    simpa [prefixWord, tailWord_744485, baseEnd_744485] using wordTrace_append hprefix tailTrace_744485
  have hstable : (prefixWord ++ tailWord_744485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744485).length < 2 ^ (prefixWord ++ tailWord_744485).sum := by decide
  have hdescent : baseEnd_744485 < baseStart_744485 := by decide
  rcases family_descends (prefixWord ++ tailWord_744485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744606 : List Nat := [4, 3, 1, 1, 2, 1, 9]
def baseStart_744606 : Nat := 118140960795 + 744606 * 2 ^ 59
def prefixEnd_744606 : Nat := 4983230072969 + 3 ^ 40 * 744606 * 2
def baseEnd_744606 : Nat := 18881025986262664656821

theorem tailTrace_744606 : CollatzResearch.WordTrace tailWord_744606 prefixEnd_744606 18881025986262664656821 := by
  unfold tailWord_744606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3394751492553388178187709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18105341293618070283667781 3394751492553388178187709)
  ·
    refine ⟨1273031809707520566820391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3394751492553388178187709 1273031809707520566820391)
    ·
      refine ⟨1909547714561280850230587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1273031809707520566820391 1909547714561280850230587)
      ·
        refine ⟨2864321571841921275345881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1909547714561280850230587 2864321571841921275345881)
        ·
          refine ⟨2148241178881440956509411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2864321571841921275345881 2148241178881440956509411)
          ·
            refine ⟨3222361768322161434764117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2148241178881440956509411 3222361768322161434764117)
            ·
              refine ⟨18881025986262664656821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3222361768322161434764117 18881025986262664656821)
              ·
                rfl

theorem cell21_744606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 9].length) (baseStart_744606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_744606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_744606 prefixEnd_744606 := by exact prefixLift 744606
  have htrace : WordTrace (prefixWord ++ tailWord_744606) baseStart_744606 baseEnd_744606 := by
    simpa [prefixWord, tailWord_744606, baseEnd_744606] using wordTrace_append hprefix tailTrace_744606
  have hstable : (prefixWord ++ tailWord_744606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744606).length < 2 ^ (prefixWord ++ tailWord_744606).sum := by decide
  have hdescent : baseEnd_744606 < baseStart_744606 := by decide
  rcases family_descends (prefixWord ++ tailWord_744606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744682 : List Nat := [3, 1, 3, 1, 1, 5, 1, 6]
def baseStart_744682 : Nat := 118140960795 + 744682 * 2 ^ 59
def prefixEnd_744682 : Nat := 4983230072969 + 3 ^ 40 * 744682 * 2
def baseEnd_744682 : Nat := 56648859370601579548189

theorem tailTrace_744682 : CollatzResearch.WordTrace tailWord_744682 prefixEnd_744682 56648859370601579548189 := by
  unfold tailWord_744682
  simp only [CollatzResearch.WordTrace]
  refine ⟨6790195972037942601317075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18107189258767846936845533 6790195972037942601317075)
  ·
    refine ⟨10185293958056913901975613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6790195972037942601317075 10185293958056913901975613)
    ·
      refine ⟨3819485234271342713240855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10185293958056913901975613 3819485234271342713240855)
      ·
        refine ⟨5729227851407014069861283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3819485234271342713240855 5729227851407014069861283)
        ·
          refine ⟨8593841777110521104791925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5729227851407014069861283 8593841777110521104791925)
          ·
            refine ⟨805672666604111353574243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8593841777110521104791925 805672666604111353574243)
            ·
              refine ⟨1208508999906167030361365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 805672666604111353574243 1208508999906167030361365)
              ·
                refine ⟨56648859370601579548189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1208508999906167030361365 56648859370601579548189)
                ·
                  rfl

theorem cell21_744682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_744682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_744682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_744682 prefixEnd_744682 := by exact prefixLift 744682
  have htrace : WordTrace (prefixWord ++ tailWord_744682) baseStart_744682 baseEnd_744682 := by
    simpa [prefixWord, tailWord_744682, baseEnd_744682] using wordTrace_append hprefix tailTrace_744682
  have hstable : (prefixWord ++ tailWord_744682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744682).length < 2 ^ (prefixWord ++ tailWord_744682).sum := by decide
  have hdescent : baseEnd_744682 < baseStart_744682 := by decide
  rcases family_descends (prefixWord ++ tailWord_744682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744713 : List Nat := [1, 2, 1, 1, 3, 3, 4, 3, 3]
def baseStart_744713 : Nat := 118140960795 + 744713 * 2 ^ 59
def prefixEnd_744713 : Nat := 4983230072969 + 3 ^ 40 * 744713 * 2
def baseEnd_744713 : Nat := 169953652734155573627837

theorem tailTrace_744713 : CollatzResearch.WordTrace tailWord_744713 prefixEnd_744713 169953652734155573627837 := by
  unfold tailWord_744713
  simp only [CollatzResearch.WordTrace]
  refine ⟨27161914551039462699646793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18107943034026308466431195 27161914551039462699646793)
  ·
    refine ⟨20371435913279597024735095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27161914551039462699646793 20371435913279597024735095)
    ·
      refine ⟨30557153869919395537102643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20371435913279597024735095 30557153869919395537102643)
      ·
        refine ⟨45835730804879093305653965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30557153869919395537102643 45835730804879093305653965)
        ·
          refine ⟨17188399051829659989620237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45835730804879093305653965 17188399051829659989620237)
          ·
            refine ⟨6445649644436122496107589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17188399051829659989620237 6445649644436122496107589)
            ·
              refine ⟨1208559308331772968020173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6445649644436122496107589 1208559308331772968020173)
              ·
                refine ⟨453209740624414863007565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1208559308331772968020173 453209740624414863007565)
                ·
                  refine ⟨169953652734155573627837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453209740624414863007565 169953652734155573627837)
                  ·
                    rfl

theorem cell21_744713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 3].length) (baseStart_744713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_744713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_744713 prefixEnd_744713 := by exact prefixLift 744713
  have htrace : WordTrace (prefixWord ++ tailWord_744713) baseStart_744713 baseEnd_744713 := by
    simpa [prefixWord, tailWord_744713, baseEnd_744713] using wordTrace_append hprefix tailTrace_744713
  have hstable : (prefixWord ++ tailWord_744713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744713).length < 2 ^ (prefixWord ++ tailWord_744713).sum := by decide
  have hdescent : baseEnd_744713 < baseStart_744713 := by decide
  rcases family_descends (prefixWord ++ tailWord_744713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744789 : List Nat := [1, 3, 2, 2, 3, 3, 1, 1, 5]
def baseStart_744789 : Nat := 118140960795 + 744789 * 2 ^ 59
def prefixEnd_744789 : Nat := 4983230072969 + 3 ^ 40 * 744789 * 2
def baseEnd_744789 : Nat := 169970996969596330361015

theorem tailTrace_744789 : CollatzResearch.WordTrace tailWord_744789 prefixEnd_744789 169970996969596330361015 := by
  unfold tailWord_744789
  simp only [CollatzResearch.WordTrace]
  refine ⟨27164686498764127679413421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18109790999176085119608947 27164686498764127679413421)
  ·
    refine ⟨10186757437036547879780033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27164686498764127679413421 10186757437036547879780033)
    ·
      refine ⟨7640068077777410909835025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10186757437036547879780033 7640068077777410909835025)
      ·
        refine ⟨5730051058333058182376269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7640068077777410909835025 5730051058333058182376269)
        ·
          refine ⟨2148769146874896818391101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5730051058333058182376269 2148769146874896818391101)
          ·
            refine ⟨805788430078086306896663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2148769146874896818391101 805788430078086306896663)
            ·
              refine ⟨1208682645117129460344995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 805788430078086306896663 1208682645117129460344995)
              ·
                refine ⟨1813023967675694190517493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1208682645117129460344995 1813023967675694190517493)
                ·
                  refine ⟨169970996969596330361015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1813023967675694190517493 169970996969596330361015)
                  ·
                    rfl

theorem cell21_744789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_744789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_744789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_744789 prefixEnd_744789 := by exact prefixLift 744789
  have htrace : WordTrace (prefixWord ++ tailWord_744789) baseStart_744789 baseEnd_744789 := by
    simpa [prefixWord, tailWord_744789, baseEnd_744789] using wordTrace_append hprefix tailTrace_744789
  have hstable : (prefixWord ++ tailWord_744789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744789).length < 2 ^ (prefixWord ++ tailWord_744789).sum := by decide
  have hdescent : baseEnd_744789 < baseStart_744789 := by decide
  rcases family_descends (prefixWord ++ tailWord_744789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744803 : List Nat := [1, 1, 1, 5, 2, 3, 1, 3, 4]
def baseStart_744803 : Nat := 118140960795 + 744803 * 2 ^ 59
def prefixEnd_744803 : Nat := 4983230072969 + 3 ^ 40 * 744803 * 2
def baseEnd_744803 : Nat := 169974191960335417127653

theorem tailTrace_744803 : CollatzResearch.WordTrace tailWord_744803 prefixEnd_744803 169974191960335417127653 := by
  unfold tailWord_744803
  simp only [CollatzResearch.WordTrace]
  refine ⟨27165197120713408070423063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18110131413808938713615375 27165197120713408070423063)
  ·
    refine ⟨40747795681070112105634595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27165197120713408070423063 40747795681070112105634595)
    ·
      refine ⟨61121693521605168158451893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40747795681070112105634595 61121693521605168158451893)
      ·
        refine ⟨5730158767650484514854865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61121693521605168158451893 5730158767650484514854865)
        ·
          refine ⟨4297619075737863386141149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5730158767650484514854865 4297619075737863386141149)
          ·
            refine ⟨1611607153401698769802931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4297619075737863386141149 1611607153401698769802931)
            ·
              refine ⟨2417410730102548154704397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1611607153401698769802931 2417410730102548154704397)
              ·
                refine ⟨906529023788455558014149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2417410730102548154704397 906529023788455558014149)
                ·
                  refine ⟨169974191960335417127653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 906529023788455558014149 169974191960335417127653)
                  ·
                    rfl

theorem cell21_744803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 4].length) (baseStart_744803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_744803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_744803 prefixEnd_744803 := by exact prefixLift 744803
  have htrace : WordTrace (prefixWord ++ tailWord_744803) baseStart_744803 baseEnd_744803 := by
    simpa [prefixWord, tailWord_744803, baseEnd_744803] using wordTrace_append hprefix tailTrace_744803
  have hstable : (prefixWord ++ tailWord_744803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744803).length < 2 ^ (prefixWord ++ tailWord_744803).sum := by decide
  have hdescent : baseEnd_744803 < baseStart_744803 := by decide
  rcases family_descends (prefixWord ++ tailWord_744803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744834 : List Nat := [3, 4, 2, 1, 1, 10]
def baseStart_744834 : Nat := 118140960795 + 744834 * 2 ^ 59
def prefixEnd_744834 : Nat := 4983230072969 + 3 ^ 40 * 744834 * 2
def baseEnd_744834 : Nat := 6295602466025416744849

theorem tailTrace_744834 : CollatzResearch.WordTrace tailWord_744834 prefixEnd_744834 6295602466025416744849 := by
  unfold tailWord_744834
  simp only [CollatzResearch.WordTrace]
  refine ⟨6791581945900275091200389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18110885189067400243201037 6791581945900275091200389)
  ·
    refine ⟨1273421614856301579600073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6791581945900275091200389 1273421614856301579600073)
    ·
      refine ⟨955066211142226184700055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1273421614856301579600073 955066211142226184700055)
      ·
        refine ⟨1432599316713339277050083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 955066211142226184700055 1432599316713339277050083)
        ·
          refine ⟨2148898975070008915575125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1432599316713339277050083 2148898975070008915575125)
          ·
            refine ⟨6295602466025416744849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2148898975070008915575125 6295602466025416744849)
            ·
              rfl

theorem cell21_744834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 10].length) (baseStart_744834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_744834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_744834 prefixEnd_744834 := by exact prefixLift 744834
  have htrace : WordTrace (prefixWord ++ tailWord_744834) baseStart_744834 baseEnd_744834 := by
    simpa [prefixWord, tailWord_744834, baseEnd_744834] using wordTrace_append hprefix tailTrace_744834
  have hstable : (prefixWord ++ tailWord_744834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744834).length < 2 ^ (prefixWord ++ tailWord_744834).sum := by decide
  have hdescent : baseEnd_744834 < baseStart_744834 := by decide
  rcases family_descends (prefixWord ++ tailWord_744834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744876 : List Nat := [2, 2, 1, 1, 1, 1, 4, 9]
def baseStart_744876 : Nat := 118140960795 + 744876 * 2 ^ 59
def prefixEnd_744876 : Nat := 4983230072969 + 3 ^ 40 * 744876 * 2
def baseEnd_744876 : Nat := 56663617184967837470279

theorem tailTrace_744876 : CollatzResearch.WordTrace tailWord_744876 prefixEnd_744876 56663617184967837470279 := by
  unfold tailWord_744876
  simp only [CollatzResearch.WordTrace]
  refine ⟨13583929824724470768915241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18111906432965961025220321 13583929824724470768915241)
  ·
    refine ⟨10187947368543353076686431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13583929824724470768915241 10187947368543353076686431)
    ·
      refine ⟨15281921052815029615029647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10187947368543353076686431 15281921052815029615029647)
      ·
        refine ⟨22922881579222544422544471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15281921052815029615029647 22922881579222544422544471)
        ·
          refine ⟨34384322368833816633816707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22922881579222544422544471 34384322368833816633816707)
          ·
            refine ⟨51576483553250724950725061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34384322368833816633816707 51576483553250724950725061)
            ·
              refine ⟨9670590666234510928260949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51576483553250724950725061 9670590666234510928260949)
              ·
                refine ⟨56663617184967837470279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9670590666234510928260949 56663617184967837470279)
                ·
                  rfl

theorem cell21_744876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 9].length) (baseStart_744876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_744876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_744876 prefixEnd_744876 := by exact prefixLift 744876
  have htrace : WordTrace (prefixWord ++ tailWord_744876) baseStart_744876 baseEnd_744876 := by
    simpa [prefixWord, tailWord_744876, baseEnd_744876] using wordTrace_append hprefix tailTrace_744876
  have hstable : (prefixWord ++ tailWord_744876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744876).length < 2 ^ (prefixWord ++ tailWord_744876).sum := by decide
  have hdescent : baseEnd_744876 < baseStart_744876 := by decide
  rcases family_descends (prefixWord ++ tailWord_744876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744907 : List Nat := [1, 1, 1, 1, 3, 3, 3, 3, 5]
def baseStart_744907 : Nat := 118140960795 + 744907 * 2 ^ 59
def prefixEnd_744907 : Nat := 4983230072969 + 3 ^ 40 * 744907 * 2
def baseEnd_744907 : Nat := 169997926177254347394107

theorem tailTrace_744907 : CollatzResearch.WordTrace tailWord_744907 prefixEnd_744907 169997926177254347394107 := by
  unfold tailWord_744907
  simp only [CollatzResearch.WordTrace]
  refine ⟨27168990312336633832208975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18112660208224422554805983 27168990312336633832208975)
  ·
    refine ⟨40753485468504950748313463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27168990312336633832208975 40753485468504950748313463)
    ·
      refine ⟨61130228202757426122470195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40753485468504950748313463 61130228202757426122470195)
      ·
        refine ⟨91695342304136139183705293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61130228202757426122470195 91695342304136139183705293)
        ·
          refine ⟨34385753364051052193889485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91695342304136139183705293 34385753364051052193889485)
          ·
            refine ⟨12894657511519144572708557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34385753364051052193889485 12894657511519144572708557)
            ·
              refine ⟨4835496566819679214765709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12894657511519144572708557 4835496566819679214765709)
              ·
                refine ⟨1813311212557379705537141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4835496566819679214765709 1813311212557379705537141)
                ·
                  refine ⟨169997926177254347394107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1813311212557379705537141 169997926177254347394107)
                  ·
                    rfl

theorem cell21_744907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 5].length) (baseStart_744907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_744907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_744907 prefixEnd_744907 := by exact prefixLift 744907
  have htrace : WordTrace (prefixWord ++ tailWord_744907) baseStart_744907 baseEnd_744907 := by
    simpa [prefixWord, tailWord_744907, baseEnd_744907] using wordTrace_append hprefix tailTrace_744907
  have hstable : (prefixWord ++ tailWord_744907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744907).length < 2 ^ (prefixWord ++ tailWord_744907).sum := by decide
  have hdescent : baseEnd_744907 < baseStart_744907 := by decide
  rcases family_descends (prefixWord ++ tailWord_744907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_744952 : List Nat := [2, 1, 2, 1, 1, 5, 9]
def baseStart_744952 : Nat := 118140960795 + 744952 * 2 ^ 59
def prefixEnd_744952 : Nat := 4983230072969 + 3 ^ 40 * 744952 * 2
def baseEnd_744952 : Nat := 18889799532260474349335

theorem tailTrace_744952 : CollatzResearch.WordTrace tailWord_744952 prefixEnd_744952 18889799532260474349335 := by
  unfold tailWord_744952
  simp only [CollatzResearch.WordTrace]
  refine ⟨13585315798586803258798555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18113754398115737678398073 13585315798586803258798555)
  ·
    refine ⟨20377973697880204888197833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13585315798586803258798555 20377973697880204888197833)
    ·
      refine ⟨15283480273410153666148375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20377973697880204888197833 15283480273410153666148375)
      ·
        refine ⟨22925220410115230499222563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15283480273410153666148375 22925220410115230499222563)
        ·
          refine ⟨34387830615172845748833845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22925220410115230499222563 34387830615172845748833845)
          ·
            refine ⟨3223859120172454288953173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34387830615172845748833845 3223859120172454288953173)
            ·
              refine ⟨18889799532260474349335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3223859120172454288953173 18889799532260474349335)
              ·
                rfl

theorem cell21_744952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 9].length) (baseStart_744952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_744952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_744952 prefixEnd_744952 := by exact prefixLift 744952
  have htrace : WordTrace (prefixWord ++ tailWord_744952) baseStart_744952 baseEnd_744952 := by
    simpa [prefixWord, tailWord_744952, baseEnd_744952] using wordTrace_append hprefix tailTrace_744952
  have hstable : (prefixWord ++ tailWord_744952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_744952).length < 2 ^ (prefixWord ++ tailWord_744952).sum := by decide
  have hdescent : baseEnd_744952 < baseStart_744952 := by decide
  rcases family_descends (prefixWord ++ tailWord_744952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745017 : List Nat := [1, 2, 1, 5, 1, 3, 1, 4, 3]
def baseStart_745017 : Nat := 118140960795 + 745017 * 2 ^ 59
def prefixEnd_745017 : Nat := 4983230072969 + 3 ^ 40 * 745017 * 2
def baseEnd_745017 : Nat := 170023029675918600560549

theorem tailTrace_745017 : CollatzResearch.WordTrace tailWord_745017 prefixEnd_745017 170023029675918600560549 := by
  unfold tailWord_745017
  simp only [CollatzResearch.WordTrace]
  refine ⟨27173002341938122618713305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18115334894625415079142203 27173002341938122618713305)
  ·
    refine ⟨20379751756453591964034979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27173002341938122618713305 20379751756453591964034979)
    ·
      refine ⟨30569627634680387946052469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20379751756453591964034979 30569627634680387946052469)
      ·
        refine ⟨2865902590751286369942419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30569627634680387946052469 2865902590751286369942419)
        ·
          refine ⟨4298853886126929554913629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2865902590751286369942419 4298853886126929554913629)
          ·
            refine ⟨1612070207297598583092611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4298853886126929554913629 1612070207297598583092611)
            ·
              refine ⟨2418105310946397874638917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1612070207297598583092611 2418105310946397874638917)
              ·
                refine ⟨453394745802449601494797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2418105310946397874638917 453394745802449601494797)
                ·
                  refine ⟨170023029675918600560549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453394745802449601494797 170023029675918600560549)
                  ·
                    rfl

theorem cell21_745017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 3].length) (baseStart_745017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745017 prefixEnd_745017 := by exact prefixLift 745017
  have htrace : WordTrace (prefixWord ++ tailWord_745017) baseStart_745017 baseEnd_745017 := by
    simpa [prefixWord, tailWord_745017, baseEnd_745017] using wordTrace_append hprefix tailTrace_745017
  have hstable : (prefixWord ++ tailWord_745017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745017).length < 2 ^ (prefixWord ++ tailWord_745017).sum := by decide
  have hdescent : baseEnd_745017 < baseStart_745017 := by decide
  rcases family_descends (prefixWord ++ tailWord_745017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745096 : List Nat := [2, 1, 3, 5, 2, 1, 2, 5]
def baseStart_745096 : Nat := 118140960795 + 745096 * 2 ^ 59
def prefixEnd_745096 : Nat := 4983230072969 + 3 ^ 40 * 745096 * 2
def baseEnd_745096 : Nat := 56680352850744006247907

theorem tailTrace_745096 : CollatzResearch.WordTrace tailWord_745096 prefixEnd_745096 56680352850744006247907 := by
  unfold tailWord_745096
  simp only [CollatzResearch.WordTrace]
  refine ⟨13587941854325959555419571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18117255805767946073892761 13587941854325959555419571)
  ·
    refine ⟨20381912781488939333129357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13587941854325959555419571 20381912781488939333129357)
    ·
      refine ⟨7643217293058352249923509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20381912781488939333129357 7643217293058352249923509)
      ·
        refine ⟨716551621224220523430329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7643217293058352249923509 716551621224220523430329)
        ·
          refine ⟨537413715918165392572747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 716551621224220523430329 537413715918165392572747)
          ·
            refine ⟨806120573877248088859121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537413715918165392572747 806120573877248088859121)
            ·
              refine ⟨604590430407936066644341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 806120573877248088859121 604590430407936066644341)
              ·
                refine ⟨56680352850744006247907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 604590430407936066644341 56680352850744006247907)
                ·
                  rfl

theorem cell21_745096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 5].length) (baseStart_745096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745096 prefixEnd_745096 := by exact prefixLift 745096
  have htrace : WordTrace (prefixWord ++ tailWord_745096) baseStart_745096 baseEnd_745096 := by
    simpa [prefixWord, tailWord_745096, baseEnd_745096] using wordTrace_append hprefix tailTrace_745096
  have hstable : (prefixWord ++ tailWord_745096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745096).length < 2 ^ (prefixWord ++ tailWord_745096).sum := by decide
  have hdescent : baseEnd_745096 < baseStart_745096 := by decide
  rcases family_descends (prefixWord ++ tailWord_745096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745121 : List Nat := [1, 2, 3, 3, 2, 3, 7]
def baseStart_745121 : Nat := 118140960795 + 745121 * 2 ^ 59
def prefixEnd_745121 : Nat := 4983230072969 + 3 ^ 40 * 745121 * 2
def baseEnd_745121 : Nat := 18894084876981947869667

theorem tailTrace_745121 : CollatzResearch.WordTrace tailWord_745121 prefixEnd_745121 18894084876981947869667 := by
  unfold tailWord_745121
  simp only [CollatzResearch.WordTrace]
  refine ⟨27176795533561348380499217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18117863689040898920332811 27176795533561348380499217)
  ·
    refine ⟨20382596650171011285374413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27176795533561348380499217 20382596650171011285374413)
    ·
      refine ⟨7643473743814129232015405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20382596650171011285374413 7643473743814129232015405)
      ·
        refine ⟨2866302653930298462005777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7643473743814129232015405 2866302653930298462005777)
        ·
          refine ⟨2149726990447723846504333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2866302653930298462005777 2149726990447723846504333)
          ·
            refine ⟨806147621417896442439125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2149726990447723846504333 806147621417896442439125)
            ·
              refine ⟨18894084876981947869667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 806147621417896442439125 18894084876981947869667)
              ·
                rfl

theorem cell21_745121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 7].length) (baseStart_745121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745121 prefixEnd_745121 := by exact prefixLift 745121
  have htrace : WordTrace (prefixWord ++ tailWord_745121) baseStart_745121 baseEnd_745121 := by
    simpa [prefixWord, tailWord_745121, baseEnd_745121] using wordTrace_append hprefix tailTrace_745121
  have hstable : (prefixWord ++ tailWord_745121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745121).length < 2 ^ (prefixWord ++ tailWord_745121).sum := by decide
  have hdescent : baseEnd_745121 < baseStart_745121 := by decide
  rcases family_descends (prefixWord ++ tailWord_745121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745141 : List Nat := [1, 3, 3, 3, 2, 2, 2, 1, 4]
def baseStart_745141 : Nat := 118140960795 + 745141 * 2 ^ 59
def prefixEnd_745141 : Nat := 4983230072969 + 3 ^ 40 * 745141 * 2
def baseEnd_745141 : Nat := 170051328165321940493629

theorem tailTrace_745141 : CollatzResearch.WordTrace tailWord_745141 prefixEnd_745141 170051328165321940493629 := by
  unfold tailWord_745141
  simp only [CollatzResearch.WordTrace]
  refine ⟨27177524993488891796227277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18118349995659261197484851 27177524993488891796227277)
  ·
    refine ⟨10191571872558334423585229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27177524993488891796227277 10191571872558334423585229)
    ·
      refine ⟨3821839452209375408844461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10191571872558334423585229 3821839452209375408844461)
      ·
        refine ⟨1433189794578515778316673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3821839452209375408844461 1433189794578515778316673)
        ·
          refine ⟨1074892345933886833737505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1433189794578515778316673 1074892345933886833737505)
          ·
            refine ⟨806169259450415125303129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1074892345933886833737505 806169259450415125303129)
            ·
              refine ⟨604626944587811343977347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 806169259450415125303129 604626944587811343977347)
              ·
                refine ⟨906940416881717015966021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 604626944587811343977347 906940416881717015966021)
                ·
                  refine ⟨170051328165321940493629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 906940416881717015966021 170051328165321940493629)
                  ·
                    rfl

theorem cell21_745141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_745141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745141 prefixEnd_745141 := by exact prefixLift 745141
  have htrace : WordTrace (prefixWord ++ tailWord_745141) baseStart_745141 baseEnd_745141 := by
    simpa [prefixWord, tailWord_745141, baseEnd_745141] using wordTrace_append hprefix tailTrace_745141
  have hstable : (prefixWord ++ tailWord_745141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745141).length < 2 ^ (prefixWord ++ tailWord_745141).sum := by decide
  have hdescent : baseEnd_745141 < baseStart_745141 := by decide
  rcases family_descends (prefixWord ++ tailWord_745141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745197 : List Nat := [1, 5, 1, 2, 1, 2, 3, 6]
def baseStart_745197 : Nat := 118140960795 + 745197 * 2 ^ 59
def prefixEnd_745197 : Nat := 4983230072969 + 3 ^ 40 * 745197 * 2
def baseEnd_745197 : Nat := 56688036042759429186727

theorem tailTrace_745197 : CollatzResearch.WordTrace tailWord_745197 prefixEnd_745197 56688036042759429186727 := by
  unfold tailWord_745197
  simp only [CollatzResearch.WordTrace]
  refine ⟨27179567481286013360265845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18119711654190675573510563 27179567481286013360265845)
  ·
    refine ⟨2548084451370563752524923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27179567481286013360265845 2548084451370563752524923)
    ·
      refine ⟨3822126677055845628787385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2548084451370563752524923 3822126677055845628787385)
      ·
        refine ⟨2866595007791884221590539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3822126677055845628787385 2866595007791884221590539)
        ·
          refine ⟨4299892511687826332385809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2866595007791884221590539 4299892511687826332385809)
          ·
            refine ⟨3224919383765869749289357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4299892511687826332385809 3224919383765869749289357)
            ·
              refine ⟨1209344768912201155983509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3224919383765869749289357 1209344768912201155983509)
              ·
                refine ⟨56688036042759429186727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1209344768912201155983509 56688036042759429186727)
                ·
                  rfl

theorem cell21_745197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 6].length) (baseStart_745197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745197 prefixEnd_745197 := by exact prefixLift 745197
  have htrace : WordTrace (prefixWord ++ tailWord_745197) baseStart_745197 baseEnd_745197 := by
    simpa [prefixWord, tailWord_745197, baseEnd_745197] using wordTrace_append hprefix tailTrace_745197
  have hstable : (prefixWord ++ tailWord_745197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745197).length < 2 ^ (prefixWord ++ tailWord_745197).sum := by decide
  have hdescent : baseEnd_745197 < baseStart_745197 := by decide
  rcases family_descends (prefixWord ++ tailWord_745197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745225 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 6]
def baseStart_745225 : Nat := 118140960795 + 745225 * 2 ^ 59
def prefixEnd_745225 : Nat := 4983230072969 + 3 ^ 40 * 745225 * 2
def baseEnd_745225 : Nat := 170070498109756461093457

theorem tailTrace_745225 : CollatzResearch.WordTrace tailWord_745225 prefixEnd_745225 170070498109756461093457 := by
  unfold tailWord_745225
  simp only [CollatzResearch.WordTrace]
  refine ⟨27180588725184574142285129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18120392483456382761523419 27180588725184574142285129)
  ·
    refine ⟨20385441543888430606713847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27180588725184574142285129 20385441543888430606713847)
    ·
      refine ⟨30578162315832645910070771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20385441543888430606713847 30578162315832645910070771)
      ·
        refine ⟨45867243473748968865106157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30578162315832645910070771 45867243473748968865106157)
        ·
          refine ⟨17200216302655863324414809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45867243473748968865106157 17200216302655863324414809)
          ·
            refine ⟨12900162226991897493311107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17200216302655863324414809 12900162226991897493311107)
            ·
              refine ⟨19350243340487846239966661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12900162226991897493311107 19350243340487846239966661)
              ·
                refine ⟨3628170626341471169993749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19350243340487846239966661 3628170626341471169993749)
                ·
                  refine ⟨170070498109756461093457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3628170626341471169993749 170070498109756461093457)
                  ·
                    rfl

theorem cell21_745225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_745225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745225 prefixEnd_745225 := by exact prefixLift 745225
  have htrace : WordTrace (prefixWord ++ tailWord_745225) baseStart_745225 baseEnd_745225 := by
    simpa [prefixWord, tailWord_745225, baseEnd_745225] using wordTrace_append hprefix tailTrace_745225
  have hstable : (prefixWord ++ tailWord_745225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745225).length < 2 ^ (prefixWord ++ tailWord_745225).sum := by decide
  have hdescent : baseEnd_745225 < baseStart_745225 := by decide
  rcases family_descends (prefixWord ++ tailWord_745225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745228 : List Nat := [2, 2, 1, 2, 2, 1, 3, 5, 3]
def baseStart_745228 : Nat := 118140960795 + 745228 * 2 ^ 59
def prefixEnd_745228 : Nat := 4983230072969 + 3 ^ 40 * 745228 * 2
def baseEnd_745228 : Nat := 170071182750629122543451

theorem tailTrace_745228 : CollatzResearch.WordTrace tailWord_745228 prefixEnd_745228 170071182750629122543451 := by
  unfold tailWord_745228
  simp only [CollatzResearch.WordTrace]
  refine ⟨13590349072086852827322169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18120465429449137103096225 13590349072086852827322169)
  ·
    refine ⟨10192761804065139620491627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13590349072086852827322169 10192761804065139620491627)
    ·
      refine ⟨15289142706097709430737441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10192761804065139620491627 15289142706097709430737441)
      ·
        refine ⟨11466857029573282073053081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15289142706097709430737441 11466857029573282073053081)
        ·
          refine ⟨8600142772179961554789811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11466857029573282073053081 8600142772179961554789811)
          ·
            refine ⟨12900214158269942332184717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8600142772179961554789811 12900214158269942332184717)
            ·
              refine ⟨4837580309351228374569269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12900214158269942332184717 4837580309351228374569269)
              ·
                refine ⟨453523154001677660115869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4837580309351228374569269 453523154001677660115869)
                ·
                  refine ⟨170071182750629122543451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453523154001677660115869 170071182750629122543451)
                  ·
                    rfl

theorem cell21_745228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 3].length) (baseStart_745228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745228 prefixEnd_745228 := by exact prefixLift 745228
  have htrace : WordTrace (prefixWord ++ tailWord_745228) baseStart_745228 baseEnd_745228 := by
    simpa [prefixWord, tailWord_745228, baseEnd_745228] using wordTrace_append hprefix tailTrace_745228
  have hstable : (prefixWord ++ tailWord_745228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745228).length < 2 ^ (prefixWord ++ tailWord_745228).sum := by decide
  have hdescent : baseEnd_745228 < baseStart_745228 := by decide
  rcases family_descends (prefixWord ++ tailWord_745228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745242 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 6]
def baseStart_745242 : Nat := 118140960795 + 745242 * 2 ^ 59
def prefixEnd_745242 : Nat := 4983230072969 + 3 ^ 40 * 745242 * 2
def baseEnd_745242 : Nat := 170074377741368209310089

theorem tailTrace_745242 : CollatzResearch.WordTrace tailWord_745242 prefixEnd_745242 170074377741368209310089 := by
  unfold tailWord_745242
  simp only [CollatzResearch.WordTrace]
  refine ⟨6795302191530746511413495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18120805844081990697102653 6795302191530746511413495)
  ·
    refine ⟨10192953287296119767120243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6795302191530746511413495 10192953287296119767120243)
    ·
      refine ⟨15289429930944179650680365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10192953287296119767120243 15289429930944179650680365)
      ·
        refine ⟨5733536224104067369005137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15289429930944179650680365 5733536224104067369005137)
        ·
          refine ⟨4300152168078050526753853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5733536224104067369005137 4300152168078050526753853)
          ·
            refine ⟨1612557063029268947532695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4300152168078050526753853 1612557063029268947532695)
            ·
              refine ⟨2418835594543903421299043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1612557063029268947532695 2418835594543903421299043)
              ·
                refine ⟨3628253391815855131948565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2418835594543903421299043 3628253391815855131948565)
                ·
                  refine ⟨170074377741368209310089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3628253391815855131948565 170074377741368209310089)
                  ·
                    rfl

theorem cell21_745242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_745242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745242 prefixEnd_745242 := by exact prefixLift 745242
  have htrace : WordTrace (prefixWord ++ tailWord_745242) baseStart_745242 baseEnd_745242 := by
    simpa [prefixWord, tailWord_745242, baseEnd_745242] using wordTrace_append hprefix tailTrace_745242
  have hstable : (prefixWord ++ tailWord_745242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745242).length < 2 ^ (prefixWord ++ tailWord_745242).sum := by decide
  have hdescent : baseEnd_745242 < baseStart_745242 := by decide
  rcases family_descends (prefixWord ++ tailWord_745242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745397 : List Nat := [1, 3, 3, 2, 1, 3, 2, 3, 3]
def baseStart_745397 : Nat := 118140960795 + 745397 * 2 ^ 59
def prefixEnd_745397 : Nat := 4983230072969 + 3 ^ 40 * 745397 * 2
def baseEnd_745397 : Nat := 170109750853122384226439

theorem tailTrace_745397 : CollatzResearch.WordTrace tailWord_745397 prefixEnd_745397 170109750853122384226439 := by
  unfold tailWord_745397
  simp only [CollatzResearch.WordTrace]
  refine ⟨27186862080561447517546445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18124574720374298345030963 27186862080561447517546445)
  ·
    refine ⟨10195073280210542819079917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27186862080561447517546445 10195073280210542819079917)
    ·
      refine ⟨3823152480078953557154969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10195073280210542819079917 3823152480078953557154969)
      ·
        refine ⟨2867364360059215167866227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3823152480078953557154969 2867364360059215167866227)
        ·
          refine ⟨4301046540088822751799341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2867364360059215167866227 4301046540088822751799341)
          ·
            refine ⟨1612892452533308531924753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4301046540088822751799341 1612892452533308531924753)
            ·
              refine ⟨1209669339399981398943565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1612892452533308531924753 1209669339399981398943565)
              ·
                refine ⟨453626002274993024603837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1209669339399981398943565 453626002274993024603837)
                ·
                  refine ⟨170109750853122384226439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453626002274993024603837 170109750853122384226439)
                  ·
                    rfl

theorem cell21_745397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 3].length) (baseStart_745397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745397 prefixEnd_745397 := by exact prefixLift 745397
  have htrace : WordTrace (prefixWord ++ tailWord_745397) baseStart_745397 baseEnd_745397 := by
    simpa [prefixWord, tailWord_745397, baseEnd_745397] using wordTrace_append hprefix tailTrace_745397
  have hstable : (prefixWord ++ tailWord_745397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745397).length < 2 ^ (prefixWord ++ tailWord_745397).sum := by decide
  have hdescent : baseEnd_745397 < baseStart_745397 := by decide
  rcases family_descends (prefixWord ++ tailWord_745397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745439 : List Nat := [1, 1, 2, 3, 4, 1, 2, 2, 5]
def baseStart_745439 : Nat := 118140960795 + 745439 * 2 ^ 59
def prefixEnd_745439 : Nat := 4983230072969 + 3 ^ 40 * 745439 * 2
def baseEnd_745439 : Nat := 170119335825339644526353

theorem tailTrace_745439 : CollatzResearch.WordTrace tailWord_745439 prefixEnd_745439 170119335825339644526353 := by
  unfold tailWord_745439
  simp only [CollatzResearch.WordTrace]
  refine ⟨27188393946409288690575371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18125595964272859127050247 27188393946409288690575371)
  ·
    refine ⟨40782590919613933035863057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27188393946409288690575371 40782590919613933035863057)
    ·
      refine ⟨30586943189710449776897293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40782590919613933035863057 30586943189710449776897293)
      ·
        refine ⟨11470103696141418666336485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30586943189710449776897293 11470103696141418666336485)
        ·
          refine ⟨2150644443026515999938091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11470103696141418666336485 2150644443026515999938091)
          ·
            refine ⟨3225966664539773999907137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2150644443026515999938091 3225966664539773999907137)
            ·
              refine ⟨2419474998404830499930353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3225966664539773999907137 2419474998404830499930353)
              ·
                refine ⟨1814606248803622874947765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2419474998404830499930353 1814606248803622874947765)
                ·
                  refine ⟨170119335825339644526353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1814606248803622874947765 170119335825339644526353)
                  ·
                    rfl

theorem cell21_745439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 5].length) (baseStart_745439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745439 prefixEnd_745439 := by exact prefixLift 745439
  have htrace : WordTrace (prefixWord ++ tailWord_745439) baseStart_745439 baseEnd_745439 := by
    simpa [prefixWord, tailWord_745439, baseEnd_745439] using wordTrace_append hprefix tailTrace_745439
  have hstable : (prefixWord ++ tailWord_745439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745439).length < 2 ^ (prefixWord ++ tailWord_745439).sum := by decide
  have hdescent : baseEnd_745439 < baseStart_745439 := by decide
  rcases family_descends (prefixWord ++ tailWord_745439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745442 : List Nat := [3, 3, 3, 1, 2, 1, 1, 7]
def baseStart_745442 : Nat := 118140960795 + 745442 * 2 ^ 59
def prefixEnd_745442 : Nat := 4983230072969 + 3 ^ 40 * 745442 * 2
def baseEnd_745442 : Nat := 56706673488737435325449

theorem tailTrace_745442 : CollatzResearch.WordTrace tailWord_745442 prefixEnd_745442 56706673488737435325449 := by
  unfold tailWord_745442
  simp only [CollatzResearch.WordTrace]
  refine ⟨6797125841349605050733645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18125668910265613468623053 6797125841349605050733645)
  ·
    refine ⟨2548922190506101894025117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6797125841349605050733645 2548922190506101894025117)
    ·
      refine ⟨955845821439788210259419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2548922190506101894025117 955845821439788210259419)
      ·
        refine ⟨1433768732159682315389129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 955845821439788210259419 1433768732159682315389129)
        ·
          refine ⟨1075326549119761736541847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1433768732159682315389129 1075326549119761736541847)
          ·
            refine ⟨1612989823679642604812771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1075326549119761736541847 1612989823679642604812771)
            ·
              refine ⟨2419484735519463907219157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1612989823679642604812771 2419484735519463907219157)
              ·
                refine ⟨56706673488737435325449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2419484735519463907219157 56706673488737435325449)
                ·
                  rfl

theorem cell21_745442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_745442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745442 prefixEnd_745442 := by exact prefixLift 745442
  have htrace : WordTrace (prefixWord ++ tailWord_745442) baseStart_745442 baseEnd_745442 := by
    simpa [prefixWord, tailWord_745442, baseEnd_745442] using wordTrace_append hprefix tailTrace_745442
  have hstable : (prefixWord ++ tailWord_745442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745442).length < 2 ^ (prefixWord ++ tailWord_745442).sum := by decide
  have hdescent : baseEnd_745442 < baseStart_745442 := by decide
  rcases family_descends (prefixWord ++ tailWord_745442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745456 : List Nat := [2, 1, 1, 1, 3, 2, 5, 3, 3]
def baseStart_745456 : Nat := 118140960795 + 745456 * 2 ^ 59
def prefixEnd_745456 : Nat := 4983230072969 + 3 ^ 40 * 745456 * 2
def baseEnd_745456 : Nat := 170123215456951392742985

theorem tailTrace_745456 : CollatzResearch.WordTrace tailWord_745456 prefixEnd_745456 170123215456951392742985 := by
  unfold tailWord_745456
  simp only [CollatzResearch.WordTrace]
  refine ⟨13594506993673850296972111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18126009324898467062629481 13594506993673850296972111)
  ·
    refine ⟨20391760490510775445458167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13594506993673850296972111 20391760490510775445458167)
    ·
      refine ⟨30587640735766163168187251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20391760490510775445458167 30587640735766163168187251)
      ·
        refine ⟨45881461103649244752280877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30587640735766163168187251 45881461103649244752280877)
        ·
          refine ⟨17205547913868466782105329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45881461103649244752280877 17205547913868466782105329)
          ·
            refine ⟨12904160935401350086578997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17205547913868466782105329 12904160935401350086578997)
            ·
              refine ⟨1209765087693876570616781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12904160935401350086578997 1209765087693876570616781)
              ·
                refine ⟨453661907885203713981293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1209765087693876570616781 453661907885203713981293)
                ·
                  refine ⟨170123215456951392742985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453661907885203713981293 170123215456951392742985)
                  ·
                    rfl

theorem cell21_745456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 3].length) (baseStart_745456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745456 prefixEnd_745456 := by exact prefixLift 745456
  have htrace : WordTrace (prefixWord ++ tailWord_745456) baseStart_745456 baseEnd_745456 := by
    simpa [prefixWord, tailWord_745456, baseEnd_745456] using wordTrace_append hprefix tailTrace_745456
  have hstable : (prefixWord ++ tailWord_745456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745456).length < 2 ^ (prefixWord ++ tailWord_745456).sum := by decide
  have hdescent : baseEnd_745456 < baseStart_745456 := by decide
  rcases family_descends (prefixWord ++ tailWord_745456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745467 : List Nat := [1, 1, 1, 1, 1, 3, 13]
def baseStart_745467 : Nat := 118140960795 + 745467 * 2 ^ 59
def prefixEnd_745467 : Nat := 4983230072969 + 3 ^ 40 * 745467 * 2
def baseEnd_745467 : Nat := 18902858422979757562181

theorem tailTrace_745467 : CollatzResearch.WordTrace tailWord_745467 prefixEnd_745467 18902858422979757562181 := by
  unfold tailWord_745467
  simp only [CollatzResearch.WordTrace]
  refine ⟨27189415190307849472594655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18126276793538566315063103 27189415190307849472594655)
  ·
    refine ⟨40784122785461774208891983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27189415190307849472594655 40784122785461774208891983)
    ·
      refine ⟨61176184178192661313337975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40784122785461774208891983 61176184178192661313337975)
      ·
        refine ⟨91764276267288991970006963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61176184178192661313337975 91764276267288991970006963)
        ·
          refine ⟨137646414400933487955010445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91764276267288991970006963 137646414400933487955010445)
          ·
            refine ⟨51617405400350057983128917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137646414400933487955010445 51617405400350057983128917)
            ·
              refine ⟨18902858422979757562181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 51617405400350057983128917 18902858422979757562181)
              ·
                rfl

theorem cell21_745467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 13].length) (baseStart_745467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745467 prefixEnd_745467 := by exact prefixLift 745467
  have htrace : WordTrace (prefixWord ++ tailWord_745467) baseStart_745467 baseEnd_745467 := by
    simpa [prefixWord, tailWord_745467, baseEnd_745467] using wordTrace_append hprefix tailTrace_745467
  have hstable : (prefixWord ++ tailWord_745467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745467).length < 2 ^ (prefixWord ++ tailWord_745467).sum := by decide
  have hdescent : baseEnd_745467 < baseStart_745467 := by decide
  rcases family_descends (prefixWord ++ tailWord_745467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745473 : List Nat := [1, 2, 4, 1, 2, 1, 5, 2, 3]
def baseStart_745473 : Nat := 118140960795 + 745473 * 2 ^ 59
def prefixEnd_745473 : Nat := 4983230072969 + 3 ^ 40 * 745473 * 2
def baseEnd_745473 : Nat := 170127095088563140959617

theorem tailTrace_745473 : CollatzResearch.WordTrace tailWord_745473 prefixEnd_745473 170127095088563140959617 := by
  unfold tailWord_745473
  simp only [CollatzResearch.WordTrace]
  refine ⟨27189634028286112497313073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18126422685524074998208715 27189634028286112497313073)
  ·
    refine ⟨20392225521214584372984805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27189634028286112497313073 20392225521214584372984805)
    ·
      refine ⟨3823542285227734569934651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20392225521214584372984805 3823542285227734569934651)
      ·
        refine ⟨5735313427841601854901977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3823542285227734569934651 5735313427841601854901977)
        ·
          refine ⟨4301485070881201391176483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5735313427841601854901977 4301485070881201391176483)
          ·
            refine ⟨6452227606321802086764725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4301485070881201391176483 6452227606321802086764725)
            ·
              refine ⟨604896338092668945634193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6452227606321802086764725 604896338092668945634193)
              ·
                refine ⟨453672253569501709225645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 604896338092668945634193 453672253569501709225645)
                ·
                  refine ⟨170127095088563140959617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453672253569501709225645 170127095088563140959617)
                  ·
                    rfl

theorem cell21_745473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 3].length) (baseStart_745473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745473 prefixEnd_745473 := by exact prefixLift 745473
  have htrace : WordTrace (prefixWord ++ tailWord_745473) baseStart_745473 baseEnd_745473 := by
    simpa [prefixWord, tailWord_745473, baseEnd_745473] using wordTrace_append hprefix tailTrace_745473
  have hstable : (prefixWord ++ tailWord_745473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745473).length < 2 ^ (prefixWord ++ tailWord_745473).sum := by decide
  have hdescent : baseEnd_745473 < baseStart_745473 := by decide
  rcases family_descends (prefixWord ++ tailWord_745473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745484 : List Nat := [2, 2, 1, 2, 3, 1, 4, 6]
def baseStart_745484 : Nat := 118140960795 + 745484 * 2 ^ 59
def prefixEnd_745484 : Nat := 4983230072969 + 3 ^ 40 * 745484 * 2
def baseEnd_745484 : Nat := 56709868479476522092087

theorem tailTrace_745484 : CollatzResearch.WordTrace tailWord_745484 prefixEnd_745484 56709868479476522092087 := by
  unfold tailWord_745484
  simp only [CollatzResearch.WordTrace]
  refine ⟨13595017615623130687981753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18126690154164174250642337 13595017615623130687981753)
  ·
    refine ⟨10196263211717348015986315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13595017615623130687981753 10196263211717348015986315)
    ·
      refine ⟨15294394817576022023979473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10196263211717348015986315 15294394817576022023979473)
      ·
        refine ⟨11470796113182016517984605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15294394817576022023979473 11470796113182016517984605)
        ·
          refine ⟨4301548542443256194244227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11470796113182016517984605 4301548542443256194244227)
          ·
            refine ⟨6452322813664884291366341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4301548542443256194244227 6452322813664884291366341)
            ·
              refine ⟨1209810527562165804631189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6452322813664884291366341 1209810527562165804631189)
              ·
                refine ⟨56709868479476522092087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1209810527562165804631189 56709868479476522092087)
                ·
                  rfl

theorem cell21_745484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 6].length) (baseStart_745484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745484 prefixEnd_745484 := by exact prefixLift 745484
  have htrace : WordTrace (prefixWord ++ tailWord_745484) baseStart_745484 baseEnd_745484 := by
    simpa [prefixWord, tailWord_745484, baseEnd_745484] using wordTrace_append hprefix tailTrace_745484
  have hstable : (prefixWord ++ tailWord_745484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745484).length < 2 ^ (prefixWord ++ tailWord_745484).sum := by decide
  have hdescent : baseEnd_745484 < baseStart_745484 := by decide
  rcases family_descends (prefixWord ++ tailWord_745484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745524 : List Nat := [2, 5, 1, 2, 3, 1, 2, 2, 3]
def baseStart_745524 : Nat := 118140960795 + 745524 * 2 ^ 59
def prefixEnd_745524 : Nat := 4983230072969 + 3 ^ 40 * 745524 * 2
def baseEnd_745524 : Nat := 170138733983398385609513

theorem tailTrace_745524 : CollatzResearch.WordTrace tailWord_745524 prefixEnd_745524 170138733983398385609513 := by
  unfold tailWord_745524
  simp only [CollatzResearch.WordTrace]
  refine ⟨13595747075550674103709813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18127662767400898804946417 13595747075550674103709813)
  ·
    refine ⟨1274601288332875697222795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13595747075550674103709813 1274601288332875697222795)
    ·
      refine ⟨1911901932499313545834193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1274601288332875697222795 1911901932499313545834193)
      ·
        refine ⟨1433926449374485159375645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1911901932499313545834193 1433926449374485159375645)
        ·
          refine ⟨537722418515431934765867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1433926449374485159375645 537722418515431934765867)
          ·
            refine ⟨806583627773147902148801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537722418515431934765867 806583627773147902148801)
            ·
              refine ⟨604937720829860926611601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 806583627773147902148801 604937720829860926611601)
              ·
                refine ⟨453703290622395694958701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 604937720829860926611601 453703290622395694958701)
                ·
                  refine ⟨170138733983398385609513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453703290622395694958701 170138733983398385609513)
                  ·
                    rfl

theorem cell21_745524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_745524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745524 prefixEnd_745524 := by exact prefixLift 745524
  have htrace : WordTrace (prefixWord ++ tailWord_745524) baseStart_745524 baseEnd_745524 := by
    simpa [prefixWord, tailWord_745524, baseEnd_745524] using wordTrace_append hprefix tailTrace_745524
  have hstable : (prefixWord ++ tailWord_745524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745524).length < 2 ^ (prefixWord ++ tailWord_745524).sum := by decide
  have hdescent : baseEnd_745524 < baseStart_745524 := by decide
  rcases family_descends (prefixWord ++ tailWord_745524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745532 : List Nat := [2, 2, 2, 2, 2, 1, 3, 4, 3]
def baseStart_745532 : Nat := 118140960795 + 745532 * 2 ^ 59
def prefixEnd_745532 : Nat := 4983230072969 + 3 ^ 40 * 745532 * 2
def baseEnd_745532 : Nat := 170140559692392149476163

theorem tailTrace_745532 : CollatzResearch.WordTrace tailWord_745532 prefixEnd_745532 170140559692392149476163 := by
  unfold tailWord_745532
  simp only [CollatzResearch.WordTrace]
  refine ⟨13595892967536182786855425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18127857290048243715807233 13595892967536182786855425)
  ·
    refine ⟨10196919725652137090141569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13595892967536182786855425 10196919725652137090141569)
    ·
      refine ⟨7647689794239102817606177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10196919725652137090141569 7647689794239102817606177)
      ·
        refine ⟨5735767345679327113204633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7647689794239102817606177 5735767345679327113204633)
        ·
          refine ⟨4301825509259495334903475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5735767345679327113204633 4301825509259495334903475)
          ·
            refine ⟨6452738263889243002355213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4301825509259495334903475 6452738263889243002355213)
            ·
              refine ⟨2419776848958466125883205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6452738263889243002355213 2419776848958466125883205)
              ·
                refine ⟨453708159179712398603101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2419776848958466125883205 453708159179712398603101)
                ·
                  refine ⟨170140559692392149476163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453708159179712398603101 170140559692392149476163)
                  ·
                    rfl

theorem cell21_745532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 3].length) (baseStart_745532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745532 prefixEnd_745532 := by exact prefixLift 745532
  have htrace : WordTrace (prefixWord ++ tailWord_745532) baseStart_745532 baseEnd_745532 := by
    simpa [prefixWord, tailWord_745532, baseEnd_745532] using wordTrace_append hprefix tailTrace_745532
  have hstable : (prefixWord ++ tailWord_745532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745532).length < 2 ^ (prefixWord ++ tailWord_745532).sum := by decide
  have hdescent : baseEnd_745532 < baseStart_745532 := by decide
  rcases family_descends (prefixWord ++ tailWord_745532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745591 : List Nat := [1, 1, 3, 1, 1, 6, 2, 1, 5]
def baseStart_745591 : Nat := 118140960795 + 745591 * 2 ^ 59
def prefixEnd_745591 : Nat := 4983230072969 + 3 ^ 40 * 745591 * 2
def baseEnd_745591 : Nat := 170154024296221157992709

theorem tailTrace_745591 : CollatzResearch.WordTrace tailWord_745591 prefixEnd_745591 170154024296221157992709 := by
  unfold tailWord_745591
  simp only [CollatzResearch.WordTrace]
  refine ⟨27193937841858618650108627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18129291894572412433405751 27193937841858618650108627)
  ·
    refine ⟨40790906762787927975162941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27193937841858618650108627 40790906762787927975162941)
    ·
      refine ⟨15296590036045472990686103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40790906762787927975162941 15296590036045472990686103)
      ·
        refine ⟨22944885054068209486029155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15296590036045472990686103 22944885054068209486029155)
        ·
          refine ⟨34417327581102314229043733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22944885054068209486029155 34417327581102314229043733)
          ·
            refine ⟨1613312230364170979486425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34417327581102314229043733 1613312230364170979486425)
            ·
              refine ⟨1209984172773128234614819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1613312230364170979486425 1209984172773128234614819)
              ·
                refine ⟨1814976259159692351922229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1209984172773128234614819 1814976259159692351922229)
                ·
                  refine ⟨170154024296221157992709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1814976259159692351922229 170154024296221157992709)
                  ·
                    rfl

theorem cell21_745591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 5].length) (baseStart_745591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745591 prefixEnd_745591 := by exact prefixLift 745591
  have htrace : WordTrace (prefixWord ++ tailWord_745591) baseStart_745591 baseEnd_745591 := by
    simpa [prefixWord, tailWord_745591, baseEnd_745591] using wordTrace_append hprefix tailTrace_745591
  have hstable : (prefixWord ++ tailWord_745591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745591).length < 2 ^ (prefixWord ++ tailWord_745591).sum := by decide
  have hdescent : baseEnd_745591 < baseStart_745591 := by decide
  rcases family_descends (prefixWord ++ tailWord_745591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745642 : List Nat := [3, 1, 5, 1, 3, 1, 1, 1, 5]
def baseStart_745642 : Nat := 118140960795 + 745642 * 2 ^ 59
def prefixEnd_745642 : Nat := 4983230072969 + 3 ^ 40 * 745642 * 2
def baseEnd_745642 : Nat := 170165663191056402642605

theorem tailTrace_745642 : CollatzResearch.WordTrace tailWord_745642 prefixEnd_745642 170165663191056402642605 := by
  unfold tailWord_745642
  simp only [CollatzResearch.WordTrace]
  refine ⟨6798949491168463590053795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18130531976449236240143453 6798949491168463590053795)
  ·
    refine ⟨10198424236752695385080693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6798949491168463590053795 10198424236752695385080693)
    ·
      refine ⟨956102272195565192351315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10198424236752695385080693 956102272195565192351315)
      ·
        refine ⟨1434153408293347788526973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 956102272195565192351315 1434153408293347788526973)
        ·
          refine ⟨537807528110005420697615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1434153408293347788526973 537807528110005420697615)
          ·
            refine ⟨806711292165008131046423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537807528110005420697615 806711292165008131046423)
            ·
              refine ⟨1210066938247512196569635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 806711292165008131046423 1210066938247512196569635)
              ·
                refine ⟨1815100407371268294854453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1210066938247512196569635 1815100407371268294854453)
                ·
                  refine ⟨170165663191056402642605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1815100407371268294854453 170165663191056402642605)
                  ·
                    rfl

theorem cell21_745642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 5].length) (baseStart_745642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745642 prefixEnd_745642 := by exact prefixLift 745642
  have htrace : WordTrace (prefixWord ++ tailWord_745642) baseStart_745642 baseEnd_745642 := by
    simpa [prefixWord, tailWord_745642, baseEnd_745642] using wordTrace_append hprefix tailTrace_745642
  have hstable : (prefixWord ++ tailWord_745642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745642).length < 2 ^ (prefixWord ++ tailWord_745642).sum := by decide
  have hdescent : baseEnd_745642 < baseStart_745642 := by decide
  rcases family_descends (prefixWord ++ tailWord_745642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745701 : List Nat := [1, 3, 1, 4, 2, 1, 4, 2, 3]
def baseStart_745701 : Nat := 118140960795 + 745701 * 2 ^ 59
def prefixEnd_745701 : Nat := 4983230072969 + 3 ^ 40 * 745701 * 2
def baseEnd_745701 : Nat := 170179127794885411159151

theorem tailTrace_745701 : CollatzResearch.WordTrace tailWord_745701 prefixEnd_745701 170179127794885411159151 := by
  unfold tailWord_745701
  simp only [CollatzResearch.WordTrace]
  refine ⟨27197949871460107436612957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18131966580973404957741971 27197949871460107436612957)
  ·
    refine ⟨10199231201797540288729859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27197949871460107436612957 10199231201797540288729859)
    ·
      refine ⟨15298846802696310433094789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10199231201797540288729859 15298846802696310433094789)
      ·
        refine ⟨2868533775505558206205273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15298846802696310433094789 2868533775505558206205273)
        ·
          refine ⟨2151400331629168654653955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2868533775505558206205273 2151400331629168654653955)
          ·
            refine ⟨3227100497443752981980933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2151400331629168654653955 3227100497443752981980933)
            ·
              refine ⟨605081343270703684121425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3227100497443752981980933 605081343270703684121425)
              ·
                refine ⟨453811007453027763091069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605081343270703684121425 453811007453027763091069)
                ·
                  refine ⟨170179127794885411159151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453811007453027763091069 170179127794885411159151)
                  ·
                    rfl

theorem cell21_745701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 3].length) (baseStart_745701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745701 prefixEnd_745701 := by exact prefixLift 745701
  have htrace : WordTrace (prefixWord ++ tailWord_745701) baseStart_745701 baseEnd_745701 := by
    simpa [prefixWord, tailWord_745701, baseEnd_745701] using wordTrace_append hprefix tailTrace_745701
  have hstable : (prefixWord ++ tailWord_745701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745701).length < 2 ^ (prefixWord ++ tailWord_745701).sum := by decide
  have hdescent : baseEnd_745701 < baseStart_745701 := by decide
  rcases family_descends (prefixWord ++ tailWord_745701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745760 : List Nat := [2, 1, 1, 5, 2, 1, 2, 4, 3]
def baseStart_745760 : Nat := 118140960795 + 745760 * 2 ^ 59
def prefixEnd_745760 : Nat := 4983230072969 + 3 ^ 40 * 745760 * 2
def baseEnd_745760 : Nat := 170192592398714419675697

theorem tailTrace_745760 : CollatzResearch.WordTrace tailWord_745760 prefixEnd_745760 170192592398714419675697 := by
  unfold tailWord_745760
  simp only [CollatzResearch.WordTrace]
  refine ⟨13600050889123180256505367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18133401185497573675340489 13600050889123180256505367)
  ·
    refine ⟨20400076333684770384758051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13600050889123180256505367 20400076333684770384758051)
    ·
      refine ⟨30600114500527155577137077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20400076333684770384758051 30600114500527155577137077)
      ·
        refine ⟨2868760734424420835356601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30600114500527155577137077 2868760734424420835356601)
        ·
          refine ⟨2151570550818315626517451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2868760734424420835356601 2151570550818315626517451)
          ·
            refine ⟨3227355826227473439776177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2151570550818315626517451 3227355826227473439776177)
            ·
              refine ⟨2420516869670605079832133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3227355826227473439776177 2420516869670605079832133)
              ·
                refine ⟨453846913063238452468525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2420516869670605079832133 453846913063238452468525)
                ·
                  refine ⟨170192592398714419675697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453846913063238452468525 170192592398714419675697)
                  ·
                    rfl

theorem cell21_745760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 3].length) (baseStart_745760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745760 prefixEnd_745760 := by exact prefixLift 745760
  have htrace : WordTrace (prefixWord ++ tailWord_745760) baseStart_745760 baseEnd_745760 := by
    simpa [prefixWord, tailWord_745760, baseEnd_745760] using wordTrace_append hprefix tailTrace_745760
  have hstable : (prefixWord ++ tailWord_745760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745760).length < 2 ^ (prefixWord ++ tailWord_745760).sum := by decide
  have hdescent : baseEnd_745760 < baseStart_745760 := by decide
  rcases family_descends (prefixWord ++ tailWord_745760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745833 : List Nat := [1, 2, 1, 1, 1, 3, 5, 3, 4]
def baseStart_745833 : Nat := 118140960795 + 745833 * 2 ^ 59
def prefixEnd_745833 : Nat := 4983230072969 + 3 ^ 40 * 745833 * 2
def baseEnd_745833 : Nat := 170209251993282514958881

theorem tailTrace_745833 : CollatzResearch.WordTrace tailWord_745833 prefixEnd_745833 170209251993282514958881 := by
  unfold tailWord_745833
  simp only [CollatzResearch.WordTrace]
  refine ⟨27202764306981893980418153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18135176204654595986945435 27202764306981893980418153)
  ·
    refine ⟨20402073230236420485313615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27202764306981893980418153 20402073230236420485313615)
    ·
      refine ⟨30603109845354630727970423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20402073230236420485313615 30603109845354630727970423)
      ·
        refine ⟨45904664768031946091955635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30603109845354630727970423 45904664768031946091955635)
        ·
          refine ⟨68856997152047919137933453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45904664768031946091955635 68856997152047919137933453)
          ·
            refine ⟨25821373932017969676725045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68856997152047919137933453 25821373932017969676725045)
            ·
              refine ⟨2420753806126684657192973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25821373932017969676725045 2420753806126684657192973)
              ·
                refine ⟨907782677297506746447365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2420753806126684657192973 907782677297506746447365)
                ·
                  refine ⟨170209251993282514958881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 907782677297506746447365 170209251993282514958881)
                  ·
                    rfl

theorem cell21_745833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 4].length) (baseStart_745833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745833 prefixEnd_745833 := by exact prefixLift 745833
  have htrace : WordTrace (prefixWord ++ tailWord_745833) baseStart_745833 baseEnd_745833 := by
    simpa [prefixWord, tailWord_745833, baseEnd_745833] using wordTrace_append hprefix tailTrace_745833
  have hstable : (prefixWord ++ tailWord_745833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745833).length < 2 ^ (prefixWord ++ tailWord_745833).sum := by decide
  have hdescent : baseEnd_745833 < baseStart_745833 := by decide
  rcases family_descends (prefixWord ++ tailWord_745833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745870 : List Nat := [4, 1, 1, 4, 1, 3, 2, 2, 3]
def baseStart_745870 : Nat := 118140960795 + 745870 * 2 ^ 59
def prefixEnd_745870 : Nat := 4983230072969 + 3 ^ 40 * 745870 * 2
def baseEnd_745870 : Nat := 170217695897378672842139

theorem tailTrace_745870 : CollatzResearch.WordTrace tailWord_745870 prefixEnd_745870 170217695897378672842139 := by
  unfold tailWord_745870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3400514225980981162439383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18136075871898566199676709 3400514225980981162439383)
  ·
    refine ⟨5100771338971471743659075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3400514225980981162439383 5100771338971471743659075)
    ·
      refine ⟨7651157008457207615488613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5100771338971471743659075 7651157008457207615488613)
      ·
        refine ⟨1434591939085726427904115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7651157008457207615488613 1434591939085726427904115)
        ·
          refine ⟨2151887908628589641856173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1434591939085726427904115 2151887908628589641856173)
          ·
            refine ⟨806957965735721115696065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2151887908628589641856173 806957965735721115696065)
            ·
              refine ⟨605218474301790836772049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 806957965735721115696065 605218474301790836772049)
              ·
                refine ⟨453913855726343127579037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605218474301790836772049 453913855726343127579037)
                ·
                  refine ⟨170217695897378672842139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453913855726343127579037 170217695897378672842139)
                  ·
                    rfl

theorem cell21_745870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_745870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745870 prefixEnd_745870 := by exact prefixLift 745870
  have htrace : WordTrace (prefixWord ++ tailWord_745870) baseStart_745870 baseEnd_745870 := by
    simpa [prefixWord, tailWord_745870, baseEnd_745870] using wordTrace_append hprefix tailTrace_745870
  have hstable : (prefixWord ++ tailWord_745870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745870).length < 2 ^ (prefixWord ++ tailWord_745870).sum := by decide
  have hdescent : baseEnd_745870 < baseStart_745870 := by decide
  rcases family_descends (prefixWord ++ tailWord_745870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745895 : List Nat := [1, 1, 6, 1, 1, 3, 1, 2, 5]
def baseStart_745895 : Nat := 118140960795 + 745895 * 2 ^ 59
def prefixEnd_745895 : Nat := 4983230072969 + 3 ^ 40 * 745895 * 2
def baseEnd_745895 : Nat := 170223401237984184925421

theorem tailTrace_745895 : CollatzResearch.WordTrace tailWord_745895 prefixEnd_745895 170223401237984184925421 := by
  unfold tailWord_745895
  simp only [CollatzResearch.WordTrace]
  refine ⟨27205025632757278569175139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18136683755171519046116759 27205025632757278569175139)
  ·
    refine ⟨40807538449135917853762709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27205025632757278569175139 40807538449135917853762709)
    ·
      refine ⟨1912853364803246149395127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40807538449135917853762709 1912853364803246149395127)
      ·
        refine ⟨2869280047204869224092691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1912853364803246149395127 2869280047204869224092691)
        ·
          refine ⟨4303920070807303836139037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2869280047204869224092691 4303920070807303836139037)
          ·
            refine ⟨1613970026552738938552139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4303920070807303836139037 1613970026552738938552139)
            ·
              refine ⟨2420955039829108407828209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1613970026552738938552139 2420955039829108407828209)
              ·
                refine ⟨1815716279871831305871157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2420955039829108407828209 1815716279871831305871157)
                ·
                  refine ⟨170223401237984184925421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1815716279871831305871157 170223401237984184925421)
                  ·
                    rfl

theorem cell21_745895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 5].length) (baseStart_745895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745895 prefixEnd_745895 := by exact prefixLift 745895
  have htrace : WordTrace (prefixWord ++ tailWord_745895) baseStart_745895 baseEnd_745895 := by
    simpa [prefixWord, tailWord_745895, baseEnd_745895] using wordTrace_append hprefix tailTrace_745895
  have hstable : (prefixWord ++ tailWord_745895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745895).length < 2 ^ (prefixWord ++ tailWord_745895).sum := by decide
  have hdescent : baseEnd_745895 < baseStart_745895 := by decide
  rcases family_descends (prefixWord ++ tailWord_745895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745968 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 8]
def baseStart_745968 : Nat := 118140960795 + 745968 * 2 ^ 59
def prefixEnd_745968 : Nat := 4983230072969 + 3 ^ 40 * 745968 * 2
def baseEnd_745968 : Nat := 170240060832552280208605

theorem tailTrace_745968 : CollatzResearch.WordTrace tailWord_745968 prefixEnd_745968 170240060832552280208605 := by
  unfold tailWord_745968
  simp only [CollatzResearch.WordTrace]
  refine ⟨13603844080746406018291279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18138458774328541357721705 13603844080746406018291279)
  ·
    refine ⟨20405766121119609027436919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13603844080746406018291279 20405766121119609027436919)
    ·
      refine ⟨30608649181679413541155379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20405766121119609027436919 30608649181679413541155379)
      ·
        refine ⟨45912973772519120311733069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30608649181679413541155379 45912973772519120311733069)
        ·
          refine ⟨17217365164694670116899901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45912973772519120311733069 17217365164694670116899901)
          ·
            refine ⟨6456511936760501293837463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17217365164694670116899901 6456511936760501293837463)
            ·
              refine ⟨9684767905140751940756195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6456511936760501293837463 9684767905140751940756195)
              ·
                refine ⟨14527151857711127911134293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9684767905140751940756195 14527151857711127911134293)
                ·
                  refine ⟨170240060832552280208605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14527151857711127911134293 170240060832552280208605)
                  ·
                    rfl

theorem cell21_745968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_745968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745968 prefixEnd_745968 := by exact prefixLift 745968
  have htrace : WordTrace (prefixWord ++ tailWord_745968) baseStart_745968 baseEnd_745968 := by
    simpa [prefixWord, tailWord_745968, baseEnd_745968] using wordTrace_append hprefix tailTrace_745968
  have hstable : (prefixWord ++ tailWord_745968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745968).length < 2 ^ (prefixWord ++ tailWord_745968).sum := by decide
  have hdescent : baseEnd_745968 < baseStart_745968 := by decide
  rcases family_descends (prefixWord ++ tailWord_745968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745985 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 6]
def baseStart_745985 : Nat := 118140960795 + 745985 * 2 ^ 59
def prefixEnd_745985 : Nat := 4983230072969 + 3 ^ 40 * 745985 * 2
def baseEnd_745985 : Nat := 170243940464164028425237

theorem tailTrace_745985 : CollatzResearch.WordTrace tailWord_745985 prefixEnd_745985 170243940464164028425237 := by
  unfold tailWord_745985
  simp only [CollatzResearch.WordTrace]
  refine ⟨27208308202431223939951409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18138872134954149293300939 27208308202431223939951409)
  ·
    refine ⟨20406231151823417954963557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27208308202431223939951409 20406231151823417954963557)
    ·
      refine ⟨3826168340966890866555667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20406231151823417954963557 3826168340966890866555667)
      ·
        refine ⟨5739252511450336299833501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3826168340966890866555667 5739252511450336299833501)
        ·
          refine ⟨2152219691793876112437563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5739252511450336299833501 2152219691793876112437563)
          ·
            refine ⟨3228329537690814168656345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152219691793876112437563 3228329537690814168656345)
            ·
              refine ⟨2421247153268110626492259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3228329537690814168656345 2421247153268110626492259)
              ·
                refine ⟨3631870729902165939738389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2421247153268110626492259 3631870729902165939738389)
                ·
                  refine ⟨170243940464164028425237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3631870729902165939738389 170243940464164028425237)
                  ·
                    rfl

theorem cell21_745985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_745985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745985 prefixEnd_745985 := by exact prefixLift 745985
  have htrace : WordTrace (prefixWord ++ tailWord_745985) baseStart_745985 baseEnd_745985 := by
    simpa [prefixWord, tailWord_745985, baseEnd_745985] using wordTrace_append hprefix tailTrace_745985
  have hstable : (prefixWord ++ tailWord_745985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745985).length < 2 ^ (prefixWord ++ tailWord_745985).sum := by decide
  have hdescent : baseEnd_745985 < baseStart_745985 := by decide
  rcases family_descends (prefixWord ++ tailWord_745985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_745988 : List Nat := [2, 3, 2, 3, 1, 3, 1, 1, 5]
def baseStart_745988 : Nat := 118140960795 + 745988 * 2 ^ 59
def prefixEnd_745988 : Nat := 4983230072969 + 3 ^ 40 * 745988 * 2
def baseEnd_745988 : Nat := 170244625105036689875231

theorem tailTrace_745988 : CollatzResearch.WordTrace tailWord_745988 prefixEnd_745988 170244625105036689875231 := by
  unfold tailWord_745988
  simp only [CollatzResearch.WordTrace]
  refine ⟨13604208810710177726155309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18138945080946903634873745 13604208810710177726155309)
  ·
    refine ⟨5101578304016316647308241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13604208810710177726155309 5101578304016316647308241)
    ·
      refine ⟨3826183728012237485481181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5101578304016316647308241 3826183728012237485481181)
      ·
        refine ⟨1434818898004589057055443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3826183728012237485481181 1434818898004589057055443)
        ·
          refine ⟨2152228347006883585583165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1434818898004589057055443 2152228347006883585583165)
          ·
            refine ⟨807085630127581344593687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2152228347006883585583165 807085630127581344593687)
            ·
              refine ⟨1210628445191372016890531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807085630127581344593687 1210628445191372016890531)
              ·
                refine ⟨1815942667787058025335797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1210628445191372016890531 1815942667787058025335797)
                ·
                  refine ⟨170244625105036689875231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1815942667787058025335797 170244625105036689875231)
                  ·
                    rfl

theorem cell21_745988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_745988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_745988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_745988 prefixEnd_745988 := by exact prefixLift 745988
  have htrace : WordTrace (prefixWord ++ tailWord_745988) baseStart_745988 baseEnd_745988 := by
    simpa [prefixWord, tailWord_745988, baseEnd_745988] using wordTrace_append hprefix tailTrace_745988
  have hstable : (prefixWord ++ tailWord_745988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_745988).length < 2 ^ (prefixWord ++ tailWord_745988).sum := by decide
  have hdescent : baseEnd_745988 < baseStart_745988 := by decide
  rcases family_descends (prefixWord ++ tailWord_745988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746036 : List Nat := [2, 5, 1, 3, 1, 1, 2, 2, 4]
def baseStart_746036 : Nat := 118140960795 + 746036 * 2 ^ 59
def prefixEnd_746036 : Nat := 4983230072969 + 3 ^ 40 * 746036 * 2
def baseEnd_746036 : Nat := 170255579358999273075133

theorem tailTrace_746036 : CollatzResearch.WordTrace tailWord_746036 prefixEnd_746036 170255579358999273075133 := by
  unfold tailWord_746036
  simp only [CollatzResearch.WordTrace]
  refine ⟨13605084162623229825028981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18140112216830973100038641 13605084162623229825028981)
  ·
    refine ⟨1275476640245927796096467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13605084162623229825028981 1275476640245927796096467)
    ·
      refine ⟨1913214960368891694144701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1275476640245927796096467 1913214960368891694144701)
      ·
        refine ⟨717455610138334385304263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1913214960368891694144701 717455610138334385304263)
        ·
          refine ⟨1076183415207501577956395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 717455610138334385304263 1076183415207501577956395)
          ·
            refine ⟨1614275122811252366934593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076183415207501577956395 1614275122811252366934593)
            ·
              refine ⟨1210706342108439275200945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1614275122811252366934593 1210706342108439275200945)
              ·
                refine ⟨908029756581329456400709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1210706342108439275200945 908029756581329456400709)
                ·
                  refine ⟨170255579358999273075133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 908029756581329456400709 170255579358999273075133)
                  ·
                    rfl

theorem cell21_746036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_746036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746036 prefixEnd_746036 := by exact prefixLift 746036
  have htrace : WordTrace (prefixWord ++ tailWord_746036) baseStart_746036 baseEnd_746036 := by
    simpa [prefixWord, tailWord_746036, baseEnd_746036] using wordTrace_append hprefix tailTrace_746036
  have hstable : (prefixWord ++ tailWord_746036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746036).length < 2 ^ (prefixWord ++ tailWord_746036).sum := by decide
  have hdescent : baseEnd_746036 < baseStart_746036 := by decide
  rcases family_descends (prefixWord ++ tailWord_746036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746047 : List Nat := [1, 1, 2, 2, 3, 2, 3, 4, 3]
def baseStart_746047 : Nat := 118140960795 + 746047 * 2 ^ 59
def prefixEnd_746047 : Nat := 4983230072969 + 3 ^ 40 * 746047 * 2
def baseEnd_746047 : Nat := 170258089708865698391777

theorem tailTrace_746047 : CollatzResearch.WordTrace tailWord_746047 prefixEnd_746047 170258089708865698391777 := by
  unfold tailWord_746047
  simp only [CollatzResearch.WordTrace]
  refine ⟨27210569528206608528708395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18140379685471072352472263 27210569528206608528708395)
  ·
    refine ⟨40815854292309912793062593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27210569528206608528708395 40815854292309912793062593)
    ·
      refine ⟨30611890719232434594796945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40815854292309912793062593 30611890719232434594796945)
      ·
        refine ⟨22958918039424325946097709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30611890719232434594796945 22958918039424325946097709)
        ·
          refine ⟨8609594264784122229786641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22958918039424325946097709 8609594264784122229786641)
          ·
            refine ⟨6457195698588091672339981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8609594264784122229786641 6457195698588091672339981)
            ·
              refine ⟨2421448386970534377127493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6457195698588091672339981 2421448386970534377127493)
              ·
                refine ⟨454021572556975195711405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2421448386970534377127493 454021572556975195711405)
                ·
                  refine ⟨170258089708865698391777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 454021572556975195711405 170258089708865698391777)
                  ·
                    rfl

theorem cell21_746047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 3].length) (baseStart_746047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746047 prefixEnd_746047 := by exact prefixLift 746047
  have htrace : WordTrace (prefixWord ++ tailWord_746047) baseStart_746047 baseEnd_746047 := by
    simpa [prefixWord, tailWord_746047, baseEnd_746047] using wordTrace_append hprefix tailTrace_746047
  have hstable : (prefixWord ++ tailWord_746047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746047).length < 2 ^ (prefixWord ++ tailWord_746047).sum := by decide
  have hdescent : baseEnd_746047 < baseStart_746047 := by decide
  rcases family_descends (prefixWord ++ tailWord_746047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746089 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 9]
def baseStart_746089 : Nat := 118140960795 + 746089 * 2 ^ 59
def prefixEnd_746089 : Nat := 4983230072969 + 3 ^ 40 * 746089 * 2
def baseEnd_746089 : Nat := 170267674681082958691691

theorem tailTrace_746089 : CollatzResearch.WordTrace tailWord_746089 prefixEnd_746089 170267674681082958691691 := by
  unfold tailWord_746089
  simp only [CollatzResearch.WordTrace]
  refine ⟨27212101394054449701737321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18141400929369633134491547 27212101394054449701737321)
  ·
    refine ⟨20409076045540837276302991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27212101394054449701737321 20409076045540837276302991)
    ·
      refine ⟨30613614068311255914454487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20409076045540837276302991 30613614068311255914454487)
      ·
        refine ⟨45920421102466883871681731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30613614068311255914454487 45920421102466883871681731)
        ·
          refine ⟨68880631653700325807522597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45920421102466883871681731 68880631653700325807522597)
          ·
            refine ⟨12915118435068811088910487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68880631653700325807522597 12915118435068811088910487)
            ·
              refine ⟨19372677652603216633365731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12915118435068811088910487 19372677652603216633365731)
              ·
                refine ⟨29059016478904824950048597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19372677652603216633365731 29059016478904824950048597)
                ·
                  refine ⟨170267674681082958691691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29059016478904824950048597 170267674681082958691691)
                  ·
                    rfl

theorem cell21_746089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_746089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746089 prefixEnd_746089 := by exact prefixLift 746089
  have htrace : WordTrace (prefixWord ++ tailWord_746089) baseStart_746089 baseEnd_746089 := by
    simpa [prefixWord, tailWord_746089, baseEnd_746089] using wordTrace_append hprefix tailTrace_746089
  have hstable : (prefixWord ++ tailWord_746089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746089).length < 2 ^ (prefixWord ++ tailWord_746089).sum := by decide
  have hdescent : baseEnd_746089 < baseStart_746089 := by decide
  rcases family_descends (prefixWord ++ tailWord_746089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746140 : List Nat := [2, 2, 3, 2, 2, 1, 3, 3, 3]
def baseStart_746140 : Nat := 118140960795 + 746140 * 2 ^ 59
def prefixEnd_746140 : Nat := 4983230072969 + 3 ^ 40 * 746140 * 2
def baseEnd_746140 : Nat := 170279313575918203341587

theorem tailTrace_746140 : CollatzResearch.WordTrace tailWord_746140 prefixEnd_746140 170279313575918203341587 := by
  unfold tailWord_746140
  simp only [CollatzResearch.WordTrace]
  refine ⟨13606980758434842705921937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18142641011246456941229249 13606980758434842705921937)
  ·
    refine ⟨10205235568826132029441453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13606980758434842705921937 10205235568826132029441453)
    ·
      refine ⟨3826963338309799511040545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10205235568826132029441453 3826963338309799511040545)
      ·
        refine ⟨2870222503732349633280409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3826963338309799511040545 2870222503732349633280409)
        ·
          refine ⟨2152666877799262224960307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2870222503732349633280409 2152666877799262224960307)
          ·
            refine ⟨3229000316698893337440461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152666877799262224960307 3229000316698893337440461)
            ·
              refine ⟨1210875118762085001540173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3229000316698893337440461 1210875118762085001540173)
              ·
                refine ⟨454078169535781875577565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1210875118762085001540173 454078169535781875577565)
                ·
                  refine ⟨170279313575918203341587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 454078169535781875577565 170279313575918203341587)
                  ·
                    rfl

theorem cell21_746140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 3].length) (baseStart_746140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746140 prefixEnd_746140 := by exact prefixLift 746140
  have htrace : WordTrace (prefixWord ++ tailWord_746140) baseStart_746140 baseEnd_746140 := by
    simpa [prefixWord, tailWord_746140, baseEnd_746140] using wordTrace_append hprefix tailTrace_746140
  have hstable : (prefixWord ++ tailWord_746140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746140).length < 2 ^ (prefixWord ++ tailWord_746140).sum := by decide
  have hdescent : baseEnd_746140 < baseStart_746140 := by decide
  rcases family_descends (prefixWord ++ tailWord_746140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746157 : List Nat := [1, 5, 2, 1, 1, 3, 3, 2, 3]
def baseStart_746157 : Nat := 118140960795 + 746157 * 2 ^ 59
def prefixEnd_746157 : Nat := 4983230072969 + 3 ^ 40 * 746157 * 2
def baseEnd_746157 : Nat := 170283193207529951558219

theorem tailTrace_746157 : CollatzResearch.WordTrace tailWord_746157 prefixEnd_746157 170283193207529951558219 := by
  unfold tailWord_746157
  simp only [CollatzResearch.WordTrace]
  refine ⟨27214581557808097315212725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18143054371872064876808483 27214581557808097315212725)
  ·
    refine ⟨2551367021044509123301193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27214581557808097315212725 2551367021044509123301193)
    ·
      refine ⟨1913525265783381842475895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2551367021044509123301193 1913525265783381842475895)
      ·
        refine ⟨2870287898675072763713843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1913525265783381842475895 2870287898675072763713843)
        ·
          refine ⟨4305431848012609145570765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2870287898675072763713843 4305431848012609145570765)
          ·
            refine ⟨1614536943004728429589037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4305431848012609145570765 1614536943004728429589037)
            ·
              refine ⟨605451353626773161095889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1614536943004728429589037 605451353626773161095889)
              ·
                refine ⟨454088515220079870821917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605451353626773161095889 454088515220079870821917)
                ·
                  refine ⟨170283193207529951558219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 454088515220079870821917 170283193207529951558219)
                  ·
                    rfl

theorem cell21_746157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_746157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746157 prefixEnd_746157 := by exact prefixLift 746157
  have htrace : WordTrace (prefixWord ++ tailWord_746157) baseStart_746157 baseEnd_746157 := by
    simpa [prefixWord, tailWord_746157, baseEnd_746157] using wordTrace_append hprefix tailTrace_746157
  have hstable : (prefixWord ++ tailWord_746157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746157).length < 2 ^ (prefixWord ++ tailWord_746157).sum := by decide
  have hdescent : baseEnd_746157 < baseStart_746157 := by decide
  rcases family_descends (prefixWord ++ tailWord_746157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746213 : List Nat := [1, 3, 1, 4, 1, 2, 1, 4, 4]
def baseStart_746213 : Nat := 118140960795 + 746213 * 2 ^ 59
def prefixEnd_746213 : Nat := 4983230072969 + 3 ^ 40 * 746213 * 2
def baseEnd_746213 : Nat := 170295973170486298624771

theorem tailTrace_746213 : CollatzResearch.WordTrace tailWord_746213 prefixEnd_746213 170295973170486298624771 := by
  unfold tailWord_746213
  simp only [CollatzResearch.WordTrace]
  refine ⟨27216624045605218879251293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18144416030403479252834195 27216624045605218879251293)
  ·
    refine ⟨10206234017101957079719235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27216624045605218879251293 10206234017101957079719235)
    ·
      refine ⟨15309351025652935619578853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10206234017101957079719235 15309351025652935619578853)
      ·
        refine ⟨2870503317309925428671035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15309351025652935619578853 2870503317309925428671035)
        ·
          refine ⟨4305754975964888143006553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2870503317309925428671035 4305754975964888143006553)
          ·
            refine ⟨3229316231973666107254915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4305754975964888143006553 3229316231973666107254915)
            ·
              refine ⟨4843974347960499160882373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3229316231973666107254915 4843974347960499160882373)
              ·
                refine ⟨908245190242593592665445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4843974347960499160882373 908245190242593592665445)
                ·
                  refine ⟨170295973170486298624771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 908245190242593592665445 170295973170486298624771)
                  ·
                    rfl

theorem cell21_746213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_746213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746213 prefixEnd_746213 := by exact prefixLift 746213
  have htrace : WordTrace (prefixWord ++ tailWord_746213) baseStart_746213 baseEnd_746213 := by
    simpa [prefixWord, tailWord_746213, baseEnd_746213] using wordTrace_append hprefix tailTrace_746213
  have hstable : (prefixWord ++ tailWord_746213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746213).length < 2 ^ (prefixWord ++ tailWord_746213).sum := by decide
  have hdescent : baseEnd_746213 < baseStart_746213 := by decide
  rcases family_descends (prefixWord ++ tailWord_746213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746216 : List Nat := [2, 1, 4, 1, 4, 1, 1, 4, 3]
def baseStart_746216 : Nat := 118140960795 + 746216 * 2 ^ 59
def prefixEnd_746216 : Nat := 4983230072969 + 3 ^ 40 * 746216 * 2
def baseEnd_746216 : Nat := 170296657811358960074765

theorem tailTrace_746216 : CollatzResearch.WordTrace tailWord_746216 prefixEnd_746216 170296657811358960074765 := by
  unfold tailWord_746216
  simp only [CollatzResearch.WordTrace]
  refine ⟨13608366732297175195805251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18144488976396233594407001 13608366732297175195805251)
  ·
    refine ⟨20412550098445762793707877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13608366732297175195805251 20412550098445762793707877)
    ·
      refine ⟨3827353143458580523820227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20412550098445762793707877 3827353143458580523820227)
      ·
        refine ⟨5741029715187870785730341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3827353143458580523820227 5741029715187870785730341)
        ·
          refine ⟨1076443071597725772324439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5741029715187870785730341 1076443071597725772324439)
          ·
            refine ⟨1614664607396588658486659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076443071597725772324439 1614664607396588658486659)
            ·
              refine ⟨2421996911094882987729989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1614664607396588658486659 2421996911094882987729989)
              ·
                refine ⟨454124420830290560199373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2421996911094882987729989 454124420830290560199373)
                ·
                  refine ⟨170296657811358960074765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 454124420830290560199373 170296657811358960074765)
                  ·
                    rfl

theorem cell21_746216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 3].length) (baseStart_746216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746216 prefixEnd_746216 := by exact prefixLift 746216
  have htrace : WordTrace (prefixWord ++ tailWord_746216) baseStart_746216 baseEnd_746216 := by
    simpa [prefixWord, tailWord_746216, baseEnd_746216] using wordTrace_append hprefix tailTrace_746216
  have hstable : (prefixWord ++ tailWord_746216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746216).length < 2 ^ (prefixWord ++ tailWord_746216).sum := by decide
  have hdescent : baseEnd_746216 < baseStart_746216 := by decide
  rcases family_descends (prefixWord ++ tailWord_746216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746244 : List Nat := [2, 3, 2, 2, 1, 1, 5, 5]
def baseStart_746244 : Nat := 118140960795 + 746244 * 2 ^ 59
def prefixEnd_746244 : Nat := 4983230072969 + 3 ^ 40 * 746244 * 2
def baseEnd_746244 : Nat := 56767682597612377869347

theorem tailTrace_746244 : CollatzResearch.WordTrace tailWord_746244 prefixEnd_746244 56767682597612377869347 := by
  unfold tailWord_746244
  simp only [CollatzResearch.WordTrace]
  refine ⟨13608877354246455586814893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18145169805661940782419857 13608877354246455586814893)
  ·
    refine ⟨5103329007842420845055585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13608877354246455586814893 5103329007842420845055585)
    ·
      refine ⟨3827496755881815633791689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5103329007842420845055585 3827496755881815633791689)
      ·
        refine ⟨2870622566911361725343767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3827496755881815633791689 2870622566911361725343767)
        ·
          refine ⟨4305933850367042588015651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2870622566911361725343767 4305933850367042588015651)
          ·
            refine ⟨6458900775550563882023477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4305933850367042588015651 6458900775550563882023477)
            ·
              refine ⟨605521947707865363939701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6458900775550563882023477 605521947707865363939701)
              ·
                refine ⟨56767682597612377869347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 605521947707865363939701 56767682597612377869347)
                ·
                  rfl

theorem cell21_746244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 5].length) (baseStart_746244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746244 prefixEnd_746244 := by exact prefixLift 746244
  have htrace : WordTrace (prefixWord ++ tailWord_746244) baseStart_746244 baseEnd_746244 := by
    simpa [prefixWord, tailWord_746244, baseEnd_746244] using wordTrace_append hprefix tailTrace_746244
  have hstable : (prefixWord ++ tailWord_746244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746244).length < 2 ^ (prefixWord ++ tailWord_746244).sum := by decide
  have hdescent : baseEnd_746244 < baseStart_746244 := by decide
  rcases family_descends (prefixWord ++ tailWord_746244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746303 : List Nat := [1, 1, 2, 2, 5, 2, 1, 7]
def baseStart_746303 : Nat := 118140960795 + 746303 * 2 ^ 59
def prefixEnd_746303 : Nat := 4983230072969 + 3 ^ 40 * 746303 * 2
def baseEnd_746303 : Nat := 56772170798888714041529

theorem tailTrace_746303 : CollatzResearch.WordTrace tailWord_746303 prefixEnd_746303 56772170798888714041529 := by
  unfold tailWord_746303
  simp only [CollatzResearch.WordTrace]
  refine ⟨27219906615279164250027563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18146604410186109500018375 27219906615279164250027563)
  ·
    refine ⟨40829859922918746375041345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27219906615279164250027563 40829859922918746375041345)
    ·
      refine ⟨30622394942189059781281009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40829859922918746375041345 30622394942189059781281009)
      ·
        refine ⟨22966796206641794835960757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30622394942189059781281009 22966796206641794835960757)
        ·
          refine ⟨2153137144372668265871321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22966796206641794835960757 2153137144372668265871321)
          ·
            refine ⟨1614852858279501199403491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2153137144372668265871321 1614852858279501199403491)
            ·
              refine ⟨2422279287419251799105237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1614852858279501199403491 2422279287419251799105237)
              ·
                refine ⟨56772170798888714041529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2422279287419251799105237 56772170798888714041529)
                ·
                  rfl

theorem cell21_746303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 7].length) (baseStart_746303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746303 prefixEnd_746303 := by exact prefixLift 746303
  have htrace : WordTrace (prefixWord ++ tailWord_746303) baseStart_746303 baseEnd_746303 := by
    simpa [prefixWord, tailWord_746303, baseEnd_746303] using wordTrace_append hprefix tailTrace_746303
  have hstable : (prefixWord ++ tailWord_746303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746303).length < 2 ^ (prefixWord ++ tailWord_746303).sum := by decide
  have hdescent : baseEnd_746303 < baseStart_746303 := by decide
  rcases family_descends (prefixWord ++ tailWord_746303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746393 : List Nat := [1, 2, 1, 2, 1, 3, 1, 5, 5]
def baseStart_746393 : Nat := 118140960795 + 746393 * 2 ^ 59
def prefixEnd_746393 : Nat := 4983230072969 + 3 ^ 40 * 746393 * 2
def baseEnd_746393 : Nat := 170337051622845985624403

theorem tailTrace_746393 : CollatzResearch.WordTrace tailWord_746393 prefixEnd_746393 170337051622845985624403 := by
  unfold tailWord_746393
  simp only [CollatzResearch.WordTrace]
  refine ⟨27223189184953109620803833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18148792789968739747202555 27223189184953109620803833)
  ·
    refine ⟨20417391888714832215602875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27223189184953109620803833 20417391888714832215602875)
    ·
      refine ⟨30626087833072248323404313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20417391888714832215602875 30626087833072248323404313)
      ·
        refine ⟨22969565874804186242553235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30626087833072248323404313 22969565874804186242553235)
        ·
          refine ⟨34454348812206279363829853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22969565874804186242553235 34454348812206279363829853)
          ·
            refine ⟨12920380804577354761436195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34454348812206279363829853 12920380804577354761436195)
            ·
              refine ⟨19380571206866032142154293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12920380804577354761436195 19380571206866032142154293)
              ·
                refine ⟨1816928550643690513326965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19380571206866032142154293 1816928550643690513326965)
                ·
                  refine ⟨170337051622845985624403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1816928550643690513326965 170337051622845985624403)
                  ·
                    rfl

theorem cell21_746393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_746393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746393 prefixEnd_746393 := by exact prefixLift 746393
  have htrace : WordTrace (prefixWord ++ tailWord_746393) baseStart_746393 baseEnd_746393 := by
    simpa [prefixWord, tailWord_746393, baseEnd_746393] using wordTrace_append hprefix tailTrace_746393
  have hstable : (prefixWord ++ tailWord_746393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746393).length < 2 ^ (prefixWord ++ tailWord_746393).sum := by decide
  have hdescent : baseEnd_746393 < baseStart_746393 := by decide
  rcases family_descends (prefixWord ++ tailWord_746393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746458 : List Nat := [3, 1, 1, 2, 4, 2, 3, 1, 4]
def baseStart_746458 : Nat := 118140960795 + 746458 * 2 ^ 59
def prefixEnd_746458 : Nat := 4983230072969 + 3 ^ 40 * 746458 * 2
def baseEnd_746458 : Nat := 170351885508420317040937

theorem tailTrace_746458 : CollatzResearch.WordTrace tailWord_746458 prefixEnd_746458 170351885508420317040937 := by
  unfold tailWord_746458
  simp only [CollatzResearch.WordTrace]
  refine ⟨6806389982429406430480007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18150373286478417147946685 6806389982429406430480007)
  ·
    refine ⟨10209584973644109645720011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6806389982429406430480007 10209584973644109645720011)
    ·
      refine ⟨15314377460466164468580017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10209584973644109645720011 15314377460466164468580017)
      ·
        refine ⟨11485783095349623351435013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15314377460466164468580017 11485783095349623351435013)
        ·
          refine ⟨2153584330378054378394065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11485783095349623351435013 2153584330378054378394065)
          ·
            refine ⟨1615188247783540783795549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2153584330378054378394065 1615188247783540783795549)
            ·
              refine ⟨605695592918827793923331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1615188247783540783795549 605695592918827793923331)
              ·
                refine ⟨908543389378241690884997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605695592918827793923331 908543389378241690884997)
                ·
                  refine ⟨170351885508420317040937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 908543389378241690884997 170351885508420317040937)
                  ·
                    rfl

theorem cell21_746458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_746458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746458 prefixEnd_746458 := by exact prefixLift 746458
  have htrace : WordTrace (prefixWord ++ tailWord_746458) baseStart_746458 baseEnd_746458 := by
    simpa [prefixWord, tailWord_746458, baseEnd_746458] using wordTrace_append hprefix tailTrace_746458
  have hstable : (prefixWord ++ tailWord_746458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746458).length < 2 ^ (prefixWord ++ tailWord_746458).sum := by decide
  have hdescent : baseEnd_746458 < baseStart_746458 := by decide
  rcases family_descends (prefixWord ++ tailWord_746458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746517 : List Nat := [1, 3, 2, 1, 4, 2, 1, 3, 4]
def baseStart_746517 : Nat := 118140960795 + 746517 * 2 ^ 59
def prefixEnd_746517 : Nat := 4983230072969 + 3 ^ 40 * 746517 * 2
def baseEnd_746517 : Nat := 170365350112249325557483

theorem tailTrace_746517 : CollatzResearch.WordTrace tailWord_746517 prefixEnd_746517 170365350112249325557483 := by
  unfold tailWord_746517
  simp only [CollatzResearch.WordTrace]
  refine ⟨27227711836503878798317805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18151807891002585865545203 27227711836503878798317805)
  ·
    refine ⟨10210391938688954549369177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27227711836503878798317805 10210391938688954549369177)
    ·
      refine ⟨7657793954016715912026883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10210391938688954549369177 7657793954016715912026883)
      ·
        refine ⟨11486690931025073868040325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7657793954016715912026883 11486690931025073868040325)
        ·
          refine ⟨2153754549567201350257561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11486690931025073868040325 2153754549567201350257561)
          ·
            refine ⟨1615315912175401012693171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2153754549567201350257561 1615315912175401012693171)
            ·
              refine ⟨2422973868263101519039757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1615315912175401012693171 2422973868263101519039757)
              ·
                refine ⟨908615200598663069639909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2422973868263101519039757 908615200598663069639909)
                ·
                  refine ⟨170365350112249325557483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 908615200598663069639909 170365350112249325557483)
                  ·
                    rfl

theorem cell21_746517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_746517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746517 prefixEnd_746517 := by exact prefixLift 746517
  have htrace : WordTrace (prefixWord ++ tailWord_746517) baseStart_746517 baseEnd_746517 := by
    simpa [prefixWord, tailWord_746517, baseEnd_746517] using wordTrace_append hprefix tailTrace_746517
  have hstable : (prefixWord ++ tailWord_746517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746517).length < 2 ^ (prefixWord ++ tailWord_746517).sum := by decide
  have hdescent : baseEnd_746517 < baseStart_746517 := by decide
  rcases family_descends (prefixWord ++ tailWord_746517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746582 : List Nat := [5, 2, 2, 1, 2, 1, 3, 5]
def baseStart_746582 : Nat := 118140960795 + 746582 * 2 ^ 59
def prefixEnd_746582 : Nat := 4983230072969 + 3 ^ 40 * 746582 * 2
def baseEnd_746582 : Nat := 56793394665941218991339

theorem tailTrace_746582 : CollatzResearch.WordTrace tailWord_746582 prefixEnd_746582 56793394665941218991339 := by
  unfold tailWord_746582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1701880161329274681214625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18153388387512263266289333 1701880161329274681214625)
  ·
    refine ⟨1276410120996956010910969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1701880161329274681214625 1276410120996956010910969)
    ·
      refine ⟨957307590747717008183227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1276410120996956010910969 957307590747717008183227)
      ·
        refine ⟨1435961386121575512274841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 957307590747717008183227 1435961386121575512274841)
        ·
          refine ⟨1076971039591181634206131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1435961386121575512274841 1076971039591181634206131)
          ·
            refine ⟨1615456559386772451309197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076971039591181634206131 1615456559386772451309197)
            ·
              refine ⟨605796209770039669240949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1615456559386772451309197 605796209770039669240949)
              ·
                refine ⟨56793394665941218991339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 605796209770039669240949 56793394665941218991339)
                ·
                  rfl

theorem cell21_746582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_746582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746582 prefixEnd_746582 := by exact prefixLift 746582
  have htrace : WordTrace (prefixWord ++ tailWord_746582) baseStart_746582 baseEnd_746582 := by
    simpa [prefixWord, tailWord_746582, baseEnd_746582] using wordTrace_append hprefix tailTrace_746582
  have hstable : (prefixWord ++ tailWord_746582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746582).length < 2 ^ (prefixWord ++ tailWord_746582).sum := by decide
  have hdescent : baseEnd_746582 < baseStart_746582 := by decide
  rcases family_descends (prefixWord ++ tailWord_746582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746638 : List Nat := [4, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_746638 : Nat := 118140960795 + 746638 * 2 ^ 59
def prefixEnd_746638 : Nat := 4983230072969 + 3 ^ 40 * 746638 * 2
def baseEnd_746638 : Nat := 170392963960780004040569

theorem tailTrace_746638 : CollatzResearch.WordTrace tailWord_746638 prefixEnd_746638 170392963960780004040569 := by
  unfold tailWord_746638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3404015633633189557934071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18154750046043677642315045 3404015633633189557934071)
  ·
    refine ⟨5106023450449784336901107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3404015633633189557934071 5106023450449784336901107)
    ·
      refine ⟨7659035175674676505351661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5106023450449784336901107 7659035175674676505351661)
      ·
        refine ⟨2872138190878003689506873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7659035175674676505351661 2872138190878003689506873)
        ·
          refine ⟨2154103643158502767130155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2872138190878003689506873 2154103643158502767130155)
          ·
            refine ⟨3231155464737754150695233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2154103643158502767130155 3231155464737754150695233)
            ·
              refine ⟨2423366598553315613021425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3231155464737754150695233 2423366598553315613021425)
              ·
                refine ⟨1817524948914986709766069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2423366598553315613021425 1817524948914986709766069)
                ·
                  refine ⟨170392963960780004040569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1817524948914986709766069 170392963960780004040569)
                  ·
                    rfl

theorem cell21_746638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_746638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746638 prefixEnd_746638 := by exact prefixLift 746638
  have htrace : WordTrace (prefixWord ++ tailWord_746638) baseStart_746638 baseEnd_746638 := by
    simpa [prefixWord, tailWord_746638, baseEnd_746638] using wordTrace_append hprefix tailTrace_746638
  have hstable : (prefixWord ++ tailWord_746638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746638).length < 2 ^ (prefixWord ++ tailWord_746638).sum := by decide
  have hdescent : baseEnd_746638 < baseStart_746638 := by decide
  rcases family_descends (prefixWord ++ tailWord_746638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746652 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 6]
def baseStart_746652 : Nat := 118140960795 + 746652 * 2 ^ 59
def prefixEnd_746652 : Nat := 4983230072969 + 3 ^ 40 * 746652 * 2
def baseEnd_746652 : Nat := 170396158951519090807207

theorem tailTrace_746652 : CollatzResearch.WordTrace tailWord_746652 prefixEnd_746652 170396158951519090807207 := by
  unfold tailWord_746652
  simp only [CollatzResearch.WordTrace]
  refine ⟨13616317845507398427241105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18155090460676531236321473 13616317845507398427241105)
  ·
    refine ⟨10212238384130548820430829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13616317845507398427241105 10212238384130548820430829)
    ·
      refine ⟨3829589394048955807661561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10212238384130548820430829 3829589394048955807661561)
      ·
        refine ⟨2872192045536716855746171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3829589394048955807661561 2872192045536716855746171)
        ·
          refine ⟨4308288068305075283619257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2872192045536716855746171 4308288068305075283619257)
          ·
            refine ⟨3231216051228806462714443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4308288068305075283619257 3231216051228806462714443)
            ·
              refine ⟨4846824076843209694071665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3231216051228806462714443 4846824076843209694071665)
              ·
                refine ⟨3635118057632407270553749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4846824076843209694071665 3635118057632407270553749)
                ·
                  refine ⟨170396158951519090807207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3635118057632407270553749 170396158951519090807207)
                  ·
                    rfl

theorem cell21_746652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_746652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746652 prefixEnd_746652 := by exact prefixLift 746652
  have htrace : WordTrace (prefixWord ++ tailWord_746652) baseStart_746652 baseEnd_746652 := by
    simpa [prefixWord, tailWord_746652, baseEnd_746652] using wordTrace_append hprefix tailTrace_746652
  have hstable : (prefixWord ++ tailWord_746652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746652).length < 2 ^ (prefixWord ++ tailWord_746652).sum := by decide
  have hdescent : baseEnd_746652 < baseStart_746652 := by decide
  rcases family_descends (prefixWord ++ tailWord_746652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746686 : List Nat := [4, 2, 1, 1, 3, 1, 4, 1, 4]
def baseStart_746686 : Nat := 118140960795 + 746686 * 2 ^ 59
def prefixEnd_746686 : Nat := 4983230072969 + 3 ^ 40 * 746686 * 2
def baseEnd_746686 : Nat := 170403918214742587240471

theorem tailTrace_746686 : CollatzResearch.WordTrace tailWord_746686 prefixEnd_746686 170403918214742587240471 := by
  unfold tailWord_746686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3404234471611452582652489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18155917181927747107479941 3404234471611452582652489)
  ·
    refine ⟨2553175853708589436989367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3404234471611452582652489 2553175853708589436989367)
    ·
      refine ⟨3829763780562884155484051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2553175853708589436989367 3829763780562884155484051)
      ·
        refine ⟨5744645670844326233226077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3829763780562884155484051 5744645670844326233226077)
        ·
          refine ⟨2154242126566622337459779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5744645670844326233226077 2154242126566622337459779)
          ·
            refine ⟨3231363189849933506189669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2154242126566622337459779 3231363189849933506189669)
            ·
              refine ⟨605880598096862532410563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3231363189849933506189669 605880598096862532410563)
              ·
                refine ⟨908820897145293798615845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 605880598096862532410563 908820897145293798615845)
                ·
                  refine ⟨170403918214742587240471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 908820897145293798615845 170403918214742587240471)
                  ·
                    rfl

theorem cell21_746686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_746686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746686 prefixEnd_746686 := by exact prefixLift 746686
  have htrace : WordTrace (prefixWord ++ tailWord_746686) baseStart_746686 baseEnd_746686 := by
    simpa [prefixWord, tailWord_746686, baseEnd_746686] using wordTrace_append hprefix tailTrace_746686
  have hstable : (prefixWord ++ tailWord_746686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746686).length < 2 ^ (prefixWord ++ tailWord_746686).sum := by decide
  have hdescent : baseEnd_746686 < baseStart_746686 := by decide
  rcases family_descends (prefixWord ++ tailWord_746686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746711 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 8]
def baseStart_746711 : Nat := 118140960795 + 746711 * 2 ^ 59
def prefixEnd_746711 : Nat := 4983230072969 + 3 ^ 40 * 746711 * 2
def baseEnd_746711 : Nat := 170409623555348099323753

theorem tailTrace_746711 : CollatzResearch.WordTrace tailWord_746711 prefixEnd_746711 170409623555348099323753 := by
  unfold tailWord_746711
  simp only [CollatzResearch.WordTrace]
  refine ⟨27234787597801049930879987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18156525065200699953919991 27234787597801049930879987)
  ·
    refine ⟨40852181396701574896319981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27234787597801049930879987 40852181396701574896319981)
    ·
      refine ⟨15319568023763090586119993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40852181396701574896319981 15319568023763090586119993)
      ·
        refine ⟨11489676017822317939589995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15319568023763090586119993 11489676017822317939589995)
        ·
          refine ⟨17234514026733476909384993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11489676017822317939589995 17234514026733476909384993)
          ·
            refine ⟨12925885520050107682038745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17234514026733476909384993 12925885520050107682038745)
            ·
              refine ⟨9694414140037580761529059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12925885520050107682038745 9694414140037580761529059)
              ·
                refine ⟨14541621210056371142293589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9694414140037580761529059 14541621210056371142293589)
                ·
                  refine ⟨170409623555348099323753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14541621210056371142293589 170409623555348099323753)
                  ·
                    rfl

theorem cell21_746711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 8].length) (baseStart_746711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746711 prefixEnd_746711 := by exact prefixLift 746711
  have htrace : WordTrace (prefixWord ++ tailWord_746711) baseStart_746711 baseEnd_746711 := by
    simpa [prefixWord, tailWord_746711, baseEnd_746711] using wordTrace_append hprefix tailTrace_746711
  have hstable : (prefixWord ++ tailWord_746711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746711).length < 2 ^ (prefixWord ++ tailWord_746711).sum := by decide
  have hdescent : baseEnd_746711 < baseStart_746711 := by decide
  rcases family_descends (prefixWord ++ tailWord_746711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746714 : List Nat := [3, 1, 1, 2, 2, 1, 1, 7, 3]
def baseStart_746714 : Nat := 118140960795 + 746714 * 2 ^ 59
def prefixEnd_746714 : Nat := 4983230072969 + 3 ^ 40 * 746714 * 2
def baseEnd_746714 : Nat := 170410308196220760773747

theorem tailTrace_746714 : CollatzResearch.WordTrace tailWord_746714 prefixEnd_746714 170410308196220760773747 := by
  unfold tailWord_746714
  simp only [CollatzResearch.WordTrace]
  refine ⟨6808724254197545360809799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18156598011193454295492797 6808724254197545360809799)
  ·
    refine ⟨10213086381296318041214699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6808724254197545360809799 10213086381296318041214699)
    ·
      refine ⟨15319629571944477061822049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10213086381296318041214699 15319629571944477061822049)
      ·
        refine ⟨11489722178958357796366537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15319629571944477061822049 11489722178958357796366537)
        ·
          refine ⟨8617291634218768347274903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11489722178958357796366537 8617291634218768347274903)
          ·
            refine ⟨12925937451328152520912355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8617291634218768347274903 12925937451328152520912355)
            ·
              refine ⟨19388906176992228781368533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12925937451328152520912355 19388906176992228781368533)
              ·
                refine ⟨454427488523255362063325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19388906176992228781368533 454427488523255362063325)
                ·
                  refine ⟨170410308196220760773747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 454427488523255362063325 170410308196220760773747)
                  ·
                    rfl

theorem cell21_746714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 3].length) (baseStart_746714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746714 prefixEnd_746714 := by exact prefixLift 746714
  have htrace : WordTrace (prefixWord ++ tailWord_746714) baseStart_746714 baseEnd_746714 := by
    simpa [prefixWord, tailWord_746714, baseEnd_746714] using wordTrace_append hprefix tailTrace_746714
  have hstable : (prefixWord ++ tailWord_746714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746714).length < 2 ^ (prefixWord ++ tailWord_746714).sum := by decide
  have hdescent : baseEnd_746714 < baseStart_746714 := by decide
  rcases family_descends (prefixWord ++ tailWord_746714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746731 : List Nat := [1, 1, 1, 1, 2, 6, 4, 2, 3]
def baseStart_746731 : Nat := 118140960795 + 746731 * 2 ^ 59
def prefixEnd_746731 : Nat := 4983230072969 + 3 ^ 40 * 746731 * 2
def baseEnd_746731 : Nat := 170414187827832508990379

theorem tailTrace_746731 : CollatzResearch.WordTrace tailWord_746731 prefixEnd_746731 170414187827832508990379 := by
  unfold tailWord_746731
  simp only [CollatzResearch.WordTrace]
  refine ⟨27235517057728593346608047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18157011371819062231072031 27235517057728593346608047)
  ·
    refine ⟨40853275586592890019912071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27235517057728593346608047 40853275586592890019912071)
    ·
      refine ⟨61279913379889335029868107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40853275586592890019912071 61279913379889335029868107)
      ·
        refine ⟨91919870069834002544802161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61279913379889335029868107 91919870069834002544802161)
        ·
          refine ⟨68939902552375501908601621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91919870069834002544802161 68939902552375501908601621)
          ·
            refine ⟨3231557932142601651965701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68939902552375501908601621 3231557932142601651965701)
            ·
              refine ⟨605917112276737809743569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3231557932142601651965701 605917112276737809743569)
              ·
                refine ⟨454437834207553357307677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605917112276737809743569 454437834207553357307677)
                ·
                  refine ⟨170414187827832508990379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 454437834207553357307677 170414187827832508990379)
                  ·
                    rfl

theorem cell21_746731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 3].length) (baseStart_746731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746731 prefixEnd_746731 := by exact prefixLift 746731
  have htrace : WordTrace (prefixWord ++ tailWord_746731) baseStart_746731 baseEnd_746731 := by
    simpa [prefixWord, tailWord_746731, baseEnd_746731] using wordTrace_append hprefix tailTrace_746731
  have hstable : (prefixWord ++ tailWord_746731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746731).length < 2 ^ (prefixWord ++ tailWord_746731).sum := by decide
  have hdescent : baseEnd_746731 < baseStart_746731 := by decide
  rcases family_descends (prefixWord ++ tailWord_746731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746855 : List Nat := [1, 1, 5, 1, 5, 1, 2, 1, 4]
def baseStart_746855 : Nat := 118140960795 + 746855 * 2 ^ 59
def prefixEnd_746855 : Nat := 4983230072969 + 3 ^ 40 * 746855 * 2
def baseEnd_746855 : Nat := 170442486317235848923459

theorem tailTrace_746855 : CollatzResearch.WordTrace tailWord_746855 prefixEnd_746855 170442486317235848923459 := by
  unfold tailWord_746855
  simp only [CollatzResearch.WordTrace]
  refine ⟨27240039709279362524122019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18160026472852908349414679 27240039709279362524122019)
  ·
    refine ⟨40860059563919043786183029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27240039709279362524122019 40860059563919043786183029)
    ·
      refine ⟨3830630584117410354954659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40860059563919043786183029 3830630584117410354954659)
      ·
        refine ⟨5745945876176115532431989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3830630584117410354954659 5745945876176115532431989)
        ·
          refine ⟨538682425891510831165499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5745945876176115532431989 538682425891510831165499)
          ·
            refine ⟨808023638837266246748249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538682425891510831165499 808023638837266246748249)
            ·
              refine ⟨606017729127949685061187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 808023638837266246748249 606017729127949685061187)
              ·
                refine ⟨909026593691924527591781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 606017729127949685061187 909026593691924527591781)
                ·
                  refine ⟨170442486317235848923459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 909026593691924527591781 170442486317235848923459)
                  ·
                    rfl

theorem cell21_746855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 4].length) (baseStart_746855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746855 prefixEnd_746855 := by exact prefixLift 746855
  have htrace : WordTrace (prefixWord ++ tailWord_746855) baseStart_746855 baseEnd_746855 := by
    simpa [prefixWord, tailWord_746855, baseEnd_746855] using wordTrace_append hprefix tailTrace_746855
  have hstable : (prefixWord ++ tailWord_746855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746855).length < 2 ^ (prefixWord ++ tailWord_746855).sum := by decide
  have hdescent : baseEnd_746855 < baseStart_746855 := by decide
  rcases family_descends (prefixWord ++ tailWord_746855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746894 : List Nat := [4, 1, 1, 4, 11]
def baseStart_746894 : Nat := 118140960795 + 746894 * 2 ^ 59
def prefixEnd_746894 : Nat := 4983230072969 + 3 ^ 40 * 746894 * 2
def baseEnd_746894 : Nat := 2104338106772598120659

theorem tailTrace_746894 : CollatzResearch.WordTrace tailWord_746894 prefixEnd_746894 2104338106772598120659 := by
  unfold tailWord_746894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3405182769517259023098967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18160974770758714789861157 3405182769517259023098967)
  ·
    refine ⟨5107774154275888534648451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3405182769517259023098967 5107774154275888534648451)
    ·
      refine ⟨7661661231413832801972677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5107774154275888534648451 7661661231413832801972677)
      ·
        refine ⟨1436561480890093650369877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7661661231413832801972677 1436561480890093650369877)
        ·
          refine ⟨2104338106772598120659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1436561480890093650369877 2104338106772598120659)
          ·
            rfl

theorem cell21_746894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 11].length) (baseStart_746894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746894 prefixEnd_746894 := by exact prefixLift 746894
  have htrace : WordTrace (prefixWord ++ tailWord_746894) baseStart_746894 baseEnd_746894 := by
    simpa [prefixWord, tailWord_746894, baseEnd_746894] using wordTrace_append hprefix tailTrace_746894
  have hstable : (prefixWord ++ tailWord_746894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746894).length < 2 ^ (prefixWord ++ tailWord_746894).sum := by decide
  have hdescent : baseEnd_746894 < baseStart_746894 := by decide
  rcases family_descends (prefixWord ++ tailWord_746894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746900 : List Nat := [2, 4, 2, 1, 2, 1, 4, 2, 3]
def baseStart_746900 : Nat := 118140960795 + 746900 * 2 ^ 59
def prefixEnd_746900 : Nat := 4983230072969 + 3 ^ 40 * 746900 * 2
def baseEnd_746900 : Nat := 170452755930325770673367

theorem tailTrace_746900 : CollatzResearch.WordTrace tailWord_746900 prefixEnd_746900 170452755930325770673367 := by
  unfold tailWord_746900
  simp only [CollatzResearch.WordTrace]
  refine ⟨13620840497058167604755077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18161120662744223473006769 13620840497058167604755077)
  ·
    refine ⟨2553907593198406425891577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13620840497058167604755077 2553907593198406425891577)
    ·
      refine ⟨1915430694898804819418683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2553907593198406425891577 1915430694898804819418683)
      ·
        refine ⟨2873146042348207229128025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1915430694898804819418683 2873146042348207229128025)
        ·
          refine ⟨2154859531761155421846019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2873146042348207229128025 2154859531761155421846019)
          ·
            refine ⟨3232289297641733132769029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2154859531761155421846019 3232289297641733132769029)
            ·
              refine ⟨606054243307824962394193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3232289297641733132769029 606054243307824962394193)
              ·
                refine ⟨454540682480868721795645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 606054243307824962394193 454540682480868721795645)
                ·
                  refine ⟨170452755930325770673367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 454540682480868721795645 170452755930325770673367)
                  ·
                    rfl

theorem cell21_746900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_746900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746900 prefixEnd_746900 := by exact prefixLift 746900
  have htrace : WordTrace (prefixWord ++ tailWord_746900) baseStart_746900 baseEnd_746900 := by
    simpa [prefixWord, tailWord_746900, baseEnd_746900] using wordTrace_append hprefix tailTrace_746900
  have hstable : (prefixWord ++ tailWord_746900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746900).length < 2 ^ (prefixWord ++ tailWord_746900).sum := by decide
  have hdescent : baseEnd_746900 < baseStart_746900 := by decide
  rcases family_descends (prefixWord ++ tailWord_746900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746911 : List Nat := [1, 1, 2, 5, 1, 4, 1, 6]
def baseStart_746911 : Nat := 118140960795 + 746911 * 2 ^ 59
def prefixEnd_746911 : Nat := 4983230072969 + 3 ^ 40 * 746911 * 2
def baseEnd_746911 : Nat := 56818422093397398663337

theorem tailTrace_746911 : CollatzResearch.WordTrace tailWord_746911 prefixEnd_746911 56818422093397398663337 := by
  unfold tailWord_746911
  simp only [CollatzResearch.WordTrace]
  refine ⟨27242082197076484088160587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18161388131384322725440391 27242082197076484088160587)
  ·
    refine ⟨40863123295614726132240881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27242082197076484088160587 40863123295614726132240881)
    ·
      refine ⟨30647342471711044599180661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40863123295614726132240881 30647342471711044599180661)
      ·
        refine ⟨2873188356722910431173187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30647342471711044599180661 2873188356722910431173187)
        ·
          refine ⟨4309782535084365646759781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2873188356722910431173187 4309782535084365646759781)
          ·
            refine ⟨808084225328318558767459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4309782535084365646759781 808084225328318558767459)
            ·
              refine ⟨1212126337992477838151189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 808084225328318558767459 1212126337992477838151189)
              ·
                refine ⟨56818422093397398663337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1212126337992477838151189 56818422093397398663337)
                ·
                  rfl

theorem cell21_746911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 6].length) (baseStart_746911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746911 prefixEnd_746911 := by exact prefixLift 746911
  have htrace : WordTrace (prefixWord ++ tailWord_746911) baseStart_746911 baseEnd_746911 := by
    simpa [prefixWord, tailWord_746911, baseEnd_746911] using wordTrace_append hprefix tailTrace_746911
  have hstable : (prefixWord ++ tailWord_746911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746911).length < 2 ^ (prefixWord ++ tailWord_746911).sum := by decide
  have hdescent : baseEnd_746911 < baseStart_746911 := by decide
  rcases family_descends (prefixWord ++ tailWord_746911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_746956 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 6]
def baseStart_746956 : Nat := 118140960795 + 746956 * 2 ^ 59
def prefixEnd_746956 : Nat := 4983230072969 + 3 ^ 40 * 746956 * 2
def baseEnd_746956 : Nat := 170465535893282117739919

theorem tailTrace_746956 : CollatzResearch.WordTrace tailWord_746956 prefixEnd_746956 170465535893282117739919 := by
  unfold tailWord_746956
  simp only [CollatzResearch.WordTrace]
  refine ⟨13621861740956728386774361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18162482321275637849032481 13621861740956728386774361)
  ·
    refine ⟨10216396305717546290080771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13621861740956728386774361 10216396305717546290080771)
    ·
      refine ⟨15324594458576319435121157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10216396305717546290080771 15324594458576319435121157)
      ·
        refine ⟨2873361460983059894085217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15324594458576319435121157 2873361460983059894085217)
        ·
          refine ⟨2155021095737294920563913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2873361460983059894085217 2155021095737294920563913)
          ·
            refine ⟨1616265821802971190422935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2155021095737294920563913 1616265821802971190422935)
            ·
              refine ⟨2424398732704456785634403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1616265821802971190422935 2424398732704456785634403)
              ·
                refine ⟨3636598099056685178451605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2424398732704456785634403 3636598099056685178451605)
                ·
                  refine ⟨170465535893282117739919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3636598099056685178451605 170465535893282117739919)
                  ·
                    rfl

theorem cell21_746956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_746956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_746956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_746956 prefixEnd_746956 := by exact prefixLift 746956
  have htrace : WordTrace (prefixWord ++ tailWord_746956) baseStart_746956 baseEnd_746956 := by
    simpa [prefixWord, tailWord_746956, baseEnd_746956] using wordTrace_append hprefix tailTrace_746956
  have hstable : (prefixWord ++ tailWord_746956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_746956).length < 2 ^ (prefixWord ++ tailWord_746956).sum := by decide
  have hdescent : baseEnd_746956 < baseStart_746956 := by decide
  rcases family_descends (prefixWord ++ tailWord_746956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747018 : List Nat := [3, 1, 2, 2, 2, 4, 1, 1, 5]
def baseStart_747018 : Nat := 118140960795 + 747018 * 2 ^ 59
def prefixEnd_747018 : Nat := 4983230072969 + 3 ^ 40 * 747018 * 2
def baseEnd_747018 : Nat := 170479685137983787706459

theorem tailTrace_747018 : CollatzResearch.WordTrace tailWord_747018 prefixEnd_747018 170479685137983787706459 := by
  unfold tailWord_747018
  simp only [CollatzResearch.WordTrace]
  refine ⟨6811496201922210340576427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18163989871792560908203805 6811496201922210340576427)
  ·
    refine ⟨10217244302883315510864641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6811496201922210340576427 10217244302883315510864641)
    ·
      refine ⟨7662933227162486633148481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10217244302883315510864641 7662933227162486633148481)
      ·
        refine ⟨5747199920371864974861361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7662933227162486633148481 5747199920371864974861361)
        ·
          refine ⟨4310399940278898731146021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5747199920371864974861361 4310399940278898731146021)
          ·
            refine ⟨808199988802293512089879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4310399940278898731146021 808199988802293512089879)
            ·
              refine ⟨1212299983203440268134819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 808199988802293512089879 1212299983203440268134819)
              ·
                refine ⟨1818449974805160402202229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1212299983203440268134819 1818449974805160402202229)
                ·
                  refine ⟨170479685137983787706459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1818449974805160402202229 170479685137983787706459)
                  ·
                    rfl

theorem cell21_747018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_747018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_747018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_747018 prefixEnd_747018 := by exact prefixLift 747018
  have htrace : WordTrace (prefixWord ++ tailWord_747018) baseStart_747018 baseEnd_747018 := by
    simpa [prefixWord, tailWord_747018, baseEnd_747018] using wordTrace_append hprefix tailTrace_747018
  have hstable : (prefixWord ++ tailWord_747018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747018).length < 2 ^ (prefixWord ++ tailWord_747018).sum := by decide
  have hdescent : baseEnd_747018 < baseStart_747018 := by decide
  rcases family_descends (prefixWord ++ tailWord_747018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747021 : List Nat := [1, 7, 1, 1, 2, 1, 2, 6]
def baseStart_747021 : Nat := 118140960795 + 747021 * 2 ^ 59
def prefixEnd_747021 : Nat := 4983230072969 + 3 ^ 40 * 747021 * 2
def baseEnd_747021 : Nat := 56826789926285483052151

theorem tailTrace_747021 : CollatzResearch.WordTrace tailWord_747021 prefixEnd_747021 56826789926285483052151 := by
  unfold tailWord_747021
  simp only [CollatzResearch.WordTrace]
  refine ⟨27246094226677972874664917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18164062817785315249776611 27246094226677972874664917)
  ·
    refine ⟨638580333437764989249959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 27246094226677972874664917 638580333437764989249959)
    ·
      refine ⟨957870500156647483874939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 638580333437764989249959 957870500156647483874939)
      ·
        refine ⟨1436805750234971225812409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 957870500156647483874939 1436805750234971225812409)
        ·
          refine ⟨1077604312676228419359307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1436805750234971225812409 1077604312676228419359307)
          ·
            refine ⟨1616406469014342629038961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077604312676228419359307 1616406469014342629038961)
            ·
              refine ⟨1212304851760756971779221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1616406469014342629038961 1212304851760756971779221)
              ·
                refine ⟨56826789926285483052151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1212304851760756971779221 56826789926285483052151)
                ·
                  rfl

theorem cell21_747021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 6].length) (baseStart_747021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_747021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_747021 prefixEnd_747021 := by exact prefixLift 747021
  have htrace : WordTrace (prefixWord ++ tailWord_747021) baseStart_747021 baseEnd_747021 := by
    simpa [prefixWord, tailWord_747021, baseEnd_747021] using wordTrace_append hprefix tailTrace_747021
  have hstable : (prefixWord ++ tailWord_747021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747021).length < 2 ^ (prefixWord ++ tailWord_747021).sum := by decide
  have hdescent : baseEnd_747021 < baseStart_747021 := by decide
  rcases family_descends (prefixWord ++ tailWord_747021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747069 : List Nat := [1, 4, 1, 3, 4, 1, 2, 2, 3]
def baseStart_747069 : Nat := 118140960795 + 747069 * 2 ^ 59
def prefixEnd_747069 : Nat := 4983230072969 + 3 ^ 40 * 747069 * 2
def baseEnd_747069 : Nat := 170491324032819032356355

theorem tailTrace_747069 : CollatzResearch.WordTrace tailWord_747069 prefixEnd_747069 170491324032819032356355 := by
  unfold tailWord_747069
  simp only [CollatzResearch.WordTrace]
  refine ⟨27247844930504077072412261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18165229953669384714941507 27247844930504077072412261)
  ·
    refine ⟨5108970924469514451077299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27247844930504077072412261 5108970924469514451077299)
    ·
      refine ⟨7663456386704271676615949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5108970924469514451077299 7663456386704271676615949)
      ·
        refine ⟨2873796145014101878730981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7663456386704271676615949 2873796145014101878730981)
        ·
          refine ⟨538836777190144102262059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2873796145014101878730981 538836777190144102262059)
          ·
            refine ⟨808255165785216153393089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538836777190144102262059 808255165785216153393089)
            ·
              refine ⟨606191374338912115044817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 808255165785216153393089 606191374338912115044817)
              ·
                refine ⟨454643530754184086283613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 606191374338912115044817 454643530754184086283613)
                ·
                  refine ⟨170491324032819032356355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 454643530754184086283613 170491324032819032356355)
                  ·
                    rfl

theorem cell21_747069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_747069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_747069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_747069 prefixEnd_747069 := by exact prefixLift 747069
  have htrace : WordTrace (prefixWord ++ tailWord_747069) baseStart_747069 baseEnd_747069 := by
    simpa [prefixWord, tailWord_747069, baseEnd_747069] using wordTrace_append hprefix tailTrace_747069
  have hstable : (prefixWord ++ tailWord_747069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747069).length < 2 ^ (prefixWord ++ tailWord_747069).sum := by decide
  have hdescent : baseEnd_747069 < baseStart_747069 := by decide
  rcases family_descends (prefixWord ++ tailWord_747069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747122 : List Nat := [3, 2, 1, 2, 3, 2, 8]
def baseStart_747122 : Nat := 118140960795 + 747122 * 2 ^ 59
def prefixEnd_747122 : Nat := 4983230072969 + 3 ^ 40 * 747122 * 2
def baseEnd_747122 : Nat := 18944824372766968663657

theorem tailTrace_747122 : CollatzResearch.WordTrace tailWord_747122 prefixEnd_747122 18944824372766968663657 := by
  unfold tailWord_747122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6812444499828016781022905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18166518666208044749394413 6812444499828016781022905)
  ·
    refine ⟨5109333374871012585767179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6812444499828016781022905 5109333374871012585767179)
    ·
      refine ⟨7664000062306518878650769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5109333374871012585767179 7664000062306518878650769)
      ·
        refine ⟨5748000046729889158988077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7664000062306518878650769 5748000046729889158988077)
        ·
          refine ⟨2155500017523708434620529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5748000046729889158988077 2155500017523708434620529)
          ·
            refine ⟨1616625013142781325965397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2155500017523708434620529 1616625013142781325965397)
            ·
              refine ⟨18944824372766968663657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1616625013142781325965397 18944824372766968663657)
              ·
                rfl

theorem cell21_747122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 8].length) (baseStart_747122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_747122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_747122 prefixEnd_747122 := by exact prefixLift 747122
  have htrace : WordTrace (prefixWord ++ tailWord_747122) baseStart_747122 baseEnd_747122 := by
    simpa [prefixWord, tailWord_747122, baseEnd_747122] using wordTrace_append hprefix tailTrace_747122
  have hstable : (prefixWord ++ tailWord_747122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747122).length < 2 ^ (prefixWord ++ tailWord_747122).sum := by decide
  have hdescent : baseEnd_747122 < baseStart_747122 := by decide
  rcases family_descends (prefixWord ++ tailWord_747122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747125 : List Nat := [1, 3, 4, 2, 1, 1, 3, 2, 4]
def baseStart_747125 : Nat := 118140960795 + 747125 * 2 ^ 59
def prefixEnd_747125 : Nat := 4983230072969 + 3 ^ 40 * 747125 * 2
def baseEnd_747125 : Nat := 170504103995775379422907

theorem tailTrace_747125 : CollatzResearch.WordTrace tailWord_747125 prefixEnd_747125 170504103995775379422907 := by
  unfold tailWord_747125
  simp only [CollatzResearch.WordTrace]
  refine ⟨27249887418301198636450829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18166591612200799090967219 27249887418301198636450829)
  ·
    refine ⟨10218707781862949488669061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27249887418301198636450829 10218707781862949488669061)
    ·
      refine ⟨1916007709099303029125449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10218707781862949488669061 1916007709099303029125449)
      ·
        refine ⟨1437005781824477271844087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1916007709099303029125449 1437005781824477271844087)
        ·
          refine ⟨2155508672736715907766131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1437005781824477271844087 2155508672736715907766131)
          ·
            refine ⟨3233263009105073861649197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2155508672736715907766131 3233263009105073861649197)
            ·
              refine ⟨1212473628414402698118449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3233263009105073861649197 1212473628414402698118449)
              ·
                refine ⟨909355221310802023588837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1212473628414402698118449 909355221310802023588837)
                ·
                  refine ⟨170504103995775379422907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 909355221310802023588837 170504103995775379422907)
                  ·
                    rfl

theorem cell21_747125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_747125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_747125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_747125 prefixEnd_747125 := by exact prefixLift 747125
  have htrace : WordTrace (prefixWord ++ tailWord_747125) baseStart_747125 baseEnd_747125 := by
    simpa [prefixWord, tailWord_747125, baseEnd_747125] using wordTrace_append hprefix tailTrace_747125
  have hstable : (prefixWord ++ tailWord_747125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747125).length < 2 ^ (prefixWord ++ tailWord_747125).sum := by decide
  have hdescent : baseEnd_747125 < baseStart_747125 := by decide
  rcases family_descends (prefixWord ++ tailWord_747125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747198 : List Nat := [4, 2, 1, 1, 2, 2, 1, 8]
def baseStart_747198 : Nat := 118140960795 + 747198 * 2 ^ 59
def prefixEnd_747198 : Nat := 4983230072969 + 3 ^ 40 * 747198 * 2
def baseEnd_747198 : Nat := 56840254530114491568697

theorem tailTrace_747198 : CollatzResearch.WordTrace tailWord_747198 prefixEnd_747198 56840254530114491568697 := by
  unfold tailWord_747198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3406568743379591512982281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18168366631357821402572165 3406568743379591512982281)
  ·
    refine ⟨2554926557534693634736711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3406568743379591512982281 2554926557534693634736711)
    ·
      refine ⟨3832389836302040452105067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2554926557534693634736711 3832389836302040452105067)
      ·
        refine ⟨5748584754453060678157601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3832389836302040452105067 5748584754453060678157601)
        ·
          refine ⟨4311438565839795508618201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5748584754453060678157601 4311438565839795508618201)
          ·
            refine ⟨3233578924379846631463651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4311438565839795508618201 3233578924379846631463651)
            ·
              refine ⟨4850368386569769947195477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3233578924379846631463651 4850368386569769947195477)
              ·
                refine ⟨56840254530114491568697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4850368386569769947195477 56840254530114491568697)
                ·
                  rfl

theorem cell21_747198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_747198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_747198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_747198 prefixEnd_747198 := by exact prefixLift 747198
  have htrace : WordTrace (prefixWord ++ tailWord_747198) baseStart_747198 baseEnd_747198 := by
    simpa [prefixWord, tailWord_747198, baseEnd_747198] using wordTrace_append hprefix tailTrace_747198
  have hstable : (prefixWord ++ tailWord_747198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747198).length < 2 ^ (prefixWord ++ tailWord_747198).sum := by decide
  have hdescent : baseEnd_747198 < baseStart_747198 := by decide
  rcases family_descends (prefixWord ++ tailWord_747198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747243 : List Nat := [1, 1, 1, 1, 2, 4, 3, 4, 4]
def baseStart_747243 : Nat := 118140960795 + 747243 * 2 ^ 59
def prefixEnd_747243 : Nat := 4983230072969 + 3 ^ 40 * 747243 * 2
def baseEnd_747243 : Nat := 170531033203433396455999

theorem tailTrace_747243 : CollatzResearch.WordTrace tailWord_747243 prefixEnd_747243 170531033203433396455999 := by
  unfold tailWord_747243
  simp only [CollatzResearch.WordTrace]
  refine ⟨27254191231873704789246383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18169460821249136526164255 27254191231873704789246383)
  ·
    refine ⟨40881286847810557183869575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27254191231873704789246383 40881286847810557183869575)
    ·
      refine ⟨61321930271715835775804363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40881286847810557183869575 61321930271715835775804363)
      ·
        refine ⟨91982895407573753663706545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61321930271715835775804363 91982895407573753663706545)
        ·
          refine ⟨68987171555680315247779909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91982895407573753663706545 68987171555680315247779909)
          ·
            refine ⟨12935094666690059108958733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68987171555680315247779909 12935094666690059108958733)
            ·
              refine ⟨4850660500008772165859525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12935094666690059108958733 4850660500008772165859525)
              ·
                refine ⟨909498843751644781098661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4850660500008772165859525 909498843751644781098661)
                ·
                  refine ⟨170531033203433396455999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 909498843751644781098661 170531033203433396455999)
                  ·
                    rfl

theorem cell21_747243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 4].length) (baseStart_747243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_747243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_747243 prefixEnd_747243 := by exact prefixLift 747243
  have htrace : WordTrace (prefixWord ++ tailWord_747243) baseStart_747243 baseEnd_747243 := by
    simpa [prefixWord, tailWord_747243, baseEnd_747243] using wordTrace_append hprefix tailTrace_747243
  have hstable : (prefixWord ++ tailWord_747243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747243).length < 2 ^ (prefixWord ++ tailWord_747243).sum := by decide
  have hdescent : baseEnd_747243 < baseStart_747243 := by decide
  rcases family_descends (prefixWord ++ tailWord_747243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747246 : List Nat := [4, 1, 2, 1, 1, 2, 3, 4, 3]
def baseStart_747246 : Nat := 118140960795 + 747246 * 2 ^ 59
def prefixEnd_747246 : Nat := 4983230072969 + 3 ^ 40 * 747246 * 2
def baseEnd_747246 : Nat := 170531717844306057905993

theorem tailTrace_747246 : CollatzResearch.WordTrace tailWord_747246 prefixEnd_747246 170531717844306057905993 := by
  unfold tailWord_747246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3406787581357854537700699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18169533767241890867737061 3406787581357854537700699)
  ·
    refine ⟨5110181372036781806551049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3406787581357854537700699 5110181372036781806551049)
    ·
      refine ⟨3832636029027586354913287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5110181372036781806551049 3832636029027586354913287)
      ·
        refine ⟨5748954043541379532369931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3832636029027586354913287 5748954043541379532369931)
        ·
          refine ⟨8623431065312069298554897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5748954043541379532369931 8623431065312069298554897)
          ·
            refine ⟨6467573298984051973916173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8623431065312069298554897 6467573298984051973916173)
            ·
              refine ⟨2425339987119019490218565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6467573298984051973916173 2425339987119019490218565)
              ·
                refine ⟨454751247584816154415981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2425339987119019490218565 454751247584816154415981)
                ·
                  refine ⟨170531717844306057905993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 454751247584816154415981 170531717844306057905993)
                  ·
                    rfl

theorem cell21_747246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_747246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_747246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_747246 prefixEnd_747246 := by exact prefixLift 747246
  have htrace : WordTrace (prefixWord ++ tailWord_747246) baseStart_747246 baseEnd_747246 := by
    simpa [prefixWord, tailWord_747246, baseEnd_747246] using wordTrace_append hprefix tailTrace_747246
  have hstable : (prefixWord ++ tailWord_747246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747246).length < 2 ^ (prefixWord ++ tailWord_747246).sum := by decide
  have hdescent : baseEnd_747246 < baseStart_747246 := by decide
  rcases family_descends (prefixWord ++ tailWord_747246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747294 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 6]
def baseStart_747294 : Nat := 118140960795 + 747294 * 2 ^ 59
def prefixEnd_747294 : Nat := 4983230072969 + 3 ^ 40 * 747294 * 2
def baseEnd_747294 : Nat := 170542672098268641105895

theorem tailTrace_747294 : CollatzResearch.WordTrace tailWord_747294 prefixEnd_747294 170542672098268641105895 := by
  unfold tailWord_747294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3407006419336117562419117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18170700903125960332901957 3407006419336117562419117)
  ·
    refine ⟨1277627407251044085907169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3407006419336117562419117 1277627407251044085907169)
    ·
      refine ⟨958220555438283064430377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1277627407251044085907169 958220555438283064430377)
      ·
        refine ⟨718665416578712298322783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 958220555438283064430377 718665416578712298322783)
        ·
          refine ⟨1077998124868068447484175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 718665416578712298322783 1077998124868068447484175)
          ·
            refine ⟨1616997187302102671226263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077998124868068447484175 1616997187302102671226263)
            ·
              refine ⟨2425495780953154006839395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1616997187302102671226263 2425495780953154006839395)
              ·
                refine ⟨3638243671429731010259093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2425495780953154006839395 3638243671429731010259093)
                ·
                  refine ⟨170542672098268641105895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3638243671429731010259093 170542672098268641105895)
                  ·
                    rfl

theorem cell21_747294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_747294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_747294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_747294 prefixEnd_747294 := by exact prefixLift 747294
  have htrace : WordTrace (prefixWord ++ tailWord_747294) baseStart_747294 baseEnd_747294 := by
    simpa [prefixWord, tailWord_747294, baseEnd_747294] using wordTrace_append hprefix tailTrace_747294
  have hstable : (prefixWord ++ tailWord_747294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747294).length < 2 ^ (prefixWord ++ tailWord_747294).sum := by decide
  have hdescent : baseEnd_747294 < baseStart_747294 := by decide
  rcases family_descends (prefixWord ++ tailWord_747294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747333 : List Nat := [1, 3, 1, 1, 1, 2, 5, 7]
def baseStart_747333 : Nat := 118140960795 + 747333 * 2 ^ 59
def prefixEnd_747333 : Nat := 4983230072969 + 3 ^ 40 * 747333 * 2
def baseEnd_747333 : Nat := 56850524143204413318605

theorem tailTrace_747333 : CollatzResearch.WordTrace tailWord_747333 prefixEnd_747333 56850524143204413318605 := by
  unfold tailWord_747333
  simp only [CollatzResearch.WordTrace]
  refine ⟨27257473801547650160022653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18171649201031766773348435 27257473801547650160022653)
  ·
    refine ⟨10221552675580368810008495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27257473801547650160022653 10221552675580368810008495)
    ·
      refine ⟨15332329013370553215012743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10221552675580368810008495 15332329013370553215012743)
      ·
        refine ⟨22998493520055829822519115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15332329013370553215012743 22998493520055829822519115)
        ·
          refine ⟨34497740280083744733778673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22998493520055829822519115 34497740280083744733778673)
          ·
            refine ⟨25873305210062808550334005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34497740280083744733778673 25873305210062808550334005)
            ·
              refine ⟨2425622363443388301593813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25873305210062808550334005 2425622363443388301593813)
              ·
                refine ⟨56850524143204413318605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2425622363443388301593813 56850524143204413318605)
                ·
                  rfl

theorem cell21_747333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 7].length) (baseStart_747333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_747333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_747333 prefixEnd_747333 := by exact prefixLift 747333
  have htrace : WordTrace (prefixWord ++ tailWord_747333) baseStart_747333 baseEnd_747333 := by
    simpa [prefixWord, tailWord_747333, baseEnd_747333] using wordTrace_append hprefix tailTrace_747333
  have hstable : (prefixWord ++ tailWord_747333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747333).length < 2 ^ (prefixWord ++ tailWord_747333).sum := by decide
  have hdescent : baseEnd_747333 < baseStart_747333 := by decide
  rcases family_descends (prefixWord ++ tailWord_747333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747356 : List Nat := [2, 2, 4, 2, 2, 1, 3, 2, 3]
def baseStart_747356 : Nat := 118140960795 + 747356 * 2 ^ 59
def prefixEnd_747356 : Nat := 4983230072969 + 3 ^ 40 * 747356 * 2
def baseEnd_747356 : Nat := 170556821342970311072435

theorem tailTrace_747356 : CollatzResearch.WordTrace tailWord_747356 prefixEnd_747356 170556821342970311072435 := by
  unfold tailWord_747356
  simp only [CollatzResearch.WordTrace]
  refine ⟨13629156340232162544054961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18172208453642883392073281 13629156340232162544054961)
  ·
    refine ⟨10221867255174121908041221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13629156340232162544054961 10221867255174121908041221)
    ·
      refine ⟨1916600110345147857757729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10221867255174121908041221 1916600110345147857757729)
      ·
        refine ⟨1437450082758860893318297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1916600110345147857757729 1437450082758860893318297)
        ·
          refine ⟨1078087562069145669988723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1437450082758860893318297 1078087562069145669988723)
          ·
            refine ⟨1617131343103718504983085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078087562069145669988723 1617131343103718504983085)
            ·
              refine ⟨606424253663894439368657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1617131343103718504983085 606424253663894439368657)
              ·
                refine ⟨454818190247920829526493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 606424253663894439368657 454818190247920829526493)
                ·
                  refine ⟨170556821342970311072435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 454818190247920829526493 170556821342970311072435)
                  ·
                    rfl

theorem cell21_747356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 3].length) (baseStart_747356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_747356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_747356 prefixEnd_747356 := by exact prefixLift 747356
  have htrace : WordTrace (prefixWord ++ tailWord_747356) baseStart_747356 baseEnd_747356 := by
    simpa [prefixWord, tailWord_747356, baseEnd_747356] using wordTrace_append hprefix tailTrace_747356
  have hstable : (prefixWord ++ tailWord_747356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747356).length < 2 ^ (prefixWord ++ tailWord_747356).sum := by decide
  have hdescent : baseEnd_747356 < baseStart_747356 := by decide
  rcases family_descends (prefixWord ++ tailWord_747356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747412 : List Nat := [2, 4, 2, 1, 1, 2, 1, 4, 4]
def baseStart_747412 : Nat := 118140960795 + 747412 * 2 ^ 59
def prefixEnd_747412 : Nat := 4983230072969 + 3 ^ 40 * 747412 * 2
def baseEnd_747412 : Nat := 170569601305926658138987

theorem tailTrace_747412 : CollatzResearch.WordTrace tailWord_747412 prefixEnd_747412 170569601305926658138987 := by
  unfold tailWord_747412
  simp only [CollatzResearch.WordTrace]
  refine ⟨13630177584130723326074245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18173570112174297768098993 13630177584130723326074245)
  ·
    refine ⟨2555658297024510623638921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13630177584130723326074245 2555658297024510623638921)
    ·
      refine ⟨1916743722768382967729191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2555658297024510623638921 1916743722768382967729191)
      ·
        refine ⟨2875115584152574451593787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1916743722768382967729191 2875115584152574451593787)
        ·
          refine ⟨4312673376228861677390681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2875115584152574451593787 4312673376228861677390681)
          ·
            refine ⟨3234505032171646258043011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4312673376228861677390681 3234505032171646258043011)
            ·
              refine ⟨4851757548257469387064517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3234505032171646258043011 4851757548257469387064517)
              ·
                refine ⟨909704540298275510074597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4851757548257469387064517 909704540298275510074597)
                ·
                  refine ⟨170569601305926658138987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 909704540298275510074597 170569601305926658138987)
                  ·
                    rfl

theorem cell21_747412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_747412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_747412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_747412 prefixEnd_747412 := by exact prefixLift 747412
  have htrace : WordTrace (prefixWord ++ tailWord_747412) baseStart_747412 baseEnd_747412 := by
    simpa [prefixWord, tailWord_747412, baseEnd_747412] using wordTrace_append hprefix tailTrace_747412
  have hstable : (prefixWord ++ tailWord_747412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747412).length < 2 ^ (prefixWord ++ tailWord_747412).sum := by decide
  have hdescent : baseEnd_747412 < baseStart_747412 := by decide
  rcases family_descends (prefixWord ++ tailWord_747412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747415 : List Nat := [1, 1, 3, 3, 1, 5, 2, 2, 3]
def baseStart_747415 : Nat := 118140960795 + 747415 * 2 ^ 59
def prefixEnd_747415 : Nat := 4983230072969 + 3 ^ 40 * 747415 * 2
def baseEnd_747415 : Nat := 170570285946799319588981

theorem tailTrace_747415 : CollatzResearch.WordTrace tailWord_747415 prefixEnd_747415 170570285946799319588981 := by
  unfold tailWord_747415
  simp only [CollatzResearch.WordTrace]
  refine ⟨27260464587250578164507699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18173643058167052109671799 27260464587250578164507699)
  ·
    refine ⟨40890696880875867246761549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27260464587250578164507699 40890696880875867246761549)
    ·
      refine ⟨15334011330328450217535581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40890696880875867246761549 15334011330328450217535581)
      ·
        refine ⟨5750254248873168831575843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15334011330328450217535581 5750254248873168831575843)
        ·
          refine ⟨8625381373309753247363765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5750254248873168831575843 8625381373309753247363765)
          ·
            refine ⟨808629503747789366940353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8625381373309753247363765 808629503747789366940353)
            ·
              refine ⟨606472127810842025205265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 808629503747789366940353 606472127810842025205265)
              ·
                refine ⟨454854095858131518903949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 606472127810842025205265 454854095858131518903949)
                ·
                  refine ⟨170570285946799319588981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 454854095858131518903949 170570285946799319588981)
                  ·
                    rfl

theorem cell21_747415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 3].length) (baseStart_747415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_747415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_747415 prefixEnd_747415 := by exact prefixLift 747415
  have htrace : WordTrace (prefixWord ++ tailWord_747415) baseStart_747415 baseEnd_747415 := by
    simpa [prefixWord, tailWord_747415, baseEnd_747415] using wordTrace_append hprefix tailTrace_747415
  have hstable : (prefixWord ++ tailWord_747415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747415).length < 2 ^ (prefixWord ++ tailWord_747415).sum := by decide
  have hdescent : baseEnd_747415 < baseStart_747415 := by decide
  rcases family_descends (prefixWord ++ tailWord_747415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747474 : List Nat := [3, 2, 2, 3, 2, 1, 2, 1, 5]
def baseStart_747474 : Nat := 118140960795 + 747474 * 2 ^ 59
def prefixEnd_747474 : Nat := 4983230072969 + 3 ^ 40 * 747474 * 2
def baseEnd_747474 : Nat := 170583750550628328105527

theorem tailTrace_747474 : CollatzResearch.WordTrace tailWord_747474 prefixEnd_747474 170583750550628328105527 := by
  unfold tailWord_747474
  simp only [CollatzResearch.WordTrace]
  refine ⟨6815654123509207810226369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18175077662691220827270317 6815654123509207810226369)
  ·
    refine ⟨5111740592631905857669777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6815654123509207810226369 5111740592631905857669777)
    ·
      refine ⟨3833805444473929393252333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5111740592631905857669777 3833805444473929393252333)
      ·
        refine ⟨1437677041677723522469625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3833805444473929393252333 1437677041677723522469625)
        ·
          refine ⟨1078257781258292641852219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1437677041677723522469625 1078257781258292641852219)
          ·
            refine ⟨1617386671887438962778329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078257781258292641852219 1617386671887438962778329)
            ·
              refine ⟨1213040003915579222083747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1617386671887438962778329 1213040003915579222083747)
              ·
                refine ⟨1819560005873368833125621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213040003915579222083747 1819560005873368833125621)
                ·
                  refine ⟨170583750550628328105527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1819560005873368833125621 170583750550628328105527)
                  ·
                    rfl

theorem cell21_747474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_747474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_747474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_747474 prefixEnd_747474 := by exact prefixLift 747474
  have htrace : WordTrace (prefixWord ++ tailWord_747474) baseStart_747474 baseEnd_747474 := by
    simpa [prefixWord, tailWord_747474, baseEnd_747474] using wordTrace_append hprefix tailTrace_747474
  have hstable : (prefixWord ++ tailWord_747474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747474).length < 2 ^ (prefixWord ++ tailWord_747474).sum := by decide
  have hdescent : baseEnd_747474 < baseStart_747474 := by decide
  rcases family_descends (prefixWord ++ tailWord_747474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747502 : List Nat := [4, 1, 2, 1, 3, 2, 1, 7]
def baseStart_747502 : Nat := 118140960795 + 747502 * 2 ^ 59
def prefixEnd_747502 : Nat := 4983230072969 + 3 ^ 40 * 747502 * 2
def baseEnd_747502 : Nat := 56863380177368833879601

theorem tailTrace_747502 : CollatzResearch.WordTrace tailWord_747502 prefixEnd_747502 56863380177368833879601 := by
  unfold tailWord_747502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3407954717241924002865595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18175758491956928015283173 3407954717241924002865595)
  ·
    refine ⟨5111932075862886004298393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3407954717241924002865595 5111932075862886004298393)
    ·
      refine ⟨3833949056897164503223795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5111932075862886004298393 3833949056897164503223795)
      ·
        refine ⟨5750923585345746754835693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3833949056897164503223795 5750923585345746754835693)
        ·
          refine ⟨2156596344504655033063385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5750923585345746754835693 2156596344504655033063385)
          ·
            refine ⟨1617447258378491274797539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2156596344504655033063385 1617447258378491274797539)
            ·
              refine ⟨2426170887567736912196309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1617447258378491274797539 2426170887567736912196309)
              ·
                refine ⟨56863380177368833879601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2426170887567736912196309 56863380177368833879601)
                ·
                  rfl

theorem cell21_747502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_747502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_747502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_747502 prefixEnd_747502 := by exact prefixLift 747502
  have htrace : WordTrace (prefixWord ++ tailWord_747502) baseStart_747502 baseEnd_747502 := by
    simpa [prefixWord, tailWord_747502, baseEnd_747502] using wordTrace_append hprefix tailTrace_747502
  have hstable : (prefixWord ++ tailWord_747502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747502).length < 2 ^ (prefixWord ++ tailWord_747502).sum := by decide
  have hdescent : baseEnd_747502 < baseStart_747502 := by decide
  rcases family_descends (prefixWord ++ tailWord_747502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747671 : List Nat := [1, 1, 3, 3, 4, 2, 2, 5]
def baseStart_747671 : Nat := 118140960795 + 747671 * 2 ^ 59
def prefixEnd_747671 : Nat := 4983230072969 + 3 ^ 40 * 747671 * 2
def baseEnd_747671 : Nat := 56876236211533254440597

theorem tailTrace_747671 : CollatzResearch.WordTrace tailWord_747671 prefixEnd_747671 56876236211533254440597 := by
  unfold tailWord_747671
  simp only [CollatzResearch.WordTrace]
  refine ⟨27269801674323133885826867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18179867782882089257217911 27269801674323133885826867)
  ·
    refine ⟨40904702511484700828740301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27269801674323133885826867 40904702511484700828740301)
    ·
      refine ⟨15339263441806762810777613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40904702511484700828740301 15339263441806762810777613)
      ·
        refine ⟨5752223790677536054041605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15339263441806762810777613 5752223790677536054041605)
        ·
          refine ⟨1078541960752038010132801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5752223790677536054041605 1078541960752038010132801)
          ·
            refine ⟨808906470564028507599601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1078541960752038010132801 808906470564028507599601)
            ·
              refine ⟨606679852923021380699701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 808906470564028507599601 606679852923021380699701)
              ·
                refine ⟨56876236211533254440597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 606679852923021380699701 56876236211533254440597)
                ·
                  rfl

theorem cell21_747671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 5].length) (baseStart_747671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_747671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_747671 prefixEnd_747671 := by exact prefixLift 747671
  have htrace : WordTrace (prefixWord ++ tailWord_747671) baseStart_747671 baseEnd_747671 := by
    simpa [prefixWord, tailWord_747671, baseEnd_747671] using wordTrace_append hprefix tailTrace_747671
  have hstable : (prefixWord ++ tailWord_747671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747671).length < 2 ^ (prefixWord ++ tailWord_747671).sum := by decide
  have hdescent : baseEnd_747671 < baseStart_747671 := by decide
  rcases family_descends (prefixWord ++ tailWord_747671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747716 : List Nat := [2, 3, 3, 1, 2, 2, 1, 3, 4]
def baseStart_747716 : Nat := 118140960795 + 747716 * 2 ^ 59
def prefixEnd_747716 : Nat := 4983230072969 + 3 ^ 40 * 747716 * 2
def baseEnd_747716 : Nat := 170638978247689685071699

theorem tailTrace_747716 : CollatzResearch.WordTrace tailWord_747716 prefixEnd_747716 170638978247689685071699 := by
  unfold tailWord_747716
  simp only [CollatzResearch.WordTrace]
  refine ⟨13635721479580053285607501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18180961972773404380810001 13635721479580053285607501)
  ·
    refine ⟨5113395554842519982102813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13635721479580053285607501 5113395554842519982102813)
    ·
      refine ⟨1917523333065944993288555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5113395554842519982102813 1917523333065944993288555)
      ·
        refine ⟨2876284999598917489932833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1917523333065944993288555 2876284999598917489932833)
        ·
          refine ⟨2157213749699188117449625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2876284999598917489932833 2157213749699188117449625)
          ·
            refine ⟨1617910312274391088087219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2157213749699188117449625 1617910312274391088087219)
            ·
              refine ⟨2426865468411586632130829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1617910312274391088087219 2426865468411586632130829)
              ·
                refine ⟨910074550654344987049061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2426865468411586632130829 910074550654344987049061)
                ·
                  refine ⟨170638978247689685071699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 910074550654344987049061 170638978247689685071699)
                  ·
                    rfl

theorem cell21_747716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_747716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_747716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_747716 prefixEnd_747716 := by exact prefixLift 747716
  have htrace : WordTrace (prefixWord ++ tailWord_747716) baseStart_747716 baseEnd_747716 := by
    simpa [prefixWord, tailWord_747716, baseEnd_747716] using wordTrace_append hprefix tailTrace_747716
  have hstable : (prefixWord ++ tailWord_747716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747716).length < 2 ^ (prefixWord ++ tailWord_747716).sum := by decide
  have hdescent : baseEnd_747716 < baseStart_747716 := by decide
  rcases family_descends (prefixWord ++ tailWord_747716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747727 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 7]
def baseStart_747727 : Nat := 118140960795 + 747727 * 2 ^ 59
def prefixEnd_747727 : Nat := 4983230072969 + 3 ^ 40 * 747727 * 2
def baseEnd_747727 : Nat := 170641488597556110388343

theorem tailTrace_747727 : CollatzResearch.WordTrace tailWord_747727 prefixEnd_747727 170641488597556110388343 := by
  unfold tailWord_747727
  simp only [CollatzResearch.WordTrace]
  refine ⟨27271844162120255449865435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18181229441413503633243623 27271844162120255449865435)
  ·
    refine ⟨40907766243180383174798153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27271844162120255449865435 40907766243180383174798153)
    ·
      refine ⟨30680824682385287381098615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40907766243180383174798153 30680824682385287381098615)
      ·
        refine ⟨46021237023577931071647923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30680824682385287381098615 46021237023577931071647923)
        ·
          refine ⟨69031855535366896607471885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46021237023577931071647923 69031855535366896607471885)
          ·
            refine ⟨25886945825762586227801957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69031855535366896607471885 25886945825762586227801957)
            ·
              refine ⟨4853802342330484917712867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25886945825762586227801957 4853802342330484917712867)
              ·
                refine ⟨7280703513495727376569301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4853802342330484917712867 7280703513495727376569301)
                ·
                  refine ⟨170641488597556110388343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7280703513495727376569301 170641488597556110388343)
                  ·
                    rfl

theorem cell21_747727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 7].length) (baseStart_747727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_747727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_747727 prefixEnd_747727 := by exact prefixLift 747727
  have htrace : WordTrace (prefixWord ++ tailWord_747727) baseStart_747727 baseEnd_747727 := by
    simpa [prefixWord, tailWord_747727, baseEnd_747727] using wordTrace_append hprefix tailTrace_747727
  have hstable : (prefixWord ++ tailWord_747727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747727).length < 2 ^ (prefixWord ++ tailWord_747727).sum := by decide
  have hdescent : baseEnd_747727 < baseStart_747727 := by decide
  rcases family_descends (prefixWord ++ tailWord_747727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747882 : List Nat := [3, 1, 3, 3, 1, 2, 2, 6]
def baseStart_747882 : Nat := 118140960795 + 747882 * 2 ^ 59
def prefixEnd_747882 : Nat := 4983230072969 + 3 ^ 40 * 747882 * 2
def baseEnd_747882 : Nat := 56892287236436761768231

theorem tailTrace_747882 : CollatzResearch.WordTrace tailWord_747882 prefixEnd_747882 56892287236436761768231 := by
  unfold tailWord_747882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6819374369139679230439475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18184998317705811281171933 6819374369139679230439475)
  ·
    refine ⟨10229061553709518845659213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6819374369139679230439475 10229061553709518845659213)
    ·
      refine ⟨3835898082641069567122205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10229061553709518845659213 3835898082641069567122205)
      ·
        refine ⟨1438461780990401087670827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3835898082641069567122205 1438461780990401087670827)
        ·
          refine ⟨2157692671485601631506241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438461780990401087670827 2157692671485601631506241)
          ·
            refine ⟨1618269503614201223629681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2157692671485601631506241 1618269503614201223629681)
            ·
              refine ⟨1213702127710650917722261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1618269503614201223629681 1213702127710650917722261)
              ·
                refine ⟨56892287236436761768231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1213702127710650917722261 56892287236436761768231)
                ·
                  rfl

theorem cell21_747882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_747882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_747882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_747882 prefixEnd_747882 := by exact prefixLift 747882
  have htrace : WordTrace (prefixWord ++ tailWord_747882) baseStart_747882 baseEnd_747882 := by
    simpa [prefixWord, tailWord_747882, baseEnd_747882] using wordTrace_append hprefix tailTrace_747882
  have hstable : (prefixWord ++ tailWord_747882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747882).length < 2 ^ (prefixWord ++ tailWord_747882).sum := by decide
  have hdescent : baseEnd_747882 < baseStart_747882 := by decide
  rcases family_descends (prefixWord ++ tailWord_747882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747930 : List Nat := [3, 1, 1, 4, 1, 2, 4, 2, 3]
def baseStart_747930 : Nat := 118140960795 + 747930 * 2 ^ 59
def prefixEnd_747930 : Nat := 4983230072969 + 3 ^ 40 * 747930 * 2
def baseEnd_747930 : Nat := 170687815963272868504595

theorem tailTrace_747930 : CollatzResearch.WordTrace tailWord_747930 prefixEnd_747930 170687815963272868504595 := by
  unfold tailWord_747930
  simp only [CollatzResearch.WordTrace]
  refine ⟨6819812045096205279876311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18186165453589880746336829 6819812045096205279876311)
  ·
    refine ⟨10229718067644307919814467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6819812045096205279876311 10229718067644307919814467)
    ·
      refine ⟨15344577101466461879721701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10229718067644307919814467 15344577101466461879721701)
      ·
        refine ⟨2877108206524961602447819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15344577101466461879721701 2877108206524961602447819)
        ·
          refine ⟨4315662309787442403671729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2877108206524961602447819 4315662309787442403671729)
          ·
            refine ⟨3236746732340581802753797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4315662309787442403671729 3236746732340581802753797)
            ·
              refine ⟨606890012313859088016337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3236746732340581802753797 606890012313859088016337)
              ·
                refine ⟨455167509235394316012253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 606890012313859088016337 455167509235394316012253)
                ·
                  refine ⟨170687815963272868504595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 455167509235394316012253 170687815963272868504595)
                  ·
                    rfl

theorem cell21_747930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 3].length) (baseStart_747930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_747930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_747930 prefixEnd_747930 := by exact prefixLift 747930
  have htrace : WordTrace (prefixWord ++ tailWord_747930) baseStart_747930 baseEnd_747930 := by
    simpa [prefixWord, tailWord_747930, baseEnd_747930] using wordTrace_append hprefix tailTrace_747930
  have hstable : (prefixWord ++ tailWord_747930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747930).length < 2 ^ (prefixWord ++ tailWord_747930).sum := by decide
  have hdescent : baseEnd_747930 < baseStart_747930 := by decide
  rcases family_descends (prefixWord ++ tailWord_747930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747944 : List Nat := [2, 1, 6, 1, 1, 1, 2, 3, 4]
def baseStart_747944 : Nat := 118140960795 + 747944 * 2 ^ 59
def prefixEnd_747944 : Nat := 4983230072969 + 3 ^ 40 * 747944 * 2
def baseEnd_747944 : Nat := 170691010954011955271233

theorem tailTrace_747944 : CollatzResearch.WordTrace tailWord_747944 prefixEnd_747944 170691010954011955271233 := by
  unfold tailWord_747944
  simp only [CollatzResearch.WordTrace]
  refine ⟨13639879401167050755257443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18186505868222734340343257 13639879401167050755257443)
  ·
    refine ⟨20459819101750576132886165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13639879401167050755257443 20459819101750576132886165)
    ·
      refine ⟨959054020394558256229039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20459819101750576132886165 959054020394558256229039)
      ·
        refine ⟨1438581030591837384343559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 959054020394558256229039 1438581030591837384343559)
        ·
          refine ⟨2157871545887756076515339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438581030591837384343559 2157871545887756076515339)
          ·
            refine ⟨3236807318831634114773009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157871545887756076515339 3236807318831634114773009)
            ·
              refine ⟨2427605489123725586079757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3236807318831634114773009 2427605489123725586079757)
              ·
                refine ⟨910352058421397094779909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2427605489123725586079757 910352058421397094779909)
                ·
                  refine ⟨170691010954011955271233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 910352058421397094779909 170691010954011955271233)
                  ·
                    rfl

theorem cell21_747944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 4].length) (baseStart_747944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_747944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_747944 prefixEnd_747944 := by exact prefixLift 747944
  have htrace : WordTrace (prefixWord ++ tailWord_747944) baseStart_747944 baseEnd_747944 := by
    simpa [prefixWord, tailWord_747944, baseEnd_747944] using wordTrace_append hprefix tailTrace_747944
  have hstable : (prefixWord ++ tailWord_747944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747944).length < 2 ^ (prefixWord ++ tailWord_747944).sum := by decide
  have hdescent : baseEnd_747944 < baseStart_747944 := by decide
  rcases family_descends (prefixWord ++ tailWord_747944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_747989 : List Nat := [1, 3, 2, 3, 1, 2, 2, 4, 3]
def baseStart_747989 : Nat := 118140960795 + 747989 * 2 ^ 59
def prefixEnd_747989 : Nat := 4983230072969 + 3 ^ 40 * 747989 * 2
def baseEnd_747989 : Nat := 170701280567101877021141

theorem tailTrace_747989 : CollatzResearch.WordTrace tailWord_747989 prefixEnd_747989 170701280567101877021141 := by
  unfold tailWord_747989
  simp only [CollatzResearch.WordTrace]
  refine ⟨27281400087171074195903021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18187600058114049463935347 27281400087171074195903021)
  ·
    refine ⟨10230525032689152823463633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27281400087171074195903021 10230525032689152823463633)
    ·
      refine ⟨7672893774516864617597725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10230525032689152823463633 7672893774516864617597725)
      ·
        refine ⟨2877335165443824231599147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7672893774516864617597725 2877335165443824231599147)
        ·
          refine ⟨4316002748165736347398721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2877335165443824231599147 4316002748165736347398721)
          ·
            refine ⟨3237002061124302260549041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4316002748165736347398721 3237002061124302260549041)
            ·
              refine ⟨2427751545843226695411781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3237002061124302260549041 2427751545843226695411781)
              ·
                refine ⟨455203414845605005389709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2427751545843226695411781 455203414845605005389709)
                ·
                  refine ⟨170701280567101877021141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 455203414845605005389709 170701280567101877021141)
                  ·
                    rfl

theorem cell21_747989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 3].length) (baseStart_747989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_747989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_747989 prefixEnd_747989 := by exact prefixLift 747989
  have htrace : WordTrace (prefixWord ++ tailWord_747989) baseStart_747989 baseEnd_747989 := by
    simpa [prefixWord, tailWord_747989, baseEnd_747989] using wordTrace_append hprefix tailTrace_747989
  have hstable : (prefixWord ++ tailWord_747989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_747989).length < 2 ^ (prefixWord ++ tailWord_747989).sum := by decide
  have hdescent : baseEnd_747989 < baseStart_747989 := by decide
  rcases family_descends (prefixWord ++ tailWord_747989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748000 : List Nat := [2, 1, 1, 3, 1, 1, 4, 8]
def baseStart_748000 : Nat := 118140960795 + 748000 * 2 ^ 59
def prefixEnd_748000 : Nat := 4983230072969 + 3 ^ 40 * 748000 * 2
def baseEnd_748000 : Nat := 56901263638989434112595

theorem tailTrace_748000 : CollatzResearch.WordTrace tailWord_748000 prefixEnd_748000 56901263638989434112595 := by
  unfold tailWord_748000
  simp only [CollatzResearch.WordTrace]
  refine ⟨13640900645065611537276727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18187867526754148716368969 13640900645065611537276727)
  ·
    refine ⟨20461350967598417305915091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13640900645065611537276727 20461350967598417305915091)
    ·
      refine ⟨30692026451397625958872637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20461350967598417305915091 30692026451397625958872637)
      ·
        refine ⟨11509509919274109734577239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30692026451397625958872637 11509509919274109734577239)
        ·
          refine ⟨17264264878911164601865859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11509509919274109734577239 17264264878911164601865859)
          ·
            refine ⟨25896397318366746902798789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17264264878911164601865859 25896397318366746902798789)
            ·
              refine ⟨4855574497193765044274773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25896397318366746902798789 4855574497193765044274773)
              ·
                refine ⟨56901263638989434112595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4855574497193765044274773 56901263638989434112595)
                ·
                  rfl

theorem cell21_748000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 8].length) (baseStart_748000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_748000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_748000 prefixEnd_748000 := by exact prefixLift 748000
  have htrace : WordTrace (prefixWord ++ tailWord_748000) baseStart_748000 baseEnd_748000 := by
    simpa [prefixWord, tailWord_748000, baseEnd_748000] using wordTrace_append hprefix tailTrace_748000
  have hstable : (prefixWord ++ tailWord_748000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748000).length < 2 ^ (prefixWord ++ tailWord_748000).sum := by decide
  have hdescent : baseEnd_748000 < baseStart_748000 := by decide
  rcases family_descends (prefixWord ++ tailWord_748000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748121 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 10]
def baseStart_748121 : Nat := 118140960795 + 748121 * 2 ^ 59
def prefixEnd_748121 : Nat := 4983230072969 + 3 ^ 40 * 748121 * 2
def baseEnd_748121 : Nat := 170731404765498980820871

theorem tailTrace_748121 : CollatzResearch.WordTrace tailWord_748121 prefixEnd_748121 170731404765498980820871 := by
  unfold tailWord_748121
  simp only [CollatzResearch.WordTrace]
  refine ⟨27286214522692860739708217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18190809681795240493138811 27286214522692860739708217)
  ·
    refine ⟨20464660892019645554781163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27286214522692860739708217 20464660892019645554781163)
    ·
      refine ⟨30696991338029468332171745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20464660892019645554781163 30696991338029468332171745)
      ·
        refine ⟨23022743503522101249128809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30696991338029468332171745 23022743503522101249128809)
        ·
          refine ⟨17267057627641575936846607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23022743503522101249128809 17267057627641575936846607)
          ·
            refine ⟨25900586441462363905269911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17267057627641575936846607 25900586441462363905269911)
            ·
              refine ⟨38850879662193545857904867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25900586441462363905269911 38850879662193545857904867)
              ·
                refine ⟨58276319493290318786857301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38850879662193545857904867 58276319493290318786857301)
                ·
                  refine ⟨170731404765498980820871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 58276319493290318786857301 170731404765498980820871)
                  ·
                    rfl

theorem cell21_748121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_748121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_748121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_748121 prefixEnd_748121 := by exact prefixLift 748121
  have htrace : WordTrace (prefixWord ++ tailWord_748121) baseStart_748121 baseEnd_748121 := by
    simpa [prefixWord, tailWord_748121, baseEnd_748121] using wordTrace_append hprefix tailTrace_748121
  have hstable : (prefixWord ++ tailWord_748121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748121).length < 2 ^ (prefixWord ++ tailWord_748121).sum := by decide
  have hdescent : baseEnd_748121 < baseStart_748121 := by decide
  rcases family_descends (prefixWord ++ tailWord_748121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748138 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 6]
def baseStart_748138 : Nat := 118140960795 + 748138 * 2 ^ 59
def prefixEnd_748138 : Nat := 4983230072969 + 3 ^ 40 * 748138 * 2
def baseEnd_748138 : Nat := 170735284397110729037503

theorem tailTrace_748138 : CollatzResearch.WordTrace tailWord_748138 prefixEnd_748138 170735284397110729037503 := by
  unfold tailWord_748138
  simp only [CollatzResearch.WordTrace]
  refine ⟨6821708640907818160769267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18191223042420848428718045 6821708640907818160769267)
  ·
    refine ⟨10232562961361727241153901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6821708640907818160769267 10232562961361727241153901)
    ·
      refine ⟨3837211110510647715432713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10232562961361727241153901 3837211110510647715432713)
      ·
        refine ⟨2877908332882985786574535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3837211110510647715432713 2877908332882985786574535)
        ·
          refine ⟨4316862499324478679861803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2877908332882985786574535 4316862499324478679861803)
          ·
            refine ⟨6475293748986718019792705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4316862499324478679861803 6475293748986718019792705)
            ·
              refine ⟨4856470311740038514844529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6475293748986718019792705 4856470311740038514844529)
              ·
                refine ⟨3642352733805028886133397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4856470311740038514844529 3642352733805028886133397)
                ·
                  refine ⟨170735284397110729037503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3642352733805028886133397 170735284397110729037503)
                  ·
                    rfl

theorem cell21_748138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_748138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_748138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_748138 prefixEnd_748138 := by exact prefixLift 748138
  have htrace : WordTrace (prefixWord ++ tailWord_748138) baseStart_748138 baseEnd_748138 := by
    simpa [prefixWord, tailWord_748138, baseEnd_748138] using wordTrace_append hprefix tailTrace_748138
  have hstable : (prefixWord ++ tailWord_748138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748138).length < 2 ^ (prefixWord ++ tailWord_748138).sum := by decide
  have hdescent : baseEnd_748138 < baseStart_748138 := by decide
  rcases family_descends (prefixWord ++ tailWord_748138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748141 : List Nat := [1, 5, 1, 1, 3, 1, 1, 5, 3]
def baseStart_748141 : Nat := 118140960795 + 748141 * 2 ^ 59
def prefixEnd_748141 : Nat := 4983230072969 + 3 ^ 40 * 748141 * 2
def baseEnd_748141 : Nat := 170735969037983390487497

theorem tailTrace_748141 : CollatzResearch.WordTrace tailWord_748141 prefixEnd_748141 170735969037983390487497 := by
  unfold tailWord_748141
  simp only [CollatzResearch.WordTrace]
  refine ⟨27286943982620404155436277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18191295988413602770290851 27286943982620404155436277)
  ·
    refine ⟨2558150998370662889572151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27286943982620404155436277 2558150998370662889572151)
    ·
      refine ⟨3837226497555994334358227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2558150998370662889572151 3837226497555994334358227)
      ·
        refine ⟨5755839746333991501537341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3837226497555994334358227 5755839746333991501537341)
        ·
          refine ⟨2158439904875246813076503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5755839746333991501537341 2158439904875246813076503)
          ·
            refine ⟨3237659857312870219614755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2158439904875246813076503 3237659857312870219614755)
            ·
              refine ⟨4856489785969305329422133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3237659857312870219614755 4856489785969305329422133)
              ·
                refine ⟨455295917434622374633325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4856489785969305329422133 455295917434622374633325)
                ·
                  refine ⟨170735969037983390487497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 455295917434622374633325 170735969037983390487497)
                  ·
                    rfl

theorem cell21_748141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_748141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_748141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_748141 prefixEnd_748141 := by exact prefixLift 748141
  have htrace : WordTrace (prefixWord ++ tailWord_748141) baseStart_748141 baseEnd_748141 := by
    simpa [prefixWord, tailWord_748141, baseEnd_748141] using wordTrace_append hprefix tailTrace_748141
  have hstable : (prefixWord ++ tailWord_748141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748141).length < 2 ^ (prefixWord ++ tailWord_748141).sum := by decide
  have hdescent : baseEnd_748141 < baseStart_748141 := by decide
  rcases family_descends (prefixWord ++ tailWord_748141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748183 : List Nat := [1, 1, 3, 3, 2, 1, 1, 4, 5]
def baseStart_748183 : Nat := 118140960795 + 748183 * 2 ^ 59
def prefixEnd_748183 : Nat := 4983230072969 + 3 ^ 40 * 748183 * 2
def baseEnd_748183 : Nat := 170745554010200650787411

theorem tailTrace_748183 : CollatzResearch.WordTrace tailWord_748183 prefixEnd_748183 170745554010200650787411 := by
  unfold tailWord_748183
  simp only [CollatzResearch.WordTrace]
  refine ⟨27288475848468245328465203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18192317232312163552310135 27288475848468245328465203)
  ·
    refine ⟨40932713772702367992697805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27288475848468245328465203 40932713772702367992697805)
    ·
      refine ⟨15349767664763387997261677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40932713772702367992697805 15349767664763387997261677)
      ·
        refine ⟨5756162874286270498973129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15349767664763387997261677 5756162874286270498973129)
        ·
          refine ⟨4317122155714702874229847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5756162874286270498973129 4317122155714702874229847)
          ·
            refine ⟨6475683233572054311344771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4317122155714702874229847 6475683233572054311344771)
            ·
              refine ⟨9713524850358081467017157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6475683233572054311344771 9713524850358081467017157)
              ·
                refine ⟨1821285909442140275065717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9713524850358081467017157 1821285909442140275065717)
                ·
                  refine ⟨170745554010200650787411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1821285909442140275065717 170745554010200650787411)
                  ·
                    rfl

theorem cell21_748183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 5].length) (baseStart_748183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_748183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_748183 prefixEnd_748183 := by exact prefixLift 748183
  have htrace : WordTrace (prefixWord ++ tailWord_748183) baseStart_748183 baseEnd_748183 := by
    simpa [prefixWord, tailWord_748183, baseEnd_748183] using wordTrace_append hprefix tailTrace_748183
  have hstable : (prefixWord ++ tailWord_748183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748183).length < 2 ^ (prefixWord ++ tailWord_748183).sum := by decide
  have hdescent : baseEnd_748183 < baseStart_748183 := by decide
  rcases family_descends (prefixWord ++ tailWord_748183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748186 : List Nat := [3, 1, 1, 6, 1, 1, 1, 7]
def baseStart_748186 : Nat := 118140960795 + 748186 * 2 ^ 59
def prefixEnd_748186 : Nat := 4983230072969 + 3 ^ 40 * 748186 * 2
def baseEnd_748186 : Nat := 56915412883691104079135

theorem tailTrace_748186 : CollatzResearch.WordTrace tailWord_748186 prefixEnd_748186 56915412883691104079135 := by
  unfold tailWord_748186
  simp only [CollatzResearch.WordTrace]
  refine ⟨6822146316864344210206103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18192390178304917893882941 6822146316864344210206103)
  ·
    refine ⟨10233219475296516315309155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6822146316864344210206103 10233219475296516315309155)
    ·
      refine ⟨15349829212944774472963733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10233219475296516315309155 15349829212944774472963733)
      ·
        refine ⟨719523244356786303420175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15349829212944774472963733 719523244356786303420175)
        ·
          refine ⟨1079284866535179455130263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719523244356786303420175 1079284866535179455130263)
          ·
            refine ⟨1618927299802769182695395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079284866535179455130263 1618927299802769182695395)
            ·
              refine ⟨2428390949704153774043093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1618927299802769182695395 2428390949704153774043093)
              ·
                refine ⟨56915412883691104079135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2428390949704153774043093 56915412883691104079135)
                ·
                  rfl

theorem cell21_748186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_748186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_748186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_748186 prefixEnd_748186 := by exact prefixLift 748186
  have htrace : WordTrace (prefixWord ++ tailWord_748186) baseStart_748186 baseEnd_748186 := by
    simpa [prefixWord, tailWord_748186, baseEnd_748186] using wordTrace_append hprefix tailTrace_748186
  have hstable : (prefixWord ++ tailWord_748186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748186).length < 2 ^ (prefixWord ++ tailWord_748186).sum := by decide
  have hdescent : baseEnd_748186 < baseStart_748186 := by decide
  rcases family_descends (prefixWord ++ tailWord_748186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748324 : List Nat := [2, 3, 1, 3, 3, 2, 1, 2, 4]
def baseStart_748324 : Nat := 118140960795 + 748324 * 2 ^ 59
def prefixEnd_748324 : Nat := 4983230072969 + 3 ^ 40 * 748324 * 2
def baseEnd_748324 : Nat := 170777732131215738937123

theorem tailTrace_748324 : CollatzResearch.WordTrace tailWord_748324 prefixEnd_748324 170777732131215738937123 := by
  unfold tailWord_748324
  simp only [CollatzResearch.WordTrace]
  refine ⟨13646809270478713204674013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18195745693971617606232017 13646809270478713204674013)
  ·
    refine ⟨5117553476429517451752755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13646809270478713204674013 5117553476429517451752755)
    ·
      refine ⟨7676330214644276177629133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5117553476429517451752755 7676330214644276177629133)
      ·
        refine ⟨2878623830491603566610925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7676330214644276177629133 2878623830491603566610925)
        ·
          refine ⟨1079483936434351337479097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2878623830491603566610925 1079483936434351337479097)
          ·
            refine ⟨809612952325763503109323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1079483936434351337479097 809612952325763503109323)
            ·
              refine ⟨1214419428488645254663985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809612952325763503109323 1214419428488645254663985)
              ·
                refine ⟨910814571366483940997989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1214419428488645254663985 910814571366483940997989)
                ·
                  refine ⟨170777732131215738937123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 910814571366483940997989 170777732131215738937123)
                  ·
                    rfl

theorem cell21_748324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_748324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_748324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_748324 prefixEnd_748324 := by exact prefixLift 748324
  have htrace : WordTrace (prefixWord ++ tailWord_748324) baseStart_748324 baseEnd_748324 := by
    simpa [prefixWord, tailWord_748324, baseEnd_748324] using wordTrace_append hprefix tailTrace_748324
  have hstable : (prefixWord ++ tailWord_748324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748324).length < 2 ^ (prefixWord ++ tailWord_748324).sum := by decide
  have hdescent : baseEnd_748324 < baseStart_748324 := by decide
  rcases family_descends (prefixWord ++ tailWord_748324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748386 : List Nat := [3, 3, 2, 1, 4, 1, 1, 1, 5]
def baseStart_748386 : Nat := 118140960795 + 748386 * 2 ^ 59
def prefixEnd_748386 : Nat := 4983230072969 + 3 ^ 40 * 748386 * 2
def baseEnd_748386 : Nat := 170791881375917408903663

theorem tailTrace_748386 : CollatzResearch.WordTrace tailWord_748386 prefixEnd_748386 170791881375917408903663 := by
  unfold tailWord_748386
  simp only [CollatzResearch.WordTrace]
  refine ⟨6823969966683202749526253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18197253244488540665403341 6823969966683202749526253)
  ·
    refine ⟨2558988737506201031072345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6823969966683202749526253 2558988737506201031072345)
    ·
      refine ⟨1919241553129650773304259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2558988737506201031072345 1919241553129650773304259)
      ·
        refine ⟨2878862329694476159956389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1919241553129650773304259 2878862329694476159956389)
        ·
          refine ⟨539786686817714279991823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2878862329694476159956389 539786686817714279991823)
          ·
            refine ⟨809680030226571419987735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 539786686817714279991823 809680030226571419987735)
            ·
              refine ⟨1214520045339857129981603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 809680030226571419987735 1214520045339857129981603)
              ·
                refine ⟨1821780068009785694972405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1214520045339857129981603 1821780068009785694972405)
                ·
                  refine ⟨170791881375917408903663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1821780068009785694972405 170791881375917408903663)
                  ·
                    rfl

theorem cell21_748386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_748386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_748386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_748386 prefixEnd_748386 := by exact prefixLift 748386
  have htrace : WordTrace (prefixWord ++ tailWord_748386) baseStart_748386 baseEnd_748386 := by
    simpa [prefixWord, tailWord_748386, baseEnd_748386] using wordTrace_append hprefix tailTrace_748386
  have hstable : (prefixWord ++ tailWord_748386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748386).length < 2 ^ (prefixWord ++ tailWord_748386).sum := by decide
  have hdescent : baseEnd_748386 < baseStart_748386 := by decide
  rcases family_descends (prefixWord ++ tailWord_748386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748473 : List Nat := [1, 2, 1, 4, 2, 3, 3, 5]
def baseStart_748473 : Nat := 118140960795 + 748473 * 2 ^ 59
def prefixEnd_748473 : Nat := 4983230072969 + 3 ^ 40 * 748473 * 2
def baseEnd_748473 : Nat := 56937245320408196984495

theorem tailTrace_748473 : CollatzResearch.WordTrace tailWord_748473 prefixEnd_748473 56937245320408196984495 := by
  unfold tailWord_748473
  simp only [CollatzResearch.WordTrace]
  refine ⟨27299053017417624856522073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18199368678278416571014715 27299053017417624856522073)
  ·
    refine ⟨20474289763063218642391555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27299053017417624856522073 20474289763063218642391555)
    ·
      refine ⟨30711434644594827963587333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20474289763063218642391555 30711434644594827963587333)
      ·
        refine ⟨5758393995861530243172625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30711434644594827963587333 5758393995861530243172625)
        ·
          refine ⟨4318795496896147682379469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5758393995861530243172625 4318795496896147682379469)
          ·
            refine ⟨1619548311336055380892301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4318795496896147682379469 1619548311336055380892301)
            ·
              refine ⟨607330616751020767834613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1619548311336055380892301 607330616751020767834613)
              ·
                refine ⟨56937245320408196984495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 607330616751020767834613 56937245320408196984495)
                ·
                  rfl

theorem cell21_748473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 5].length) (baseStart_748473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_748473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_748473 prefixEnd_748473 := by exact prefixLift 748473
  have htrace : WordTrace (prefixWord ++ tailWord_748473) baseStart_748473 baseEnd_748473 := by
    simpa [prefixWord, tailWord_748473, baseEnd_748473] using wordTrace_append hprefix tailTrace_748473
  have hstable : (prefixWord ++ tailWord_748473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748473).length < 2 ^ (prefixWord ++ tailWord_748473).sum := by decide
  have hdescent : baseEnd_748473 < baseStart_748473 := by decide
  rcases family_descends (prefixWord ++ tailWord_748473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748493 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 6]
def baseStart_748493 : Nat := 118140960795 + 748493 * 2 ^ 59
def prefixEnd_748493 : Nat := 4983230072969 + 3 ^ 40 * 748493 * 2
def baseEnd_748493 : Nat := 170816300233709000620111

theorem tailTrace_748493 : CollatzResearch.WordTrace tailWord_748493 prefixEnd_748493 170816300233709000620111 := by
  unfold tailWord_748493
  simp only [CollatzResearch.WordTrace]
  refine ⟨27299782477345168272250133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18199854984896778848166755 27299782477345168272250133)
  ·
    refine ⟨1279677303625554762761725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27299782477345168272250133 1279677303625554762761725)
    ·
      refine ⟨479878988859583036035647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1279677303625554762761725 479878988859583036035647)
      ·
        refine ⟨719818483289374554053471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479878988859583036035647 719818483289374554053471)
        ·
          refine ⟨1079727724934061831080207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719818483289374554053471 1079727724934061831080207)
          ·
            refine ⟨1619591587401092746620311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079727724934061831080207 1619591587401092746620311)
            ·
              refine ⟨2429387381101639119930467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619591587401092746620311 2429387381101639119930467)
              ·
                refine ⟨3644081071652458679895701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2429387381101639119930467 3644081071652458679895701)
                ·
                  refine ⟨170816300233709000620111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3644081071652458679895701 170816300233709000620111)
                  ·
                    rfl

theorem cell21_748493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_748493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_748493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_748493 prefixEnd_748493 := by exact prefixLift 748493
  have htrace : WordTrace (prefixWord ++ tailWord_748493) baseStart_748493 baseEnd_748493 := by
    simpa [prefixWord, tailWord_748493, baseEnd_748493] using wordTrace_append hprefix tailTrace_748493
  have hstable : (prefixWord ++ tailWord_748493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748493).length < 2 ^ (prefixWord ++ tailWord_748493).sum := by decide
  have hdescent : baseEnd_748493 < baseStart_748493 := by decide
  rcases family_descends (prefixWord ++ tailWord_748493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748504 : List Nat := [2, 1, 2, 2, 2, 3, 2, 4, 3]
def baseStart_748504 : Nat := 118140960795 + 748504 * 2 ^ 59
def prefixEnd_748504 : Nat := 4983230072969 + 3 ^ 40 * 748504 * 2
def baseEnd_748504 : Nat := 170818810583575425936755

theorem tailTrace_748504 : CollatzResearch.WordTrace tailWord_748504 prefixEnd_748504 170818810583575425936755 := by
  unfold tailWord_748504
  simp only [CollatzResearch.WordTrace]
  refine ⟨13650091840152658575450283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18200122453536878100600377 13650091840152658575450283)
  ·
    refine ⟨20475137760228987863175425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13650091840152658575450283 20475137760228987863175425)
    ·
      refine ⟨15356353320171740897381569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20475137760228987863175425 15356353320171740897381569)
      ·
        refine ⟨11517264990128805673036177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15356353320171740897381569 11517264990128805673036177)
        ·
          refine ⟨8637948742596604254777133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11517264990128805673036177 8637948742596604254777133)
          ·
            refine ⟨3239230778473726595541425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8637948742596604254777133 3239230778473726595541425)
            ·
              refine ⟨2429423083855294946656069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3239230778473726595541425 2429423083855294946656069)
              ·
                refine ⟨455516828222867802498013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2429423083855294946656069 455516828222867802498013)
                ·
                  refine ⟨170818810583575425936755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 455516828222867802498013 170818810583575425936755)
                  ·
                    rfl

theorem cell21_748504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 3].length) (baseStart_748504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_748504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_748504 prefixEnd_748504 := by exact prefixLift 748504
  have htrace : WordTrace (prefixWord ++ tailWord_748504) baseStart_748504 baseEnd_748504 := by
    simpa [prefixWord, tailWord_748504, baseEnd_748504] using wordTrace_append hprefix tailTrace_748504
  have hstable : (prefixWord ++ tailWord_748504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748504).length < 2 ^ (prefixWord ++ tailWord_748504).sum := by decide
  have hdescent : baseEnd_748504 < baseStart_748504 := by decide
  rcases family_descends (prefixWord ++ tailWord_748504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748614 : List Nat := [6, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_748614 : Nat := 118140960795 + 748614 * 2 ^ 59
def prefixEnd_748614 : Nat := 4983230072969 + 3 ^ 40 * 748614 * 2
def baseEnd_748614 : Nat := 170843914082239679103197

theorem tailTrace_748614 : CollatzResearch.WordTrace tailWord_748614 prefixEnd_748614 170843914082239679103197 := by
  unfold tailWord_748614
  simp only [CollatzResearch.WordTrace]
  refine ⟨853256115934587685543903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18202797139937870624936597 853256115934587685543903)
  ·
    refine ⟨1279884173901881528315855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 853256115934587685543903 1279884173901881528315855)
    ·
      refine ⟨1919826260852822292473783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1279884173901881528315855 1919826260852822292473783)
      ·
        refine ⟨2879739391279233438710675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1919826260852822292473783 2879739391279233438710675)
        ·
          refine ⟨4319609086918850158066013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2879739391279233438710675 4319609086918850158066013)
          ·
            refine ⟨1619853407594568809274755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4319609086918850158066013 1619853407594568809274755)
            ·
              refine ⟨2429780111391853213912133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619853407594568809274755 2429780111391853213912133)
              ·
                refine ⟨455583770885972477608525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2429780111391853213912133 455583770885972477608525)
                ·
                  refine ⟨170843914082239679103197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 455583770885972477608525 170843914082239679103197)
                  ·
                    rfl

theorem cell21_748614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_748614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_748614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_748614 prefixEnd_748614 := by exact prefixLift 748614
  have htrace : WordTrace (prefixWord ++ tailWord_748614) baseStart_748614 baseEnd_748614 := by
    simpa [prefixWord, tailWord_748614, baseEnd_748614] using wordTrace_append hprefix tailTrace_748614
  have hstable : (prefixWord ++ tailWord_748614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748614).length < 2 ^ (prefixWord ++ tailWord_748614).sum := by decide
  have hdescent : baseEnd_748614 < baseStart_748614 := by decide
  rcases family_descends (prefixWord ++ tailWord_748614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748642 : List Nat := [3, 3, 2, 2, 1, 2, 3, 5]
def baseStart_748642 : Nat := 118140960795 + 748642 * 2 ^ 59
def prefixEnd_748642 : Nat := 4983230072969 + 3 ^ 40 * 748642 * 2
def baseEnd_748642 : Nat := 56950101354572617545491

theorem tailTrace_748642 : CollatzResearch.WordTrace tailWord_748642 prefixEnd_748642 56950101354572617545491 := by
  unfold tailWord_748642
  simp only [CollatzResearch.WordTrace]
  refine ⟨6826304238451341679856045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18203477969203577812949453 6826304238451341679856045)
  ·
    refine ⟨2559864089419253129946017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6826304238451341679856045 2559864089419253129946017)
    ·
      refine ⟨1919898067064439847459513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2559864089419253129946017 1919898067064439847459513)
      ·
        refine ⟨1439923550298329885594635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1919898067064439847459513 1439923550298329885594635)
        ·
          refine ⟨2159885325447494828391953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1439923550298329885594635 2159885325447494828391953)
          ·
            refine ⟨1619913994085621121293965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2159885325447494828391953 1619913994085621121293965)
            ·
              refine ⟨607467747782107920485237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1619913994085621121293965 607467747782107920485237)
              ·
                refine ⟨56950101354572617545491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 607467747782107920485237 56950101354572617545491)
                ·
                  rfl

theorem cell21_748642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_748642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_748642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_748642 prefixEnd_748642 := by exact prefixLift 748642
  have htrace : WordTrace (prefixWord ++ tailWord_748642) baseStart_748642 baseEnd_748642 := by
    simpa [prefixWord, tailWord_748642, baseEnd_748642] using wordTrace_append hprefix tailTrace_748642
  have hstable : (prefixWord ++ tailWord_748642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748642).length < 2 ^ (prefixWord ++ tailWord_748642).sum := by decide
  have hdescent : baseEnd_748642 < baseStart_748642 := by decide
  rcases family_descends (prefixWord ++ tailWord_748642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748656 : List Nat := [2, 1, 1, 1, 5, 1, 4, 3, 3]
def baseStart_748656 : Nat := 118140960795 + 748656 * 2 ^ 59
def prefixEnd_748656 : Nat := 4983230072969 + 3 ^ 40 * 748656 * 2
def baseEnd_748656 : Nat := 170853499054456939403111

theorem tailTrace_748656 : CollatzResearch.WordTrace tailWord_748656 prefixEnd_748656 170853499054456939403111 := by
  unfold tailWord_748656
  simp only [CollatzResearch.WordTrace]
  refine ⟨13652863787877323555216911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18203818383836431406955881 13652863787877323555216911)
  ·
    refine ⟨20479295681815985332825367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13652863787877323555216911 20479295681815985332825367)
    ·
      refine ⟨30718943522723977999238051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20479295681815985332825367 30718943522723977999238051)
      ·
        refine ⟨46078415284085966998857077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30718943522723977999238051 46078415284085966998857077)
        ·
          refine ⟨4319851432883059406142851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46078415284085966998857077 4319851432883059406142851)
          ·
            refine ⟨6479777149324589109214277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4319851432883059406142851 6479777149324589109214277)
            ·
              refine ⟨1214958215498360457977677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6479777149324589109214277 1214958215498360457977677)
              ·
                refine ⟨455609330811885171741629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1214958215498360457977677 455609330811885171741629)
                ·
                  refine ⟨170853499054456939403111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 455609330811885171741629 170853499054456939403111)
                  ·
                    rfl

theorem cell21_748656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 3].length) (baseStart_748656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_748656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_748656 prefixEnd_748656 := by exact prefixLift 748656
  have htrace : WordTrace (prefixWord ++ tailWord_748656) baseStart_748656 baseEnd_748656 := by
    simpa [prefixWord, tailWord_748656, baseEnd_748656] using wordTrace_append hprefix tailTrace_748656
  have hstable : (prefixWord ++ tailWord_748656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748656).length < 2 ^ (prefixWord ++ tailWord_748656).sum := by decide
  have hdescent : baseEnd_748656 < baseStart_748656 := by decide
  rcases family_descends (prefixWord ++ tailWord_748656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748729 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 6]
def baseStart_748729 : Nat := 118140960795 + 748729 * 2 ^ 59
def prefixEnd_748729 : Nat := 4983230072969 + 3 ^ 40 * 748729 * 2
def baseEnd_748729 : Nat := 170870158649025034686295

theorem tailTrace_748729 : CollatzResearch.WordTrace tailWord_748729 prefixEnd_748729 170870158649025034686295 := by
  unfold tailWord_748729
  simp only [CollatzResearch.WordTrace]
  refine ⟨27308390104490180577841241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18205593402993453718560827 27308390104490180577841241)
  ·
    refine ⟨20481292578367635433380931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27308390104490180577841241 20481292578367635433380931)
    ·
      refine ⟨30721938867551453150071397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20481292578367635433380931 30721938867551453150071397)
      ·
        refine ⟨5760363537665897465638387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30721938867551453150071397 5760363537665897465638387)
        ·
          refine ⟨8640545306498846198457581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5760363537665897465638387 8640545306498846198457581)
          ·
            refine ⟨3240204489937067324421593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8640545306498846198457581 3240204489937067324421593)
            ·
              refine ⟨2430153367452800493316195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3240204489937067324421593 2430153367452800493316195)
              ·
                refine ⟨3645230051179200739974293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2430153367452800493316195 3645230051179200739974293)
                ·
                  refine ⟨170870158649025034686295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3645230051179200739974293 170870158649025034686295)
                  ·
                    rfl

theorem cell21_748729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_748729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_748729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_748729 prefixEnd_748729 := by exact prefixLift 748729
  have htrace : WordTrace (prefixWord ++ tailWord_748729) baseStart_748729 baseEnd_748729 := by
    simpa [prefixWord, tailWord_748729, baseEnd_748729] using wordTrace_append hprefix tailTrace_748729
  have hstable : (prefixWord ++ tailWord_748729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748729).length < 2 ^ (prefixWord ++ tailWord_748729).sum := by decide
  have hdescent : baseEnd_748729 < baseStart_748729 := by decide
  rcases family_descends (prefixWord ++ tailWord_748729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748732 : List Nat := [2, 2, 2, 3, 2, 3, 1, 1, 5]
def baseStart_748732 : Nat := 118140960795 + 748732 * 2 ^ 59
def prefixEnd_748732 : Nat := 4983230072969 + 3 ^ 40 * 748732 * 2
def baseEnd_748732 : Nat := 170870843289897696136289

theorem tailTrace_748732 : CollatzResearch.WordTrace tailWord_748732 prefixEnd_748732 170870843289897696136289 := by
  unfold tailWord_748732
  simp only [CollatzResearch.WordTrace]
  refine ⟨13654249761739656045100225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18205666348986208060133633 13654249761739656045100225)
  ·
    refine ⟨10240687321304742033825169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13654249761739656045100225 10240687321304742033825169)
    ·
      refine ⟨7680515490978556525368877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10240687321304742033825169 7680515490978556525368877)
      ·
        refine ⟨2880193309116958697013329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7680515490978556525368877 2880193309116958697013329)
        ·
          refine ⟨2160144981837719022759997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2880193309116958697013329 2160144981837719022759997)
          ·
            refine ⟨810054368189144633534999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2160144981837719022759997 810054368189144633534999)
            ·
              refine ⟨1215081552283716950302499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810054368189144633534999 1215081552283716950302499)
              ·
                refine ⟨1822622328425575425453749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215081552283716950302499 1822622328425575425453749)
                ·
                  refine ⟨170870843289897696136289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1822622328425575425453749 170870843289897696136289)
                  ·
                    rfl

theorem cell21_748732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_748732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_748732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_748732 prefixEnd_748732 := by exact prefixLift 748732
  have htrace : WordTrace (prefixWord ++ tailWord_748732) baseStart_748732 baseEnd_748732 := by
    simpa [prefixWord, tailWord_748732, baseEnd_748732] using wordTrace_append hprefix tailTrace_748732
  have hstable : (prefixWord ++ tailWord_748732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748732).length < 2 ^ (prefixWord ++ tailWord_748732).sum := by decide
  have hdescent : baseEnd_748732 < baseStart_748732 := by decide
  rcases family_descends (prefixWord ++ tailWord_748732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748738 : List Nat := [3, 5, 1, 1, 2, 2, 2, 1, 4]
def baseStart_748738 : Nat := 118140960795 + 748738 * 2 ^ 59
def prefixEnd_748738 : Nat := 4983230072969 + 3 ^ 40 * 748738 * 2
def baseEnd_748738 : Nat := 170872212571643019036277

theorem tailTrace_748738 : CollatzResearch.WordTrace tailWord_748738 prefixEnd_748738 170872212571643019036277 := by
  unfold tailWord_748738
  simp only [CollatzResearch.WordTrace]
  refine ⟨6827179590364393778729717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18205812240971716743279245 6827179590364393778729717)
  ·
    refine ⟨640048086596661916755911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6827179590364393778729717 640048086596661916755911)
    ·
      refine ⟨960072129894992875133867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 640048086596661916755911 960072129894992875133867)
      ·
        refine ⟨1440108194842489312700801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 960072129894992875133867 1440108194842489312700801)
        ·
          refine ⟨1080081146131866984525601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1440108194842489312700801 1080081146131866984525601)
          ·
            refine ⟨810060859598900238394201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1080081146131866984525601 810060859598900238394201)
            ·
              refine ⟨607545644699175178795651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 810060859598900238394201 607545644699175178795651)
              ·
                refine ⟨911318467048762768193477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607545644699175178795651 911318467048762768193477)
                ·
                  refine ⟨170872212571643019036277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 911318467048762768193477 170872212571643019036277)
                  ·
                    rfl

theorem cell21_748738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_748738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_748738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_748738 prefixEnd_748738 := by exact prefixLift 748738
  have htrace : WordTrace (prefixWord ++ tailWord_748738) baseStart_748738 baseEnd_748738 := by
    simpa [prefixWord, tailWord_748738, baseEnd_748738] using wordTrace_append hprefix tailTrace_748738
  have hstable : (prefixWord ++ tailWord_748738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748738).length < 2 ^ (prefixWord ++ tailWord_748738).sum := by decide
  have hdescent : baseEnd_748738 < baseStart_748738 := by decide
  rcases family_descends (prefixWord ++ tailWord_748738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748746 : List Nat := [3, 1, 2, 1, 3, 3, 1, 3, 4]
def baseStart_748746 : Nat := 118140960795 + 748746 * 2 ^ 59
def prefixEnd_748746 : Nat := 4983230072969 + 3 ^ 40 * 748746 * 2
def baseEnd_748746 : Nat := 170874038280636782902927

theorem tailTrace_748746 : CollatzResearch.WordTrace tailWord_748746 prefixEnd_748746 170874038280636782902927 := by
  unfold tailWord_748746
  simp only [CollatzResearch.WordTrace]
  refine ⟨6827252536357148120302523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18206006763619061654140061 6827252536357148120302523)
  ·
    refine ⟨10240878804535722180453785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6827252536357148120302523 10240878804535722180453785)
    ·
      refine ⟨7680659103401791635340339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10240878804535722180453785 7680659103401791635340339)
      ·
        refine ⟨11520988655102687453010509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7680659103401791635340339 11520988655102687453010509)
        ·
          refine ⟨4320370745663507794878941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11520988655102687453010509 4320370745663507794878941)
          ·
            refine ⟨1620139029623815423079603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4320370745663507794878941 1620139029623815423079603)
            ·
              refine ⟨2430208544435723134619405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1620139029623815423079603 2430208544435723134619405)
              ·
                refine ⟨911328204163396175482277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2430208544435723134619405 911328204163396175482277)
                ·
                  refine ⟨170874038280636782902927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 911328204163396175482277 170874038280636782902927)
                  ·
                    rfl

theorem cell21_748746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_748746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_748746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_748746 prefixEnd_748746 := by exact prefixLift 748746
  have htrace : WordTrace (prefixWord ++ tailWord_748746) baseStart_748746 baseEnd_748746 := by
    simpa [prefixWord, tailWord_748746, baseEnd_748746] using wordTrace_append hprefix tailTrace_748746
  have hstable : (prefixWord ++ tailWord_748746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748746).length < 2 ^ (prefixWord ++ tailWord_748746).sum := by decide
  have hdescent : baseEnd_748746 < baseStart_748746 := by decide
  rcases family_descends (prefixWord ++ tailWord_748746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748791 : List Nat := [1, 1, 3, 1, 1, 1, 2, 8, 3]
def baseStart_748791 : Nat := 118140960795 + 748791 * 2 ^ 59
def prefixEnd_748791 : Nat := 4983230072969 + 3 ^ 40 * 748791 * 2
def baseEnd_748791 : Nat := 170884307893726704652835

theorem tailTrace_748791 : CollatzResearch.WordTrace tailWord_748791 prefixEnd_748791 170884307893726704652835 := by
  unfold tailWord_748791
  simp only [CollatzResearch.WordTrace]
  refine ⟨27310651430265565166598227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18207100953510376777732151 27310651430265565166598227)
  ·
    refine ⟨40965977145398347749897341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27310651430265565166598227 40965977145398347749897341)
    ·
      refine ⟨15362241429524380406211503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40965977145398347749897341 15362241429524380406211503)
      ·
        refine ⟨23043362144286570609317255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15362241429524380406211503 23043362144286570609317255)
        ·
          refine ⟨34565043216429855913975883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23043362144286570609317255 34565043216429855913975883)
          ·
            refine ⟨51847564824644783870963825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34565043216429855913975883 51847564824644783870963825)
            ·
              refine ⟨38885673618483587903222869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51847564824644783870963825 38885673618483587903222869)
              ·
                refine ⟨455691487716604545740893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 38885673618483587903222869 455691487716604545740893)
                ·
                  refine ⟨170884307893726704652835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 455691487716604545740893 170884307893726704652835)
                  ·
                    rfl

theorem cell21_748791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 3].length) (baseStart_748791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_748791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_748791 prefixEnd_748791 := by exact prefixLift 748791
  have htrace : WordTrace (prefixWord ++ tailWord_748791) baseStart_748791 baseEnd_748791 := by
    simpa [prefixWord, tailWord_748791, baseEnd_748791] using wordTrace_append hprefix tailTrace_748791
  have hstable : (prefixWord ++ tailWord_748791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748791).length < 2 ^ (prefixWord ++ tailWord_748791).sum := by decide
  have hdescent : baseEnd_748791 < baseStart_748791 := by decide
  rcases family_descends (prefixWord ++ tailWord_748791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748805 : List Nat := [1, 3, 1, 1, 2, 1, 3, 5, 4]
def baseStart_748805 : Nat := 118140960795 + 748805 * 2 ^ 59
def prefixEnd_748805 : Nat := 4983230072969 + 3 ^ 40 * 748805 * 2
def baseEnd_748805 : Nat := 170887502884465791419473

theorem tailTrace_748805 : CollatzResearch.WordTrace tailWord_748805 prefixEnd_748805 170887502884465791419473 := by
  unfold tailWord_748805
  simp only [CollatzResearch.WordTrace]
  refine ⟨27311162052214845557607869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18207441368143230371738579 27311162052214845557607869)
  ·
    refine ⟨10241685769580567084102951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27311162052214845557607869 10241685769580567084102951)
    ·
      refine ⟨15362528654370850626154427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10241685769580567084102951 15362528654370850626154427)
      ·
        refine ⟨23043792981556275939231641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15362528654370850626154427 23043792981556275939231641)
        ·
          refine ⟨17282844736167206954423731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23043792981556275939231641 17282844736167206954423731)
          ·
            refine ⟨25924267104250810431635597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17282844736167206954423731 25924267104250810431635597)
            ·
              refine ⟨9721600164094053911863349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25924267104250810431635597 9721600164094053911863349)
              ·
                refine ⟨911400015383817554237189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9721600164094053911863349 911400015383817554237189)
                ·
                  refine ⟨170887502884465791419473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 911400015383817554237189 170887502884465791419473)
                  ·
                    rfl

theorem cell21_748805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_748805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_748805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_748805 prefixEnd_748805 := by exact prefixLift 748805
  have htrace : WordTrace (prefixWord ++ tailWord_748805) baseStart_748805 baseEnd_748805 := by
    simpa [prefixWord, tailWord_748805, baseEnd_748805] using wordTrace_append hprefix tailTrace_748805
  have hstable : (prefixWord ++ tailWord_748805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748805).length < 2 ^ (prefixWord ++ tailWord_748805).sum := by decide
  have hdescent : baseEnd_748805 < baseStart_748805 := by decide
  rcases family_descends (prefixWord ++ tailWord_748805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_748898 : List Nat := [3, 3, 2, 1, 1, 1, 2, 4, 4]
def baseStart_748898 : Nat := 118140960795 + 748898 * 2 ^ 59
def prefixEnd_748898 : Nat := 4983230072969 + 3 ^ 40 * 748898 * 2
def baseEnd_748898 : Nat := 170908726751518296369283

theorem tailTrace_748898 : CollatzResearch.WordTrace tailWord_748898 prefixEnd_748898 170908726751518296369283 := by
  unfold tailWord_748898
  simp only [CollatzResearch.WordTrace]
  refine ⟨6828638510219480610185837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18209702693918614960495565 6828638510219480610185837)
  ·
    refine ⟨2560739441332305228819689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6828638510219480610185837 2560739441332305228819689)
    ·
      refine ⟨1920554580999228921614767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2560739441332305228819689 1920554580999228921614767)
      ·
        refine ⟨2880831871498843382422151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1920554580999228921614767 2880831871498843382422151)
        ·
          refine ⟨4321247807248265073633227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2880831871498843382422151 4321247807248265073633227)
          ·
            refine ⟨6481871710872397610449841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4321247807248265073633227 6481871710872397610449841)
            ·
              refine ⟨4861403783154298207837381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6481871710872397610449841 4861403783154298207837381)
              ·
                refine ⟨911513209341430913969509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4861403783154298207837381 911513209341430913969509)
                ·
                  refine ⟨170908726751518296369283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 911513209341430913969509 170908726751518296369283)
                  ·
                    rfl

theorem cell21_748898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_748898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_748898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_748898 prefixEnd_748898 := by exact prefixLift 748898
  have htrace : WordTrace (prefixWord ++ tailWord_748898) baseStart_748898 baseEnd_748898 := by
    simpa [prefixWord, tailWord_748898, baseEnd_748898] using wordTrace_append hprefix tailTrace_748898
  have hstable : (prefixWord ++ tailWord_748898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_748898).length < 2 ^ (prefixWord ++ tailWord_748898).sum := by decide
  have hdescent : baseEnd_748898 < baseStart_748898 := by decide
  rcases family_descends (prefixWord ++ tailWord_748898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749185 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 6]
def baseStart_749185 : Nat := 118140960795 + 749185 * 2 ^ 59
def prefixEnd_749185 : Nat := 4983230072969 + 3 ^ 40 * 749185 * 2
def baseEnd_749185 : Nat := 170974224061669575085363

theorem tailTrace_749185 : CollatzResearch.WordTrace tailWord_749185 prefixEnd_749185 170974224061669575085363 := by
  unfold tailWord_749185
  simp only [CollatzResearch.WordTrace]
  refine ⟨27325021790838170456441009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18216681193892113637627339 27325021790838170456441009)
  ·
    refine ⟨20493766343128627842330757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27325021790838170456441009 20493766343128627842330757)
    ·
      refine ⟨3842581189336617720437017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20493766343128627842330757 3842581189336617720437017)
      ·
        refine ⟨2881935892002463290327763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3842581189336617720437017 2881935892002463290327763)
        ·
          refine ⟨4322903838003694935491645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2881935892002463290327763 4322903838003694935491645)
          ·
            refine ⟨1621088939251385600809367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4322903838003694935491645 1621088939251385600809367)
            ·
              refine ⟨2431633408877078401214051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1621088939251385600809367 2431633408877078401214051)
              ·
                refine ⟨3647450113315617601821077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2431633408877078401214051 3647450113315617601821077)
                ·
                  refine ⟨170974224061669575085363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3647450113315617601821077 170974224061669575085363)
                  ·
                    rfl

theorem cell21_749185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 6].length) (baseStart_749185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_749185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_749185 prefixEnd_749185 := by exact prefixLift 749185
  have htrace : WordTrace (prefixWord ++ tailWord_749185) baseStart_749185 baseEnd_749185 := by
    simpa [prefixWord, tailWord_749185, baseEnd_749185] using wordTrace_append hprefix tailTrace_749185
  have hstable : (prefixWord ++ tailWord_749185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749185).length < 2 ^ (prefixWord ++ tailWord_749185).sum := by decide
  have hdescent : baseEnd_749185 < baseStart_749185 := by decide
  rcases family_descends (prefixWord ++ tailWord_749185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749216 : List Nat := [2, 1, 1, 4, 3, 1, 4, 5]
def baseStart_749216 : Nat := 118140960795 + 749216 * 2 ^ 59
def prefixEnd_749216 : Nat := 4983230072969 + 3 ^ 40 * 749216 * 2
def baseEnd_749216 : Nat := 56993766228006803356211

theorem tailTrace_749216 : CollatzResearch.WordTrace tailWord_749216 prefixEnd_749216 56993766228006803356211 := by
  unfold tailWord_749216
  simp only [CollatzResearch.WordTrace]
  refine ⟨13663076226862931375409751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18217434969150575167213001 13663076226862931375409751)
  ·
    refine ⟨20494614340294397063114627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13663076226862931375409751 20494614340294397063114627)
    ·
      refine ⟨30741921510441595594671941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20494614340294397063114627 30741921510441595594671941)
      ·
        refine ⟨5764110283207799174000989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30741921510441595594671941 5764110283207799174000989)
        ·
          refine ⟨2161541356202924690250371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5764110283207799174000989 2161541356202924690250371)
          ·
            refine ⟨3242312034304387035375557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2161541356202924690250371 3242312034304387035375557)
            ·
              refine ⟨607933506432072569132917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3242312034304387035375557 607933506432072569132917)
              ·
                refine ⟨56993766228006803356211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 607933506432072569132917 56993766228006803356211)
                ·
                  rfl

theorem cell21_749216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 5].length) (baseStart_749216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_749216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_749216 prefixEnd_749216 := by exact prefixLift 749216
  have htrace : WordTrace (prefixWord ++ tailWord_749216) baseStart_749216 baseEnd_749216 := by
    simpa [prefixWord, tailWord_749216, baseEnd_749216] using wordTrace_append hprefix tailTrace_749216
  have hstable : (prefixWord ++ tailWord_749216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749216).length < 2 ^ (prefixWord ++ tailWord_749216).sum := by decide
  have hdescent : baseEnd_749216 < baseStart_749216 := by decide
  rcases family_descends (prefixWord ++ tailWord_749216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749416 : List Nat := [2, 1, 4, 2, 1, 1, 5, 2, 3]
def baseStart_749416 : Nat := 118140960795 + 749416 * 2 ^ 59
def prefixEnd_749416 : Nat := 4983230072969 + 3 ^ 40 * 749416 * 2
def baseEnd_749416 : Nat := 171026941408864506734891

theorem tailTrace_749416 : CollatzResearch.WordTrace tailWord_749416 prefixEnd_749416 171026941408864506734891 := by
  unfold tailWord_749416
  simp only [CollatzResearch.WordTrace]
  refine ⟨13666723526500648454050051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18222298035334197938733401 13666723526500648454050051)
  ·
    refine ⟨20500085289750972681075077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13666723526500648454050051 20500085289750972681075077)
    ·
      refine ⟨3843765991828307377701577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20500085289750972681075077 3843765991828307377701577)
      ·
        refine ⟨2882824493871230533276183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3843765991828307377701577 2882824493871230533276183)
        ·
          refine ⟨4324236740806845799914275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2882824493871230533276183 4324236740806845799914275)
          ·
            refine ⟨6486355111210268699871413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4324236740806845799914275 6486355111210268699871413)
            ·
              refine ⟨608095791675962690612945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6486355111210268699871413 608095791675962690612945)
              ·
                refine ⟨456071843756972017959709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 608095791675962690612945 456071843756972017959709)
                ·
                  refine ⟨171026941408864506734891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 456071843756972017959709 171026941408864506734891)
                  ·
                    rfl

theorem cell21_749416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 3].length) (baseStart_749416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_749416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_749416 prefixEnd_749416 := by exact prefixLift 749416
  have htrace : WordTrace (prefixWord ++ tailWord_749416) baseStart_749416 baseEnd_749416 := by
    simpa [prefixWord, tailWord_749416, baseEnd_749416] using wordTrace_append hprefix tailTrace_749416
  have hstable : (prefixWord ++ tailWord_749416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749416).length < 2 ^ (prefixWord ++ tailWord_749416).sum := by decide
  have hdescent : baseEnd_749416 < baseStart_749416 := by decide
  rcases family_descends (prefixWord ++ tailWord_749416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749489 : List Nat := [1, 2, 2, 4, 2, 1, 2, 3, 4]
def baseStart_749489 : Nat := 118140960795 + 749489 * 2 ^ 59
def prefixEnd_749489 : Nat := 4983230072969 + 3 ^ 40 * 749489 * 2
def baseEnd_749489 : Nat := 171043601003432602018075

theorem tailTrace_749489 : CollatzResearch.WordTrace tailWord_749489 prefixEnd_749489 171043601003432602018075 := by
  unfold tailWord_749489
  simp only [CollatzResearch.WordTrace]
  refine ⟨27336109581736830375507521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18224073054491220250338347 27336109581736830375507521)
  ·
    refine ⟨20502082186302622781630641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27336109581736830375507521 20502082186302622781630641)
    ·
      refine ⟨15376561639726967086222981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20502082186302622781630641 15376561639726967086222981)
      ·
        refine ⟨2883105307448806328666809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15376561639726967086222981 2883105307448806328666809)
        ·
          refine ⟨2162328980586604746500107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2883105307448806328666809 2162328980586604746500107)
          ·
            refine ⟨3243493470879907119750161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2162328980586604746500107 3243493470879907119750161)
            ·
              refine ⟨2432620103159930339812621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3243493470879907119750161 2432620103159930339812621)
              ·
                refine ⟨912232538684973877429733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2432620103159930339812621 912232538684973877429733)
                ·
                  refine ⟨171043601003432602018075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 912232538684973877429733 171043601003432602018075)
                  ·
                    rfl

theorem cell21_749489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 4].length) (baseStart_749489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_749489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_749489 prefixEnd_749489 := by exact prefixLift 749489
  have htrace : WordTrace (prefixWord ++ tailWord_749489) baseStart_749489 baseEnd_749489 := by
    simpa [prefixWord, tailWord_749489, baseEnd_749489] using wordTrace_append hprefix tailTrace_749489
  have hstable : (prefixWord ++ tailWord_749489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749489).length < 2 ^ (prefixWord ++ tailWord_749489).sum := by decide
  have hdescent : baseEnd_749489 < baseStart_749489 := by decide
  rcases family_descends (prefixWord ++ tailWord_749489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749492 : List Nat := [2, 5, 2, 1, 2, 1, 1, 2, 5]
def baseStart_749492 : Nat := 118140960795 + 749492 * 2 ^ 59
def prefixEnd_749492 : Nat := 4983230072969 + 3 ^ 40 * 749492 * 2
def baseEnd_749492 : Nat := 171044285644305263468069

theorem tailTrace_749492 : CollatzResearch.WordTrace tailWord_749492 prefixEnd_749492 171044285644305263468069 := by
  unfold tailWord_749492
  simp only [CollatzResearch.WordTrace]
  refine ⟨13668109500362980943933365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18224146000483974591911153 13668109500362980943933365)
  ·
    refine ⟨1281385265659029463493753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13668109500362980943933365 1281385265659029463493753)
    ·
      refine ⟨961038949244272097620315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1281385265659029463493753 961038949244272097620315)
      ·
        refine ⟨1441558423866408146430473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 961038949244272097620315 1441558423866408146430473)
        ·
          refine ⟨1081168817899806109822855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1441558423866408146430473 1081168817899806109822855)
          ·
            refine ⟨1621753226849709164734283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081168817899806109822855 1621753226849709164734283)
            ·
              refine ⟨2432629840274563747101425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1621753226849709164734283 2432629840274563747101425)
              ·
                refine ⟨1824472380205922810326069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2432629840274563747101425 1824472380205922810326069)
                ·
                  refine ⟨171044285644305263468069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1824472380205922810326069 171044285644305263468069)
                  ·
                    rfl

theorem cell21_749492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_749492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_749492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_749492 prefixEnd_749492 := by exact prefixLift 749492
  have htrace : WordTrace (prefixWord ++ tailWord_749492) baseStart_749492 baseEnd_749492 := by
    simpa [prefixWord, tailWord_749492, baseEnd_749492] using wordTrace_append hprefix tailTrace_749492
  have hstable : (prefixWord ++ tailWord_749492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749492).length < 2 ^ (prefixWord ++ tailWord_749492).sum := by decide
  have hdescent : baseEnd_749492 < baseStart_749492 := by decide
  rcases family_descends (prefixWord ++ tailWord_749492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749503 : List Nat := [1, 1, 2, 2, 2, 1, 7, 5]
def baseStart_749503 : Nat := 118140960795 + 749503 * 2 ^ 59
def prefixEnd_749503 : Nat := 4983230072969 + 3 ^ 40 * 749503 * 2
def baseEnd_749503 : Nat := 57015598664723896261571

theorem tailTrace_749503 : CollatzResearch.WordTrace tailWord_749503 prefixEnd_749503 57015598664723896261571 := by
  unfold tailWord_749503
  simp only [CollatzResearch.WordTrace]
  refine ⟨27336620203686110766517163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18224413469124073844344775 27336620203686110766517163)
  ·
    refine ⟨41004930305529166149775745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27336620203686110766517163 41004930305529166149775745)
    ·
      refine ⟨30753697729146874612331809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41004930305529166149775745 30753697729146874612331809)
      ·
        refine ⟨23065273296860155959248857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30753697729146874612331809 23065273296860155959248857)
        ·
          refine ⟨17298954972645116969436643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23065273296860155959248857 17298954972645116969436643)
          ·
            refine ⟨25948432458967675454154965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17298954972645116969436643 25948432458967675454154965)
            ·
              refine ⟨608166385757054893456757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 25948432458967675454154965 608166385757054893456757)
              ·
                refine ⟨57015598664723896261571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 608166385757054893456757 57015598664723896261571)
                ·
                  rfl

theorem cell21_749503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 5].length) (baseStart_749503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_749503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_749503 prefixEnd_749503 := by exact prefixLift 749503
  have htrace : WordTrace (prefixWord ++ tailWord_749503) baseStart_749503 baseEnd_749503 := by
    simpa [prefixWord, tailWord_749503, baseEnd_749503] using wordTrace_append hprefix tailTrace_749503
  have hstable : (prefixWord ++ tailWord_749503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749503).length < 2 ^ (prefixWord ++ tailWord_749503).sum := by decide
  have hdescent : baseEnd_749503 < baseStart_749503 := by decide
  rcases family_descends (prefixWord ++ tailWord_749503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749548 : List Nat := [2, 2, 1, 1, 2, 1, 1, 7, 4]
def baseStart_749548 : Nat := 118140960795 + 749548 * 2 ^ 59
def prefixEnd_749548 : Nat := 4983230072969 + 3 ^ 40 * 749548 * 2
def baseEnd_749548 : Nat := 171057065607261610534621

theorem tailTrace_749548 : CollatzResearch.WordTrace tailWord_749548 prefixEnd_749548 171057065607261610534621 := by
  unfold tailWord_749548
  simp only [CollatzResearch.WordTrace]
  refine ⟨13669130744261541725952649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18225507659015388967936865 13669130744261541725952649)
  ·
    refine ⟨10251848058196156294464487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13669130744261541725952649 10251848058196156294464487)
    ·
      refine ⟨15377772087294234441696731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10251848058196156294464487 15377772087294234441696731)
      ·
        refine ⟨23066658130941351662545097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15377772087294234441696731 23066658130941351662545097)
        ·
          refine ⟨17299993598206013746908823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23066658130941351662545097 17299993598206013746908823)
          ·
            refine ⟨25949990397309020620363235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17299993598206013746908823 25949990397309020620363235)
            ·
              refine ⟨38924985595963530930544853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25949990397309020620363235 38924985595963530930544853)
              ·
                refine ⟨912304349905395256184645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 38924985595963530930544853 912304349905395256184645)
                ·
                  refine ⟨171057065607261610534621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 912304349905395256184645 171057065607261610534621)
                  ·
                    rfl

theorem cell21_749548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_749548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_749548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_749548 prefixEnd_749548 := by exact prefixLift 749548
  have htrace : WordTrace (prefixWord ++ tailWord_749548) baseStart_749548 baseEnd_749548 := by
    simpa [prefixWord, tailWord_749548, baseEnd_749548] using wordTrace_append hprefix tailTrace_749548
  have hstable : (prefixWord ++ tailWord_749548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749548).length < 2 ^ (prefixWord ++ tailWord_749548).sum := by decide
  have hdescent : baseEnd_749548 < baseStart_749548 := by decide
  rcases family_descends (prefixWord ++ tailWord_749548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749669 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 7]
def baseStart_749669 : Nat := 118140960795 + 749669 * 2 ^ 59
def prefixEnd_749669 : Nat := 4983230072969 + 3 ^ 40 * 749669 * 2
def baseEnd_749669 : Nat := 171084679455792289017707

theorem tailTrace_749669 : CollatzResearch.WordTrace tailWord_749669 prefixEnd_749669 171084679455792289017707 := by
  unfold tailWord_749669
  simp only [CollatzResearch.WordTrace]
  refine ⟨27342674721084721117060061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18228449814056480744706707 27342674721084721117060061)
  ·
    refine ⟨10253503020406770418897523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27342674721084721117060061 10253503020406770418897523)
    ·
      refine ⟨15380254530610155628346285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10253503020406770418897523 15380254530610155628346285)
      ·
        refine ⟨5767595448978808360629857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15380254530610155628346285 5767595448978808360629857)
        ·
          refine ⟨4325696586734106270472393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5767595448978808360629857 4325696586734106270472393)
          ·
            refine ⟨3244272440050579702854295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4325696586734106270472393 3244272440050579702854295)
            ·
              refine ⟨4866408660075869554281443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3244272440050579702854295 4866408660075869554281443)
              ·
                refine ⟨7299612990113804331422165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4866408660075869554281443 7299612990113804331422165)
                ·
                  refine ⟨171084679455792289017707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7299612990113804331422165 171084679455792289017707)
                  ·
                    rfl

theorem cell21_749669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_749669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_749669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_749669 prefixEnd_749669 := by exact prefixLift 749669
  have htrace : WordTrace (prefixWord ++ tailWord_749669) baseStart_749669 baseEnd_749669 := by
    simpa [prefixWord, tailWord_749669, baseEnd_749669] using wordTrace_append hprefix tailTrace_749669
  have hstable : (prefixWord ++ tailWord_749669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749669).length < 2 ^ (prefixWord ++ tailWord_749669).sum := by decide
  have hdescent : baseEnd_749669 < baseStart_749669 := by decide
  rcases family_descends (prefixWord ++ tailWord_749669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749700 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 6]
def baseStart_749700 : Nat := 118140960795 + 749700 * 2 ^ 59
def prefixEnd_749700 : Nat := 4983230072969 + 3 ^ 40 * 749700 * 2
def baseEnd_749700 : Nat := 171091754078143124000977

theorem tailTrace_749700 : CollatzResearch.WordTrace tailWord_749700 prefixEnd_749700 171091754078143124000977 := by
  unfold tailWord_749700
  simp only [CollatzResearch.WordTrace]
  refine ⟨13671902691986206705719277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18229203589314942274292369 13671902691986206705719277)
  ·
    refine ⟨5126963509494827514644729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13671902691986206705719277 5126963509494827514644729)
    ·
      refine ⟨3845222632121120635983547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5126963509494827514644729 3845222632121120635983547)
      ·
        refine ⟨5767833948181680953975321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3845222632121120635983547 5767833948181680953975321)
        ·
          refine ⟨4325875461136260715481491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5767833948181680953975321 4325875461136260715481491)
          ·
            refine ⟨6488813191704391073222237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4325875461136260715481491 6488813191704391073222237)
            ·
              refine ⟨2433304946889146652458339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6488813191704391073222237 2433304946889146652458339)
              ·
                refine ⟨3649957420333719978687509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2433304946889146652458339 3649957420333719978687509)
                ·
                  refine ⟨171091754078143124000977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3649957420333719978687509 171091754078143124000977)
                  ·
                    rfl

theorem cell21_749700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_749700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_749700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_749700 prefixEnd_749700 := by exact prefixLift 749700
  have htrace : WordTrace (prefixWord ++ tailWord_749700) baseStart_749700 baseEnd_749700 := by
    simpa [prefixWord, tailWord_749700, baseEnd_749700] using wordTrace_append hprefix tailTrace_749700
  have hstable : (prefixWord ++ tailWord_749700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749700).length < 2 ^ (prefixWord ++ tailWord_749700).sum := by decide
  have hdescent : baseEnd_749700 < baseStart_749700 := by decide
  rcases family_descends (prefixWord ++ tailWord_749700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749717 : List Nat := [1, 3, 2, 1, 1, 1, 7, 1, 4]
def baseStart_749717 : Nat := 118140960795 + 749717 * 2 ^ 59
def prefixEnd_749717 : Nat := 4983230072969 + 3 ^ 40 * 749717 * 2
def baseEnd_749717 : Nat := 171095633709754872217609

theorem tailTrace_749717 : CollatzResearch.WordTrace tailWord_749717 prefixEnd_749717 171095633709754872217609 := by
  unfold tailWord_749717
  simp only [CollatzResearch.WordTrace]
  refine ⟨27344425424910825314807405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18229616949940550209871603 27344425424910825314807405)
  ·
    refine ⟨10254159534341559493052777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27344425424910825314807405 10254159534341559493052777)
    ·
      refine ⟨7690619650756169619789583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10254159534341559493052777 7690619650756169619789583)
      ·
        refine ⟨11535929476134254429684375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7690619650756169619789583 11535929476134254429684375)
        ·
          refine ⟨17303894214201381644526563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11535929476134254429684375 17303894214201381644526563)
          ·
            refine ⟨25955841321302072466789845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17303894214201381644526563 25955841321302072466789845)
            ·
              refine ⟨608340030968017323440387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 25955841321302072466789845 608340030968017323440387)
              ·
                refine ⟨912510046452025985160581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608340030968017323440387 912510046452025985160581)
                ·
                  refine ⟨171095633709754872217609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 912510046452025985160581 171095633709754872217609)
                  ·
                    rfl

theorem cell21_749717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_749717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_749717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_749717 prefixEnd_749717 := by exact prefixLift 749717
  have htrace : WordTrace (prefixWord ++ tailWord_749717) baseStart_749717 baseEnd_749717 := by
    simpa [prefixWord, tailWord_749717, baseEnd_749717] using wordTrace_append hprefix tailTrace_749717
  have hstable : (prefixWord ++ tailWord_749717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749717).length < 2 ^ (prefixWord ++ tailWord_749717).sum := by decide
  have hdescent : baseEnd_749717 < baseStart_749717 := by decide
  rcases family_descends (prefixWord ++ tailWord_749717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749855 : List Nat := [1, 1, 2, 4, 3, 2, 2, 3, 3]
def baseStart_749855 : Nat := 118140960795 + 749855 * 2 ^ 59
def prefixEnd_749855 : Nat := 4983230072969 + 3 ^ 40 * 749855 * 2
def baseEnd_749855 : Nat := 171127127189897298917327

theorem tailTrace_749855 : CollatzResearch.WordTrace tailWord_749855 prefixEnd_749855 171127127189897298917327 := by
  unfold tailWord_749855
  simp only [CollatzResearch.WordTrace]
  refine ⟨27349458698410874883331019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18232972465607249922220679 27349458698410874883331019)
  ·
    refine ⟨41024188047616312324996529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27349458698410874883331019 41024188047616312324996529)
    ·
      refine ⟨30768141035712234243747397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41024188047616312324996529 30768141035712234243747397)
      ·
        refine ⟨5769026444196043920702637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30768141035712234243747397 5769026444196043920702637)
        ·
          refine ⟨2163384916573516470263489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5769026444196043920702637 2163384916573516470263489)
          ·
            refine ⟨1622538687430137352697617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2163384916573516470263489 1622538687430137352697617)
            ·
              refine ⟨1216904015572603014523213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1622538687430137352697617 1216904015572603014523213)
              ·
                refine ⟨456339005839726130446205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1216904015572603014523213 456339005839726130446205)
                ·
                  refine ⟨171127127189897298917327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 456339005839726130446205 171127127189897298917327)
                  ·
                    rfl

theorem cell21_749855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 3].length) (baseStart_749855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_749855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_749855 prefixEnd_749855 := by exact prefixLift 749855
  have htrace : WordTrace (prefixWord ++ tailWord_749855) baseStart_749855 baseEnd_749855 := by
    simpa [prefixWord, tailWord_749855, baseEnd_749855] using wordTrace_append hprefix tailTrace_749855
  have hstable : (prefixWord ++ tailWord_749855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749855).length < 2 ^ (prefixWord ++ tailWord_749855).sum := by decide
  have hdescent : baseEnd_749855 < baseStart_749855 := by decide
  rcases family_descends (prefixWord ++ tailWord_749855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749886 : List Nat := [4, 2, 1, 2, 1, 3, 3, 1, 4]
def baseStart_749886 : Nat := 118140960795 + 749886 * 2 ^ 59
def prefixEnd_749886 : Nat := 4983230072969 + 3 ^ 40 * 749886 * 2
def baseEnd_749886 : Nat := 171134201812248133900597

theorem tailTrace_749886 : CollatzResearch.WordTrace tailWord_749886 prefixEnd_749886 171134201812248133900597 := by
  unfold tailWord_749886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3418823670162320897213689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18233726240865711451806341 3418823670162320897213689)
  ·
    refine ⟨2564117752621740672910267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3418823670162320897213689 2564117752621740672910267)
    ·
      refine ⟨3846176628932611009365401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2564117752621740672910267 3846176628932611009365401)
      ·
        refine ⟨2884632471699458257024051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3846176628932611009365401 2884632471699458257024051)
        ·
          refine ⟨4326948707549187385536077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2884632471699458257024051 4326948707549187385536077)
          ·
            refine ⟨1622605765330945269576029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4326948707549187385536077 1622605765330945269576029)
            ·
              refine ⟨608477161999104476091011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1622605765330945269576029 608477161999104476091011)
              ·
                refine ⟨912715742998656714136517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608477161999104476091011 912715742998656714136517)
                ·
                  refine ⟨171134201812248133900597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 912715742998656714136517 171134201812248133900597)
                  ·
                    rfl

theorem cell21_749886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_749886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_749886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_749886 prefixEnd_749886 := by exact prefixLift 749886
  have htrace : WordTrace (prefixWord ++ tailWord_749886) baseStart_749886 baseEnd_749886 := by
    simpa [prefixWord, tailWord_749886, baseEnd_749886] using wordTrace_append hprefix tailTrace_749886
  have hstable : (prefixWord ++ tailWord_749886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749886).length < 2 ^ (prefixWord ++ tailWord_749886).sum := by decide
  have hdescent : baseEnd_749886 < baseStart_749886 := by decide
  rcases family_descends (prefixWord ++ tailWord_749886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749911 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 8]
def baseStart_749911 : Nat := 118140960795 + 749911 * 2 ^ 59
def prefixEnd_749911 : Nat := 4983230072969 + 3 ^ 40 * 749911 * 2
def baseEnd_749911 : Nat := 171139907152853645983879

theorem tailTrace_749911 : CollatzResearch.WordTrace tailWord_749911 prefixEnd_749911 171139907152853645983879 := by
  unfold tailWord_749911
  simp only [CollatzResearch.WordTrace]
  refine ⟨27351501186207996447369587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18234334124138664298246391 27351501186207996447369587)
  ·
    refine ⟨41027251779311994671054381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27351501186207996447369587 41027251779311994671054381)
    ·
      refine ⟨15385219417241998001645393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41027251779311994671054381 15385219417241998001645393)
      ·
        refine ⟨11538914562931498501234045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15385219417241998001645393 11538914562931498501234045)
        ·
          refine ⟨4327092961099311937962767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11538914562931498501234045 4327092961099311937962767)
          ·
            refine ⟨6490639441648967906944151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4327092961099311937962767 6490639441648967906944151)
            ·
              refine ⟨9735959162473451860416227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6490639441648967906944151 9735959162473451860416227)
              ·
                refine ⟨14603938743710177790624341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9735959162473451860416227 14603938743710177790624341)
                ·
                  refine ⟨171139907152853645983879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14603938743710177790624341 171139907152853645983879)
                  ·
                    rfl

theorem cell21_749911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 8].length) (baseStart_749911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_749911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_749911 prefixEnd_749911 := by exact prefixLift 749911
  have htrace : WordTrace (prefixWord ++ tailWord_749911) baseStart_749911 baseEnd_749911 := by
    simpa [prefixWord, tailWord_749911, baseEnd_749911] using wordTrace_append hprefix tailTrace_749911
  have hstable : (prefixWord ++ tailWord_749911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749911).length < 2 ^ (prefixWord ++ tailWord_749911).sum := by decide
  have hdescent : baseEnd_749911 < baseStart_749911 := by decide
  rcases family_descends (prefixWord ++ tailWord_749911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_749928 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 6]
def baseStart_749928 : Nat := 118140960795 + 749928 * 2 ^ 59
def prefixEnd_749928 : Nat := 4983230072969 + 3 ^ 40 * 749928 * 2
def baseEnd_749928 : Nat := 171143786784465394200511

theorem tailTrace_749928 : CollatzResearch.WordTrace tailWord_749928 prefixEnd_749928 171143786784465394200511 := by
  unfold tailWord_749928
  simp only [CollatzResearch.WordTrace]
  refine ⟨13676060613573204175369219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18234747484764272233825625 13676060613573204175369219)
  ·
    refine ⟨20514090920359806263053829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13676060613573204175369219 20514090920359806263053829)
    ·
      refine ⟨3846392047567463674322593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20514090920359806263053829 3846392047567463674322593)
      ·
        refine ⟨2884794035675597755741945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3846392047567463674322593 2884794035675597755741945)
        ·
          refine ⟨2163595526756698316806459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2884794035675597755741945 2163595526756698316806459)
          ·
            refine ⟨3245393290135047475209689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2163595526756698316806459 3245393290135047475209689)
            ·
              refine ⟨2434044967601285606407267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3245393290135047475209689 2434044967601285606407267)
              ·
                refine ⟨3651067451401928409610901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2434044967601285606407267 3651067451401928409610901)
                ·
                  refine ⟨171143786784465394200511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3651067451401928409610901 171143786784465394200511)
                  ·
                    rfl

theorem cell21_749928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_749928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_749928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_749928 prefixEnd_749928 := by exact prefixLift 749928
  have htrace : WordTrace (prefixWord ++ tailWord_749928) baseStart_749928 baseEnd_749928 := by
    simpa [prefixWord, tailWord_749928, baseEnd_749928] using wordTrace_append hprefix tailTrace_749928
  have hstable : (prefixWord ++ tailWord_749928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_749928).length < 2 ^ (prefixWord ++ tailWord_749928).sum := by decide
  have hdescent : baseEnd_749928 < baseStart_749928 := by decide
  rcases family_descends (prefixWord ++ tailWord_749928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750049 : List Nat := [1, 2, 3, 1, 2, 2, 4, 1, 5]
def baseStart_750049 : Nat := 118140960795 + 750049 * 2 ^ 59
def prefixEnd_750049 : Nat := 4983230072969 + 3 ^ 40 * 750049 * 2
def baseEnd_750049 : Nat := 171171400632996072683597

theorem tailTrace_750049 : CollatzResearch.WordTrace tailWord_750049 prefixEnd_750049 171171400632996072683597 := by
  unfold tailWord_750049
  simp only [CollatzResearch.WordTrace]
  refine ⟨27356534459708046015893201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18237689639805364010595467 27356534459708046015893201)
  ·
    refine ⟨20517400844781034511919901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27356534459708046015893201 20517400844781034511919901)
    ·
      refine ⟨7694025316792887941969963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20517400844781034511919901 7694025316792887941969963)
      ·
        refine ⟨11541037975189331912954945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7694025316792887941969963 11541037975189331912954945)
        ·
          refine ⟨8655778481391998934716209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11541037975189331912954945 8655778481391998934716209)
          ·
            refine ⟨6491833861043999201037157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8655778481391998934716209 6491833861043999201037157)
            ·
              refine ⟨1217218848945749850194467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6491833861043999201037157 1217218848945749850194467)
              ·
                refine ⟨1825828273418624775291701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1217218848945749850194467 1825828273418624775291701)
                ·
                  refine ⟨171171400632996072683597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1825828273418624775291701 171171400632996072683597)
                  ·
                    rfl

theorem cell21_750049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 5].length) (baseStart_750049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_750049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_750049 prefixEnd_750049 := by exact prefixLift 750049
  have htrace : WordTrace (prefixWord ++ tailWord_750049) baseStart_750049 baseEnd_750049 := by
    simpa [prefixWord, tailWord_750049, baseEnd_750049] using wordTrace_append hprefix tailTrace_750049
  have hstable : (prefixWord ++ tailWord_750049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750049).length < 2 ^ (prefixWord ++ tailWord_750049).sum := by decide
  have hdescent : baseEnd_750049 < baseStart_750049 := by decide
  rcases family_descends (prefixWord ++ tailWord_750049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750069 : List Nat := [1, 3, 5, 1, 2, 2, 2, 5]
def baseStart_750069 : Nat := 118140960795 + 750069 * 2 ^ 59
def prefixEnd_750069 : Nat := 4983230072969 + 3 ^ 40 * 750069 * 2
def baseEnd_750069 : Nat := 57058654968493494116741

theorem tailTrace_750069 : CollatzResearch.WordTrace tailWord_750069 prefixEnd_750069 57058654968493494116741 := by
  unfold tailWord_750069
  simp only [CollatzResearch.WordTrace]
  refine ⟨27357263919635589431621261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18238175946423726287747507 27357263919635589431621261)
  ·
    refine ⟨10258973969863346036857973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27357263919635589431621261 10258973969863346036857973)
    ·
      refine ⟨961778809674688690955435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10258973969863346036857973 961778809674688690955435)
      ·
        refine ⟨1442668214512033036433153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 961778809674688690955435 1442668214512033036433153)
        ·
          refine ⟨1082001160884024777324865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1442668214512033036433153 1082001160884024777324865)
          ·
            refine ⟨811500870663018582993649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1082001160884024777324865 811500870663018582993649)
            ·
              refine ⟨608625652997263937245237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 811500870663018582993649 608625652997263937245237)
              ·
                refine ⟨57058654968493494116741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 608625652997263937245237 57058654968493494116741)
                ·
                  rfl

theorem cell21_750069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 5].length) (baseStart_750069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_750069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_750069 prefixEnd_750069 := by exact prefixLift 750069
  have htrace : WordTrace (prefixWord ++ tailWord_750069) baseStart_750069 baseEnd_750069 := by
    simpa [prefixWord, tailWord_750069, baseEnd_750069] using wordTrace_append hprefix tailTrace_750069
  have hstable : (prefixWord ++ tailWord_750069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750069).length < 2 ^ (prefixWord ++ tailWord_750069).sum := by decide
  have hdescent : baseEnd_750069 < baseStart_750069 := by decide
  rcases family_descends (prefixWord ++ tailWord_750069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750094 : List Nat := [4, 1, 1, 2, 3, 1, 9]
def baseStart_750094 : Nat := 118140960795 + 750094 * 2 ^ 59
def prefixEnd_750094 : Nat := 4983230072969 + 3 ^ 40 * 750094 * 2
def baseEnd_750094 : Nat := 19020185582898443825945

theorem tailTrace_750094 : CollatzResearch.WordTrace tailWord_750094 prefixEnd_750094 19020185582898443825945 := by
  unfold tailWord_750094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3419771968068127337660167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18238783829696679134187557 3419771968068127337660167)
  ·
    refine ⟨5129657952102191006490251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3419771968068127337660167 5129657952102191006490251)
    ·
      refine ⟨7694486928153286509735377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5129657952102191006490251 7694486928153286509735377)
      ·
        refine ⟨5770865196114964882301533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7694486928153286509735377 5770865196114964882301533)
        ·
          refine ⟨2164074448543111830863075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5770865196114964882301533 2164074448543111830863075)
          ·
            refine ⟨3246111672814667746294613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2164074448543111830863075 3246111672814667746294613)
            ·
              refine ⟨19020185582898443825945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3246111672814667746294613 19020185582898443825945)
              ·
                rfl

theorem cell21_750094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 9].length) (baseStart_750094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_750094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_750094 prefixEnd_750094 := by exact prefixLift 750094
  have htrace : WordTrace (prefixWord ++ tailWord_750094) baseStart_750094 baseEnd_750094 := by
    simpa [prefixWord, tailWord_750094, baseEnd_750094] using wordTrace_append hprefix tailTrace_750094
  have hstable : (prefixWord ++ tailWord_750094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750094).length < 2 ^ (prefixWord ++ tailWord_750094).sum := by decide
  have hdescent : baseEnd_750094 < baseStart_750094 := by decide
  rcases family_descends (prefixWord ++ tailWord_750094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750156 : List Nat := [2, 2, 1, 3, 1, 2, 4, 2, 4]
def baseStart_750156 : Nat := 118140960795 + 750156 * 2 ^ 59
def prefixEnd_750156 : Nat := 4983230072969 + 3 ^ 40 * 750156 * 2
def baseEnd_750156 : Nat := 171195819490787664400045

theorem tailTrace_750156 : CollatzResearch.WordTrace tailWord_750156 prefixEnd_750156 171195819490787664400045 := by
  unfold tailWord_750156
  simp only [CollatzResearch.WordTrace]
  refine ⟨13680218535160201645019161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18240291380213602193358881 13680218535160201645019161)
  ·
    refine ⟨10260163901370151233764371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13680218535160201645019161 10260163901370151233764371)
    ·
      refine ⟨15390245852055226850646557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10260163901370151233764371 15390245852055226850646557)
      ·
        refine ⟨5771342194520710068992459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15390245852055226850646557 5771342194520710068992459)
        ·
          refine ⟨8657013291781065103488689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5771342194520710068992459 8657013291781065103488689)
          ·
            refine ⟨6492759968835798827616517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8657013291781065103488689 6492759968835798827616517)
            ·
              refine ⟨1217392494156712280178097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6492759968835798827616517 1217392494156712280178097)
              ·
                refine ⟨913044370617534210133573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1217392494156712280178097 913044370617534210133573)
                ·
                  refine ⟨171195819490787664400045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 913044370617534210133573 171195819490787664400045)
                  ·
                    rfl

theorem cell21_750156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_750156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_750156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_750156 prefixEnd_750156 := by exact prefixLift 750156
  have htrace : WordTrace (prefixWord ++ tailWord_750156) baseStart_750156 baseEnd_750156 := by
    simpa [prefixWord, tailWord_750156, baseEnd_750156] using wordTrace_append hprefix tailTrace_750156
  have hstable : (prefixWord ++ tailWord_750156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750156).length < 2 ^ (prefixWord ++ tailWord_750156).sum := by decide
  have hdescent : baseEnd_750156 < baseStart_750156 := by decide
  rcases family_descends (prefixWord ++ tailWord_750156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750215 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 6]
def baseStart_750215 : Nat := 118140960795 + 750215 * 2 ^ 59
def prefixEnd_750215 : Nat := 4983230072969 + 3 ^ 40 * 750215 * 2
def baseEnd_750215 : Nat := 171209284094616672916591

theorem tailTrace_750215 : CollatzResearch.WordTrace tailWord_750215 prefixEnd_750215 171209284094616672916591 := by
  unfold tailWord_750215
  simp only [CollatzResearch.WordTrace]
  refine ⟨27362588977106656366436099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18241725984737770910957399 27362588977106656366436099)
  ·
    refine ⟨41043883465659984549654149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27362588977106656366436099 41043883465659984549654149)
    ·
      refine ⟨7695728149811247103060153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41043883465659984549654149 7695728149811247103060153)
      ·
        refine ⟨5771796112358435327295115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7695728149811247103060153 5771796112358435327295115)
        ·
          refine ⟨8657694168537652990942673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5771796112358435327295115 8657694168537652990942673)
          ·
            refine ⟨6493270626403239743207005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8657694168537652990942673 6493270626403239743207005)
            ·
              refine ⟨2434976484901214903702627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6493270626403239743207005 2434976484901214903702627)
              ·
                refine ⟨3652464727351822355553941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2434976484901214903702627 3652464727351822355553941)
                ·
                  refine ⟨171209284094616672916591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3652464727351822355553941 171209284094616672916591)
                  ·
                    rfl

theorem cell21_750215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 6].length) (baseStart_750215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_750215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_750215 prefixEnd_750215 := by exact prefixLift 750215
  have htrace : WordTrace (prefixWord ++ tailWord_750215) baseStart_750215 baseEnd_750215 := by
    simpa [prefixWord, tailWord_750215, baseEnd_750215] using wordTrace_append hprefix tailTrace_750215
  have hstable : (prefixWord ++ tailWord_750215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750215).length < 2 ^ (prefixWord ++ tailWord_750215).sum := by decide
  have hdescent : baseEnd_750215 < baseStart_750215 := by decide
  rcases family_descends (prefixWord ++ tailWord_750215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750218 : List Nat := [3, 1, 2, 3, 3, 1, 2, 1, 5]
def baseStart_750218 : Nat := 118140960795 + 750218 * 2 ^ 59
def prefixEnd_750218 : Nat := 4983230072969 + 3 ^ 40 * 750218 * 2
def baseEnd_750218 : Nat := 171209968735489334366585

theorem tailTrace_750218 : CollatzResearch.WordTrace tailWord_750218 prefixEnd_750218 171209968735489334366585 := by
  unfold tailWord_750218
  simp only [CollatzResearch.WordTrace]
  refine ⟨6840674599023946969698827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18241798930730525252530205 6840674599023946969698827)
  ·
    refine ⟨10261011898535920454548241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6840674599023946969698827 10261011898535920454548241)
    ·
      refine ⟨7695758923901940340911181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10261011898535920454548241 7695758923901940340911181)
      ·
        refine ⟨2885909596463227627841693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7695758923901940340911181 2885909596463227627841693)
        ·
          refine ⟨1082216098673710360440635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2885909596463227627841693 1082216098673710360440635)
          ·
            refine ⟨1623324148010565540660953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082216098673710360440635 1623324148010565540660953)
            ·
              refine ⟨1217493111007924155495715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1623324148010565540660953 1217493111007924155495715)
              ·
                refine ⟨1826239666511886233243573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1217493111007924155495715 1826239666511886233243573)
                ·
                  refine ⟨171209968735489334366585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1826239666511886233243573 171209968735489334366585)
                  ·
                    rfl

theorem cell21_750218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_750218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_750218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_750218 prefixEnd_750218 := by exact prefixLift 750218
  have htrace : WordTrace (prefixWord ++ tailWord_750218) baseStart_750218 baseEnd_750218 := by
    simpa [prefixWord, tailWord_750218, baseEnd_750218] using wordTrace_append hprefix tailTrace_750218
  have hstable : (prefixWord ++ tailWord_750218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750218).length < 2 ^ (prefixWord ++ tailWord_750218).sum := by decide
  have hdescent : baseEnd_750218 < baseStart_750218 := by decide
  rcases family_descends (prefixWord ++ tailWord_750218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750263 : List Nat := [1, 1, 3, 1, 7, 1, 7]
def baseStart_750263 : Nat := 118140960795 + 750263 * 2 ^ 59
def prefixEnd_750263 : Nat := 4983230072969 + 3 ^ 40 * 750263 * 2
def baseEnd_750263 : Nat := 19024470927619917346277

theorem tailTrace_750263 : CollatzResearch.WordTrace tailWord_750263 prefixEnd_750263 19024470927619917346277 := by
  unfold tailWord_750263
  simp only [CollatzResearch.WordTrace]
  refine ⟨27364339680932760564183443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18242893120621840376122295 27364339680932760564183443)
  ·
    refine ⟨41046509521399140846275165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27364339680932760564183443 41046509521399140846275165)
    ·
      refine ⟨15392441070524677817353187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41046509521399140846275165 15392441070524677817353187)
      ·
        refine ⟨23088661605787016726029781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15392441070524677817353187 23088661605787016726029781)
        ·
          refine ⟨541140506385633204516323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 23088661605787016726029781 541140506385633204516323)
          ·
            refine ⟨811710759578449806774485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541140506385633204516323 811710759578449806774485)
            ·
              refine ⟨19024470927619917346277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 811710759578449806774485 19024470927619917346277)
              ·
                rfl

theorem cell21_750263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 7].length) (baseStart_750263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_750263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_750263 prefixEnd_750263 := by exact prefixLift 750263
  have htrace : WordTrace (prefixWord ++ tailWord_750263) baseStart_750263 baseEnd_750263 := by
    simpa [prefixWord, tailWord_750263, baseEnd_750263] using wordTrace_append hprefix tailTrace_750263
  have hstable : (prefixWord ++ tailWord_750263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750263).length < 2 ^ (prefixWord ++ tailWord_750263).sum := by decide
  have hdescent : baseEnd_750263 < baseStart_750263 := by decide
  rcases family_descends (prefixWord ++ tailWord_750263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750370 : List Nat := [3, 3, 1, 1, 2, 2, 1, 5, 3]
def baseStart_750370 : Nat := 118140960795 + 750370 * 2 ^ 59
def prefixEnd_750370 : Nat := 4983230072969 + 3 ^ 40 * 750370 * 2
def baseEnd_750370 : Nat := 171244657206370847832941

theorem tailTrace_750370 : CollatzResearch.WordTrace tailWord_750370 prefixEnd_750370 171244657206370847832941 := by
  unfold tailWord_750370
  simp only [CollatzResearch.WordTrace]
  refine ⟨6842060572886279459582141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18245494861030078558885709 6842060572886279459582141)
  ·
    refine ⟨2565772714832354797343303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6842060572886279459582141 2565772714832354797343303)
    ·
      refine ⟨3848659072248532196014955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2565772714832354797343303 3848659072248532196014955)
      ·
        refine ⟨5772988608372798294022433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3848659072248532196014955 5772988608372798294022433)
        ·
          refine ⟨4329741456279598720516825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5772988608372798294022433 4329741456279598720516825)
          ·
            refine ⟨3247306092209699040387619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4329741456279598720516825 3247306092209699040387619)
            ·
              refine ⟨4870959138314548560581429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3247306092209699040387619 4870959138314548560581429)
              ·
                refine ⟨456652419216988927554509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4870959138314548560581429 456652419216988927554509)
                ·
                  refine ⟨171244657206370847832941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 456652419216988927554509 171244657206370847832941)
                  ·
                    rfl

theorem cell21_750370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_750370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_750370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_750370 prefixEnd_750370 := by exact prefixLift 750370
  have htrace : WordTrace (prefixWord ++ tailWord_750370) baseStart_750370 baseEnd_750370 := by
    simpa [prefixWord, tailWord_750370, baseEnd_750370] using wordTrace_append hprefix tailTrace_750370
  have hstable : (prefixWord ++ tailWord_750370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750370).length < 2 ^ (prefixWord ++ tailWord_750370).sum := by decide
  have hdescent : baseEnd_750370 < baseStart_750370 := by decide
  rcases family_descends (prefixWord ++ tailWord_750370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750457 : List Nat := [1, 2, 1, 3, 2, 3, 1, 8]
def baseStart_750457 : Nat := 118140960795 + 750457 * 2 ^ 59
def prefixEnd_750457 : Nat := 4983230072969 + 3 ^ 40 * 750457 * 2
def baseEnd_750457 : Nat := 57088170597226009960921

theorem tailTrace_750457 : CollatzResearch.WordTrace tailWord_750457 prefixEnd_750457 57088170597226009960921 := by
  unfold tailWord_750457
  simp only [CollatzResearch.WordTrace]
  refine ⟨27371415442229931696745625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18247610294819954464497083 27371415442229931696745625)
  ·
    refine ⟨20528561581672448772559219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27371415442229931696745625 20528561581672448772559219)
    ·
      refine ⟨30792842372508673158838829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20528561581672448772559219 30792842372508673158838829)
      ·
        refine ⟨11547315889690752434564561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30792842372508673158838829 11547315889690752434564561)
        ·
          refine ⟨8660486917268064325923421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11547315889690752434564561 8660486917268064325923421)
          ·
            refine ⟨3247682593975524122221283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8660486917268064325923421 3247682593975524122221283)
            ·
              refine ⟨4871523890963286183331925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3247682593975524122221283 4871523890963286183331925)
              ·
                refine ⟨57088170597226009960921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4871523890963286183331925 57088170597226009960921)
                ·
                  rfl

theorem cell21_750457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 8].length) (baseStart_750457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_750457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_750457 prefixEnd_750457 := by exact prefixLift 750457
  have htrace : WordTrace (prefixWord ++ tailWord_750457) baseStart_750457 baseEnd_750457 := by
    simpa [prefixWord, tailWord_750457, baseEnd_750457] using wordTrace_append hprefix tailTrace_750457
  have hstable : (prefixWord ++ tailWord_750457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750457).length < 2 ^ (prefixWord ++ tailWord_750457).sum := by decide
  have hdescent : baseEnd_750457 < baseStart_750457 := by decide
  rcases family_descends (prefixWord ++ tailWord_750457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_750474 : List Nat := [3, 1, 2, 4, 1, 1, 2, 7]
def baseStart_750474 : Nat := 118140960795 + 750474 * 2 ^ 59
def prefixEnd_750474 : Nat := 4983230072969 + 3 ^ 40 * 750474 * 2
def baseEnd_750474 : Nat := 57089463807763259366465

theorem tailTrace_750474 : CollatzResearch.WordTrace tailWord_750474 prefixEnd_750474 57089463807763259366465 := by
  unfold tailWord_750474
  simp only [CollatzResearch.WordTrace]
  refine ⟨6843008870792085900028619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18248023655445562400076317 6843008870792085900028619)
  ·
    refine ⟨10264513306188128850042929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6843008870792085900028619 10264513306188128850042929)
    ·
      refine ⟨7698384979641096637532197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10264513306188128850042929 7698384979641096637532197)
      ·
        refine ⟨1443447183682705619537287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7698384979641096637532197 1443447183682705619537287)
        ·
          refine ⟨2165170775524058429305931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1443447183682705619537287 2165170775524058429305931)
          ·
            refine ⟨3247756163286087643958897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2165170775524058429305931 3247756163286087643958897)
            ·
              refine ⟨2435817122464565732969173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3247756163286087643958897 2435817122464565732969173)
              ·
                refine ⟨57089463807763259366465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2435817122464565732969173 57089463807763259366465)
                ·
                  rfl

theorem cell21_750474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_750474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_750474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_750474 prefixEnd_750474 := by exact prefixLift 750474
  have htrace : WordTrace (prefixWord ++ tailWord_750474) baseStart_750474 baseEnd_750474 := by
    simpa [prefixWord, tailWord_750474, baseEnd_750474] using wordTrace_append hprefix tailTrace_750474
  have hstable : (prefixWord ++ tailWord_750474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_750474).length < 2 ^ (prefixWord ++ tailWord_750474).sum := by decide
  have hdescent : baseEnd_750474 < baseStart_750474 := by decide
  rcases family_descends (prefixWord ++ tailWord_750474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
