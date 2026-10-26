import V185TrunkScan19Chunk023

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_240095 : List Nat := [1, 1, 2, 3, 3, 9]
def baseStart_240095 : Nat := 118140960795 + 240095 * 2 ^ 59
def prefixEnd_240095 : Nat := 4983230072969 + 3 ^ 40 * 240095 * 2
def baseEnd_240095 : Nat := 8117474089964994956927

theorem tailTrace_240095 : CollatzResearch.WordTrace tailWord_240095 prefixEnd_240095 8117474089964994956927 := by
  unfold tailWord_240095
  simp only [CollatzResearch.WordTrace]
  refine ⟨8756984065184294806537739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5837989376789529871025159 8756984065184294806537739)
  ·
    refine ⟨13135476097776442209806609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8756984065184294806537739 13135476097776442209806609)
    ·
      refine ⟨9851607073332331657354957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13135476097776442209806609 9851607073332331657354957)
      ·
        refine ⟨3694352652499624371508109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9851607073332331657354957 3694352652499624371508109)
        ·
          refine ⟨1385382244687359139315541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3694352652499624371508109 1385382244687359139315541)
          ·
            refine ⟨8117474089964994956927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1385382244687359139315541 8117474089964994956927)
            ·
              rfl

theorem cell19_240095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 9].length) (baseStart_240095 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240095 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240095 prefixEnd_240095 := by exact prefixLift 240095
  have htrace : WordTrace (prefixWord ++ tailWord_240095) baseStart_240095 baseEnd_240095 := by
    simpa [prefixWord, tailWord_240095, baseEnd_240095] using wordTrace_append hprefix tailTrace_240095
  have hstable : (prefixWord ++ tailWord_240095).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240095).length < 2 ^ (prefixWord ++ tailWord_240095).sum := by decide
  have hdescent : baseEnd_240095 < baseStart_240095 := by decide
  rcases family_descends (prefixWord ++ tailWord_240095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240110 : List Nat := [4, 1, 2, 1, 2, 4, 1, 4]
def baseStart_240110 : Nat := 118140960795 + 240110 * 2 ^ 59
def prefixEnd_240110 : Nat := 4983230072969 + 3 ^ 40 * 240110 * 2
def baseEnd_240110 : Nat := 73061831082169364278969

theorem tailTrace_240110 : CollatzResearch.WordTrace tailWord_240110 prefixEnd_240110 73061831082169364278969 := by
  unfold tailWord_240110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1094691395016244046041723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5838354106753301578889189 1094691395016244046041723)
  ·
    refine ⟨1642037092524366069062585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1094691395016244046041723 1642037092524366069062585)
    ·
      refine ⟨1231527819393274551796939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1642037092524366069062585 1231527819393274551796939)
      ·
        refine ⟨1847291729089911827695409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1231527819393274551796939 1847291729089911827695409)
        ·
          refine ⟨1385468796817433870771557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1847291729089911827695409 1385468796817433870771557)
          ·
            refine ⟨259775399403268850769667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1385468796817433870771557 259775399403268850769667)
            ·
              refine ⟨389663099104903276154501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259775399403268850769667 389663099104903276154501)
              ·
                refine ⟨73061831082169364278969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 389663099104903276154501 73061831082169364278969)
                ·
                  rfl

theorem cell19_240110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_240110 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240110 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240110 prefixEnd_240110 := by exact prefixLift 240110
  have htrace : WordTrace (prefixWord ++ tailWord_240110) baseStart_240110 baseEnd_240110 := by
    simpa [prefixWord, tailWord_240110, baseEnd_240110] using wordTrace_append hprefix tailTrace_240110
  have hstable : (prefixWord ++ tailWord_240110).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240110).length < 2 ^ (prefixWord ++ tailWord_240110).sum := by decide
  have hdescent : baseEnd_240110 < baseStart_240110 := by decide
  rcases family_descends (prefixWord ++ tailWord_240110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240129 : List Nat := [1, 2, 4, 1, 3, 2, 3, 3]
def baseStart_240129 : Nat := 118140960795 + 240129 * 2 ^ 59
def prefixEnd_240129 : Nat := 4983230072969 + 3 ^ 40 * 240129 * 2
def baseEnd_240129 : Nat := 73067612493982949856695

theorem tailTrace_240129 : CollatzResearch.WordTrace tailWord_240129 prefixEnd_240129 73067612493982949856695 := by
  unfold tailWord_240129
  simp only [CollatzResearch.WordTrace]
  refine ⟨8758224147061118613275441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5838816098040745742183627 8758224147061118613275441)
  ·
    refine ⟨6568668110295838959956581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8758224147061118613275441 6568668110295838959956581)
    ·
      refine ⟨1231625270680469804991859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6568668110295838959956581 1231625270680469804991859)
      ·
        refine ⟨1847437906020704707487789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1231625270680469804991859 1847437906020704707487789)
        ·
          refine ⟨692789214757764265307921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1847437906020704707487789 692789214757764265307921)
          ·
            refine ⟨519591911068323198980941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692789214757764265307921 519591911068323198980941)
            ·
              refine ⟨194846966650621199617853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 519591911068323198980941 194846966650621199617853)
              ·
                refine ⟨73067612493982949856695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194846966650621199617853 73067612493982949856695)
                ·
                  rfl

theorem cell19_240129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 3].length) (baseStart_240129 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240129 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240129 prefixEnd_240129 := by exact prefixLift 240129
  have htrace : WordTrace (prefixWord ++ tailWord_240129) baseStart_240129 baseEnd_240129 := by
    simpa [prefixWord, tailWord_240129, baseEnd_240129] using wordTrace_append hprefix tailTrace_240129
  have hstable : (prefixWord ++ tailWord_240129).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240129).length < 2 ^ (prefixWord ++ tailWord_240129).sum := by decide
  have hdescent : baseEnd_240129 < baseStart_240129 := by decide
  rcases family_descends (prefixWord ++ tailWord_240129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240131 : List Nat := [1, 1, 1, 3, 2, 1, 7, 3]
def baseStart_240131 : Nat := 118140960795 + 240131 * 2 ^ 59
def prefixEnd_240131 : Nat := 4983230072969 + 3 ^ 40 * 240131 * 2
def baseEnd_240131 : Nat := 73068221063647537812245

theorem tailTrace_240131 : CollatzResearch.WordTrace tailWord_240131 prefixEnd_240131 73068221063647537812245 := by
  unfold tailWord_240131
  simp only [CollatzResearch.WordTrace]
  refine ⟨8758297093053872954848247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5838864728702581969898831 8758297093053872954848247)
  ·
    refine ⟨13137445639580809432272371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8758297093053872954848247 13137445639580809432272371)
    ·
      refine ⟨19706168459371214148408557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13137445639580809432272371 19706168459371214148408557)
      ·
        refine ⟨7389813172264205305653209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19706168459371214148408557 7389813172264205305653209)
        ·
          refine ⟨5542359879198153979239907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7389813172264205305653209 5542359879198153979239907)
          ·
            refine ⟨8313539818797230968859861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5542359879198153979239907 8313539818797230968859861)
            ·
              refine ⟨194848589503060100832653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 8313539818797230968859861 194848589503060100832653)
              ·
                refine ⟨73068221063647537812245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194848589503060100832653 73068221063647537812245)
                ·
                  rfl

theorem cell19_240131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 3].length) (baseStart_240131 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240131 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240131 prefixEnd_240131 := by exact prefixLift 240131
  have htrace : WordTrace (prefixWord ++ tailWord_240131) baseStart_240131 baseEnd_240131 := by
    simpa [prefixWord, tailWord_240131, baseEnd_240131] using wordTrace_append hprefix tailTrace_240131
  have hstable : (prefixWord ++ tailWord_240131).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240131).length < 2 ^ (prefixWord ++ tailWord_240131).sum := by decide
  have hdescent : baseEnd_240131 < baseStart_240131 := by decide
  rcases family_descends (prefixWord ++ tailWord_240131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240133 : List Nat := [1, 3, 1, 1, 2, 2, 2, 7]
def baseStart_240133 : Nat := 118140960795 + 240133 * 2 ^ 59
def prefixEnd_240133 : Nat := 4983230072969 + 3 ^ 40 * 240133 * 2
def baseEnd_240133 : Nat := 73068829633312125767795

theorem tailTrace_240133 : CollatzResearch.WordTrace tailWord_240133 prefixEnd_240133 73068829633312125767795 := by
  unfold tailWord_240133
  simp only [CollatzResearch.WordTrace]
  refine ⟨8758370039046627296421053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5838913359364418197614035 8758370039046627296421053)
  ·
    refine ⟨3284388764642485236157895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8758370039046627296421053 3284388764642485236157895)
    ·
      refine ⟨4926583146963727854236843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3284388764642485236157895 4926583146963727854236843)
      ·
        refine ⟨7389874720445591781355265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4926583146963727854236843 7389874720445591781355265)
        ·
          refine ⟨5542406040334193836016449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7389874720445591781355265 5542406040334193836016449)
          ·
            refine ⟨4156804530250645377012337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5542406040334193836016449 4156804530250645377012337)
            ·
              refine ⟨3117603397687984032759253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4156804530250645377012337 3117603397687984032759253)
              ·
                refine ⟨73068829633312125767795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3117603397687984032759253 73068829633312125767795)
                ·
                  rfl

theorem cell19_240133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_240133 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240133 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240133 prefixEnd_240133 := by exact prefixLift 240133
  have htrace : WordTrace (prefixWord ++ tailWord_240133) baseStart_240133 baseEnd_240133 := by
    simpa [prefixWord, tailWord_240133, baseEnd_240133] using wordTrace_append hprefix tailTrace_240133
  have hstable : (prefixWord ++ tailWord_240133).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240133).length < 2 ^ (prefixWord ++ tailWord_240133).sum := by decide
  have hdescent : baseEnd_240133 < baseStart_240133 := by decide
  rcases family_descends (prefixWord ++ tailWord_240133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240148 : List Nat := [2, 4, 3, 1, 1, 2, 6]
def baseStart_240148 : Nat := 118140960795 + 240148 * 2 ^ 59
def prefixEnd_240148 : Nat := 4983230072969 + 3 ^ 40 * 240148 * 2
def baseEnd_240148 : Nat := 24357797968598845144807

theorem tailTrace_240148 : CollatzResearch.WordTrace tailWord_240148 prefixEnd_240148 24357797968598845144807 := by
  unfold tailWord_240148
  simp only [CollatzResearch.WordTrace]
  refine ⟨4379458566996142429108549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5839278089328189905478065 4379458566996142429108549)
  ·
    refine ⟨821148481311776705457853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4379458566996142429108549 821148481311776705457853)
    ·
      refine ⟨307930680491916264546695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 821148481311776705457853 307930680491916264546695)
      ·
        refine ⟨461896020737874396820043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307930680491916264546695 461896020737874396820043)
        ·
          refine ⟨692844031106811595230065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461896020737874396820043 692844031106811595230065)
          ·
            refine ⟨519633023330108696422549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692844031106811595230065 519633023330108696422549)
            ·
              refine ⟨24357797968598845144807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 519633023330108696422549 24357797968598845144807)
              ·
                rfl

theorem cell19_240148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 6].length) (baseStart_240148 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240148 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240148 prefixEnd_240148 := by exact prefixLift 240148
  have htrace : WordTrace (prefixWord ++ tailWord_240148) baseStart_240148 baseEnd_240148 := by
    simpa [prefixWord, tailWord_240148, baseEnd_240148] using wordTrace_append hprefix tailTrace_240148
  have hstable : (prefixWord ++ tailWord_240148).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240148).length < 2 ^ (prefixWord ++ tailWord_240148).sum := by decide
  have hdescent : baseEnd_240148 < baseStart_240148 := by decide
  rcases family_descends (prefixWord ++ tailWord_240148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240180 : List Nat := [2, 5, 1, 3, 2, 1, 2, 3]
def baseStart_240180 : Nat := 118140960795 + 240180 * 2 ^ 59
def prefixEnd_240180 : Nat := 4983230072969 + 3 ^ 40 * 240180 * 2
def baseEnd_240180 : Nat := 73083131020429942723223

theorem tailTrace_240180 : CollatzResearch.WordTrace tailWord_240180 prefixEnd_240180 73083131020429942723223 := by
  unfold tailWord_240180
  simp only [CollatzResearch.WordTrace]
  refine ⟨4380042134938177161690997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5840056179917569548921329 4380042134938177161690997)
  ·
    refine ⟨410628950150454108908531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4380042134938177161690997 410628950150454108908531)
    ·
      refine ⟨615943425225681163362797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410628950150454108908531 615943425225681163362797)
      ·
        refine ⟨230978784459630436261049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 615943425225681163362797 230978784459630436261049)
        ·
          refine ⟨173234088344722827195787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230978784459630436261049 173234088344722827195787)
          ·
            refine ⟨259851132517084240793681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173234088344722827195787 259851132517084240793681)
            ·
              refine ⟨194888349387813180595261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259851132517084240793681 194888349387813180595261)
              ·
                refine ⟨73083131020429942723223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194888349387813180595261 73083131020429942723223)
                ·
                  rfl

theorem cell19_240180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 3].length) (baseStart_240180 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240180 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240180 prefixEnd_240180 := by exact prefixLift 240180
  have htrace : WordTrace (prefixWord ++ tailWord_240180) baseStart_240180 baseEnd_240180 := by
    simpa [prefixWord, tailWord_240180, baseEnd_240180] using wordTrace_append hprefix tailTrace_240180
  have hstable : (prefixWord ++ tailWord_240180).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240180).length < 2 ^ (prefixWord ++ tailWord_240180).sum := by decide
  have hdescent : baseEnd_240180 < baseStart_240180 := by decide
  rcases family_descends (prefixWord ++ tailWord_240180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240186 : List Nat := [3, 1, 1, 1, 3, 5, 2, 3]
def baseStart_240186 : Nat := 118140960795 + 240186 * 2 ^ 59
def prefixEnd_240186 : Nat := 4983230072969 + 3 ^ 40 * 240186 * 2
def baseEnd_240186 : Nat := 73084956729423706589873

theorem tailTrace_240186 : CollatzResearch.WordTrace tailWord_240186 prefixEnd_240186 73084956729423706589873 := by
  unfold tailWord_240186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2190075776963654337025103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5840202071903078232066941 2190075776963654337025103)
  ·
    refine ⟨3285113665445481505537655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2190075776963654337025103 3285113665445481505537655)
    ·
      refine ⟨4927670498168222258306483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3285113665445481505537655 4927670498168222258306483)
      ·
        refine ⟨7391505747252333387459725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4927670498168222258306483 7391505747252333387459725)
        ·
          refine ⟨2771814655219625020297397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7391505747252333387459725 2771814655219625020297397)
          ·
            refine ⟨259857623926839845652881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2771814655219625020297397 259857623926839845652881)
            ·
              refine ⟨194893217945129884239661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259857623926839845652881 194893217945129884239661)
              ·
                refine ⟨73084956729423706589873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194893217945129884239661 73084956729423706589873)
                ·
                  rfl

theorem cell19_240186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_240186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240186 prefixEnd_240186 := by exact prefixLift 240186
  have htrace : WordTrace (prefixWord ++ tailWord_240186) baseStart_240186 baseEnd_240186 := by
    simpa [prefixWord, tailWord_240186, baseEnd_240186] using wordTrace_append hprefix tailTrace_240186
  have hstable : (prefixWord ++ tailWord_240186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240186).length < 2 ^ (prefixWord ++ tailWord_240186).sum := by decide
  have hdescent : baseEnd_240186 < baseStart_240186 := by decide
  rcases family_descends (prefixWord ++ tailWord_240186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240188 : List Nat := [2, 2, 2, 2, 3, 2, 1, 5]
def baseStart_240188 : Nat := 118140960795 + 240188 * 2 ^ 59
def prefixEnd_240188 : Nat := 4983230072969 + 3 ^ 40 * 240188 * 2
def baseEnd_240188 : Nat := 73085565299088294545423

theorem tailTrace_240188 : CollatzResearch.WordTrace tailWord_240188 prefixEnd_240188 73085565299088294545423 := by
  unfold tailWord_240188
  simp only [CollatzResearch.WordTrace]
  refine ⟨4380188026923685844836609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5840250702564914459782145 4380188026923685844836609)
  ·
    refine ⟨3285141020192764383627457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4380188026923685844836609 3285141020192764383627457)
    ·
      refine ⟨2463855765144573287720593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3285141020192764383627457 2463855765144573287720593)
      ·
        refine ⟨1847891823858429965790445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2463855765144573287720593 1847891823858429965790445)
        ·
          refine ⟨692959433946911237171417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1847891823858429965790445 692959433946911237171417)
          ·
            refine ⟨519719575460183427878563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692959433946911237171417 519719575460183427878563)
            ·
              refine ⟨779579363190275141817845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519719575460183427878563 779579363190275141817845)
              ·
                refine ⟨73085565299088294545423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 779579363190275141817845 73085565299088294545423)
                ·
                  rfl

theorem cell19_240188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_240188 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240188 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240188 prefixEnd_240188 := by exact prefixLift 240188
  have htrace : WordTrace (prefixWord ++ tailWord_240188) baseStart_240188 baseEnd_240188 := by
    simpa [prefixWord, tailWord_240188, baseEnd_240188] using wordTrace_append hprefix tailTrace_240188
  have hstable : (prefixWord ++ tailWord_240188).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240188).length < 2 ^ (prefixWord ++ tailWord_240188).sum := by decide
  have hdescent : baseEnd_240188 < baseStart_240188 := by decide
  rcases family_descends (prefixWord ++ tailWord_240188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240205 : List Nat := [1, 6, 1, 1, 2, 3, 5]
def baseStart_240205 : Nat := 118140960795 + 240205 * 2 ^ 59
def prefixEnd_240205 : Nat := 4983230072969 + 3 ^ 40 * 240205 * 2
def baseEnd_240205 : Nat := 24363579380412430722533

theorem tailTrace_240205 : CollatzResearch.WordTrace tailWord_240205 prefixEnd_240205 24363579380412430722533 := by
  unfold tailWord_240205
  simp only [CollatzResearch.WordTrace]
  refine ⟨8760996094785783593042069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5840664063190522395361379 8760996094785783593042069)
  ·
    refine ⟨410671691943083605923847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8760996094785783593042069 410671691943083605923847)
    ·
      refine ⟨616007537914625408885771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410671691943083605923847 616007537914625408885771)
      ·
        refine ⟨924011306871938113328657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616007537914625408885771 924011306871938113328657)
        ·
          refine ⟨693008480153953584996493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 924011306871938113328657 693008480153953584996493)
          ·
            refine ⟨259878180057732594373685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 693008480153953584996493 259878180057732594373685)
            ·
              refine ⟨24363579380412430722533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 259878180057732594373685 24363579380412430722533)
              ·
                rfl

theorem cell19_240205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 5].length) (baseStart_240205 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240205 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240205 prefixEnd_240205 := by exact prefixLift 240205
  have htrace : WordTrace (prefixWord ++ tailWord_240205) baseStart_240205 baseEnd_240205 := by
    simpa [prefixWord, tailWord_240205, baseEnd_240205] using wordTrace_append hprefix tailTrace_240205
  have hstable : (prefixWord ++ tailWord_240205).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240205).length < 2 ^ (prefixWord ++ tailWord_240205).sum := by decide
  have hdescent : baseEnd_240205 < baseStart_240205 := by decide
  rcases family_descends (prefixWord ++ tailWord_240205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240209 : List Nat := [1, 2, 2, 1, 3, 3, 7]
def baseStart_240209 : Nat := 118140960795 + 240209 * 2 ^ 59
def prefixEnd_240209 : Nat := 4983230072969 + 3 ^ 40 * 240209 * 2
def baseEnd_240209 : Nat := 24363985093522156026233

theorem tailTrace_240209 : CollatzResearch.WordTrace tailWord_240209 prefixEnd_240209 24363985093522156026233 := by
  unfold tailWord_240209
  simp only [CollatzResearch.WordTrace]
  refine ⟨8761141986771292276187681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5840761324514194850791787 8761141986771292276187681)
  ·
    refine ⟨6570856490078469207140761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8761141986771292276187681 6570856490078469207140761)
    ·
      refine ⟨4928142367558851905355571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6570856490078469207140761 4928142367558851905355571)
      ·
        refine ⟨7392213551338277858033357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4928142367558851905355571 7392213551338277858033357)
        ·
          refine ⟨2772080081751854196762509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7392213551338277858033357 2772080081751854196762509)
          ·
            refine ⟨1039530030656945323785941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2772080081751854196762509 1039530030656945323785941)
            ·
              refine ⟨24363985093522156026233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1039530030656945323785941 24363985093522156026233)
              ·
                rfl

theorem cell19_240209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 7].length) (baseStart_240209 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240209 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240209 prefixEnd_240209 := by exact prefixLift 240209
  have htrace : WordTrace (prefixWord ++ tailWord_240209) baseStart_240209 baseEnd_240209 := by
    simpa [prefixWord, tailWord_240209, baseEnd_240209] using wordTrace_append hprefix tailTrace_240209
  have hstable : (prefixWord ++ tailWord_240209).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240209).length < 2 ^ (prefixWord ++ tailWord_240209).sum := by decide
  have hdescent : baseEnd_240209 < baseStart_240209 := by decide
  rcases family_descends (prefixWord ++ tailWord_240209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240247 : List Nat := [1, 1, 3, 1, 1, 3, 4, 5]
def baseStart_240247 : Nat := 118140960795 + 240247 * 2 ^ 59
def prefixEnd_240247 : Nat := 4983230072969 + 3 ^ 40 * 240247 * 2
def baseEnd_240247 : Nat := 73103518104193639234151

theorem tailTrace_240247 : CollatzResearch.WordTrace tailWord_240247 prefixEnd_240247 73103518104193639234151 := by
  unfold tailWord_240247
  simp only [CollatzResearch.WordTrace]
  refine ⟨8762527960633624766070995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5841685307089083177380663 8762527960633624766070995)
  ·
    refine ⟨13143791940950437149106493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8762527960633624766070995 13143791940950437149106493)
    ·
      refine ⟨4928921977856413930914935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13143791940950437149106493 4928921977856413930914935)
      ·
        refine ⟨7393382966784620896372403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4928921977856413930914935 7393382966784620896372403)
        ·
          refine ⟨11090074450176931344558605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7393382966784620896372403 11090074450176931344558605)
          ·
            refine ⟨4158777918816349254209477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11090074450176931344558605 4158777918816349254209477)
            ·
              refine ⟨779770859778065485164277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4158777918816349254209477 779770859778065485164277)
              ·
                refine ⟨73103518104193639234151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 779770859778065485164277 73103518104193639234151)
                ·
                  rfl

theorem cell19_240247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_240247 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240247 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240247 prefixEnd_240247 := by exact prefixLift 240247
  have htrace : WordTrace (prefixWord ++ tailWord_240247) baseStart_240247 baseEnd_240247 := by
    simpa [prefixWord, tailWord_240247, baseEnd_240247] using wordTrace_append hprefix tailTrace_240247
  have hstable : (prefixWord ++ tailWord_240247).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240247).length < 2 ^ (prefixWord ++ tailWord_240247).sum := by decide
  have hdescent : baseEnd_240247 < baseStart_240247 := by decide
  rcases family_descends (prefixWord ++ tailWord_240247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240258 : List Nat := [3, 4, 3, 1, 2, 6]
def baseStart_240258 : Nat := 118140960795 + 240258 * 2 ^ 59
def prefixEnd_240258 : Nat := 4983230072969 + 3 ^ 40 * 240258 * 2
def baseEnd_240258 : Nat := 8122985026372096998853

theorem tailTrace_240258 : CollatzResearch.WordTrace tailWord_240258 prefixEnd_240258 8122985026372096998853 := by
  unfold tailWord_240258
  simp only [CollatzResearch.WordTrace]
  refine ⟨2190732290898443411180357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5841952775729182429814285 2190732290898443411180357)
  ·
    refine ⟨410762304543458139596317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2190732290898443411180357 410762304543458139596317)
    ·
      refine ⟨154035864203796802348619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 410762304543458139596317 154035864203796802348619)
      ·
        refine ⟨231053796305695203522929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154035864203796802348619 231053796305695203522929)
        ·
          refine ⟨173290347229271402642197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231053796305695203522929 173290347229271402642197)
          ·
            refine ⟨8122985026372096998853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 173290347229271402642197 8122985026372096998853)
            ·
              rfl

theorem cell19_240258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 6].length) (baseStart_240258 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240258 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240258 prefixEnd_240258 := by exact prefixLift 240258
  have htrace : WordTrace (prefixWord ++ tailWord_240258) baseStart_240258 baseEnd_240258 := by
    simpa [prefixWord, tailWord_240258, baseEnd_240258] using wordTrace_append hprefix tailTrace_240258
  have hstable : (prefixWord ++ tailWord_240258).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240258).length < 2 ^ (prefixWord ++ tailWord_240258).sum := by decide
  have hdescent : baseEnd_240258 < baseStart_240258 := by decide
  rcases family_descends (prefixWord ++ tailWord_240258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240266 : List Nat := [3, 1, 2, 3, 10]
def baseStart_240266 : Nat := 118140960795 + 240266 * 2 ^ 59
def prefixEnd_240266 : Nat := 4983230072969 + 3 ^ 40 * 240266 * 2
def baseEnd_240266 : Nat := 2707751833926193511551

theorem tailTrace_240266 : CollatzResearch.WordTrace tailWord_240266 prefixEnd_240266 2707751833926193511551 := by
  unfold tailWord_240266
  simp only [CollatzResearch.WordTrace]
  refine ⟨2190805236891197752753163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5842147298376527340675101 2190805236891197752753163)
  ·
    refine ⟨3286207855336796629129745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2190805236891197752753163 3286207855336796629129745)
    ·
      refine ⟨2464655891502597471847309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3286207855336796629129745 2464655891502597471847309)
      ·
        refine ⟨924245959313474051942741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2464655891502597471847309 924245959313474051942741)
        ·
          refine ⟨2707751833926193511551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 924245959313474051942741 2707751833926193511551)
          ·
            rfl

theorem cell19_240266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 10].length) (baseStart_240266 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240266 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240266 prefixEnd_240266 := by exact prefixLift 240266
  have htrace : WordTrace (prefixWord ++ tailWord_240266) baseStart_240266 baseEnd_240266 := by
    simpa [prefixWord, tailWord_240266, baseEnd_240266] using wordTrace_append hprefix tailTrace_240266
  have hstable : (prefixWord ++ tailWord_240266).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240266).length < 2 ^ (prefixWord ++ tailWord_240266).sum := by decide
  have hdescent : baseEnd_240266 < baseStart_240266 := by decide
  rcases family_descends (prefixWord ++ tailWord_240266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240357 : List Nat := [1, 3, 1, 4, 1, 4, 2, 3]
def baseStart_240357 : Nat := 118140960795 + 240357 * 2 ^ 59
def prefixEnd_240357 : Nat := 4983230072969 + 3 ^ 40 * 240357 * 2
def baseEnd_240357 : Nat := 73136989435745976789407

theorem tailTrace_240357 : CollatzResearch.WordTrace tailWord_240357 prefixEnd_240357 73136989435745976789407 := by
  unfold tailWord_240357
  simp only [CollatzResearch.WordTrace]
  refine ⟨8766539990235113552575325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5844359993490075701716883 8766539990235113552575325)
  ·
    refine ⟨3287452496338167582215747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8766539990235113552575325 3287452496338167582215747)
    ·
      refine ⟨4931178744507251373323621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3287452496338167582215747 4931178744507251373323621)
      ·
        refine ⟨924596014595109632498179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4931178744507251373323621 924596014595109632498179)
        ·
          refine ⟨1386894021892664448747269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924596014595109632498179 1386894021892664448747269)
          ·
            refine ⟨260042629104874584140113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1386894021892664448747269 260042629104874584140113)
            ·
              refine ⟨195031971828655938105085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260042629104874584140113 195031971828655938105085)
              ·
                refine ⟨73136989435745976789407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195031971828655938105085 73136989435745976789407)
                ·
                  rfl

theorem cell19_240357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 3].length) (baseStart_240357 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240357 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240357 prefixEnd_240357 := by exact prefixLift 240357
  have htrace : WordTrace (prefixWord ++ tailWord_240357) baseStart_240357 baseEnd_240357 := by
    simpa [prefixWord, tailWord_240357, baseEnd_240357] using wordTrace_append hprefix tailTrace_240357
  have hstable : (prefixWord ++ tailWord_240357).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240357).length < 2 ^ (prefixWord ++ tailWord_240357).sum := by decide
  have hdescent : baseEnd_240357 < baseStart_240357 := by decide
  rcases family_descends (prefixWord ++ tailWord_240357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240372 : List Nat := [2, 6, 1, 1, 3, 1, 5]
def baseStart_240372 : Nat := 118140960795 + 240372 * 2 ^ 59
def prefixEnd_240372 : Nat := 4983230072969 + 3 ^ 40 * 240372 * 2
def baseEnd_240372 : Nat := 24380517902743462152011

theorem tailTrace_240372 : CollatzResearch.WordTrace tailWord_240372 prefixEnd_240372 24380517902743462152011 := by
  unfold tailWord_240372
  simp only [CollatzResearch.WordTrace]
  refine ⟨4383543542590385557185685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5844724723453847409580913 4383543542590385557185685)
  ·
    refine ⟨205478603558924322993079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4383543542590385557185685 205478603558924322993079)
    ·
      refine ⟨308217905338386484489619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205478603558924322993079 308217905338386484489619)
      ·
        refine ⟨462326858007579726734429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308217905338386484489619 462326858007579726734429)
        ·
          refine ⟨173372571752842397525411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 462326858007579726734429 173372571752842397525411)
          ·
            refine ⟨260058857629263596288117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173372571752842397525411 260058857629263596288117)
            ·
              refine ⟨24380517902743462152011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 260058857629263596288117 24380517902743462152011)
              ·
                rfl

theorem cell19_240372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 5].length) (baseStart_240372 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240372 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240372 prefixEnd_240372 := by exact prefixLift 240372
  have htrace : WordTrace (prefixWord ++ tailWord_240372) baseStart_240372 baseEnd_240372 := by
    simpa [prefixWord, tailWord_240372, baseEnd_240372] using wordTrace_append hprefix tailTrace_240372
  have hstable : (prefixWord ++ tailWord_240372).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240372).length < 2 ^ (prefixWord ++ tailWord_240372).sum := by decide
  have hdescent : baseEnd_240372 < baseStart_240372 := by decide
  rcases family_descends (prefixWord ++ tailWord_240372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240380 : List Nat := [2, 2, 2, 1, 3, 2, 7]
def baseStart_240380 : Nat := 118140960795 + 240380 * 2 ^ 59
def prefixEnd_240380 : Nat := 4983230072969 + 3 ^ 40 * 240380 * 2
def baseEnd_240380 : Nat := 24381329328962912759411

theorem tailTrace_240380 : CollatzResearch.WordTrace tailWord_240380 prefixEnd_240380 24381329328962912759411 := by
  unfold tailWord_240380
  simp only [CollatzResearch.WordTrace]
  refine ⟨4383689434575894240331297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5844919246101192320441729 4383689434575894240331297)
  ·
    refine ⟨3287767075931920680248473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4383689434575894240331297 3287767075931920680248473)
    ·
      refine ⟨2465825306948940510186355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3287767075931920680248473 2465825306948940510186355)
      ·
        refine ⟨3698737960423410765279533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2465825306948940510186355 3698737960423410765279533)
        ·
          refine ⟨1387026735158779036979825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3698737960423410765279533 1387026735158779036979825)
          ·
            refine ⟨1040270051369084277734869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1387026735158779036979825 1040270051369084277734869)
            ·
              refine ⟨24381329328962912759411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1040270051369084277734869 24381329328962912759411)
              ·
                rfl

theorem cell19_240380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 7].length) (baseStart_240380 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240380 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240380 prefixEnd_240380 := by exact prefixLift 240380
  have htrace : WordTrace (prefixWord ++ tailWord_240380) baseStart_240380 baseEnd_240380 := by
    simpa [prefixWord, tailWord_240380, baseEnd_240380] using wordTrace_append hprefix tailTrace_240380
  have hstable : (prefixWord ++ tailWord_240380).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240380).length < 2 ^ (prefixWord ++ tailWord_240380).sum := by decide
  have hdescent : baseEnd_240380 < baseStart_240380 := by decide
  rcases family_descends (prefixWord ++ tailWord_240380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240399 : List Nat := [1, 1, 2, 1, 1, 1, 8, 4]
def baseStart_240399 : Nat := 118140960795 + 240399 * 2 ^ 59
def prefixEnd_240399 : Nat := 4983230072969 + 3 ^ 40 * 240399 * 2
def baseEnd_240399 : Nat := 73149769398702323855959

theorem tailTrace_240399 : CollatzResearch.WordTrace tailWord_240399 prefixEnd_240399 73149769398702323855959 := by
  unfold tailWord_240399
  simp only [CollatzResearch.WordTrace]
  refine ⟨8768071856082954725604251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5845381237388636483736167 8768071856082954725604251)
  ·
    refine ⟨13152107784124432088406377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8768071856082954725604251 13152107784124432088406377)
    ·
      refine ⟨9864080838093324066304783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13152107784124432088406377 9864080838093324066304783)
      ·
        refine ⟨14796121257139986099457175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9864080838093324066304783 14796121257139986099457175)
        ·
          refine ⟨22194181885709979149185763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14796121257139986099457175 22194181885709979149185763)
          ·
            refine ⟨33291272828564968723778645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22194181885709979149185763 33291272828564968723778645)
            ·
              refine ⟨390132103459745727231781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 33291272828564968723778645 390132103459745727231781)
              ·
                refine ⟨73149769398702323855959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 390132103459745727231781 73149769398702323855959)
                ·
                  rfl

theorem cell19_240399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 4].length) (baseStart_240399 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240399 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240399 prefixEnd_240399 := by exact prefixLift 240399
  have htrace : WordTrace (prefixWord ++ tailWord_240399) baseStart_240399 baseEnd_240399 := by
    simpa [prefixWord, tailWord_240399, baseEnd_240399] using wordTrace_append hprefix tailTrace_240399
  have hstable : (prefixWord ++ tailWord_240399).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240399).length < 2 ^ (prefixWord ++ tailWord_240399).sum := by decide
  have hdescent : baseEnd_240399 < baseStart_240399 := by decide
  rcases family_descends (prefixWord ++ tailWord_240399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240437 : List Nat := [1, 3, 3, 1, 3, 8]
def baseStart_240437 : Nat := 118140960795 + 240437 * 2 ^ 59
def prefixEnd_240437 : Nat := 4983230072969 + 3 ^ 40 * 240437 * 2
def baseEnd_240437 : Nat := 8129036913592166112379

theorem tailTrace_240437 : CollatzResearch.WordTrace tailWord_240437 prefixEnd_240437 8129036913592166112379 := by
  unfold tailWord_240437
  simp only [CollatzResearch.WordTrace]
  refine ⟨8769457829945287215487565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5846305219963524810325043 8769457829945287215487565)
  ·
    refine ⟨3288546686229482705807837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8769457829945287215487565 3288546686229482705807837)
    ·
      refine ⟨1233205007336056014677939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3288546686229482705807837 1233205007336056014677939)
      ·
        refine ⟨1849807511004084022016909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1233205007336056014677939 1849807511004084022016909)
        ·
          refine ⟨693677816626531508256341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1849807511004084022016909 693677816626531508256341)
          ·
            refine ⟨8129036913592166112379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 693677816626531508256341 8129036913592166112379)
            ·
              rfl

theorem cell19_240437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 8].length) (baseStart_240437 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240437 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240437 prefixEnd_240437 := by exact prefixLift 240437
  have htrace : WordTrace (prefixWord ++ tailWord_240437) baseStart_240437 baseEnd_240437 := by
    simpa [prefixWord, tailWord_240437, baseEnd_240437] using wordTrace_append hprefix tailTrace_240437
  have hstable : (prefixWord ++ tailWord_240437).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240437).length < 2 ^ (prefixWord ++ tailWord_240437).sum := by decide
  have hdescent : baseEnd_240437 < baseStart_240437 := by decide
  rcases family_descends (prefixWord ++ tailWord_240437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240473 : List Nat := [1, 2, 1, 2, 2, 5, 3, 3]
def baseStart_240473 : Nat := 118140960795 + 240473 * 2 ^ 59
def prefixEnd_240473 : Nat := 4983230072969 + 3 ^ 40 * 240473 * 2
def baseEnd_240473 : Nat := 73172286476292078211313

theorem tailTrace_240473 : CollatzResearch.WordTrace tailWord_240473 prefixEnd_240473 73172286476292078211313 := by
  unfold tailWord_240473
  simp only [CollatzResearch.WordTrace]
  refine ⟨8770770857814865363798073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5847180571876576909198715 8770770857814865363798073)
  ·
    refine ⟨6578078143361149022848555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8770770857814865363798073 6578078143361149022848555)
    ·
      refine ⟨9867117215041723534272833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6578078143361149022848555 9867117215041723534272833)
      ·
        refine ⟨7400337911281292650704625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9867117215041723534272833 7400337911281292650704625)
        ·
          refine ⟨5550253433460969488028469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7400337911281292650704625 5550253433460969488028469)
          ·
            refine ⟨520336259386965889502669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5550253433460969488028469 520336259386965889502669)
            ·
              refine ⟨195126097270112208563501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 520336259386965889502669 195126097270112208563501)
              ·
                refine ⟨73172286476292078211313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195126097270112208563501 73172286476292078211313)
                ·
                  rfl

theorem cell19_240473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 3].length) (baseStart_240473 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240473 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240473 prefixEnd_240473 := by exact prefixLift 240473
  have htrace : WordTrace (prefixWord ++ tailWord_240473) baseStart_240473 baseEnd_240473 := by
    simpa [prefixWord, tailWord_240473, baseEnd_240473] using wordTrace_append hprefix tailTrace_240473
  have hstable : (prefixWord ++ tailWord_240473).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240473).length < 2 ^ (prefixWord ++ tailWord_240473).sum := by decide
  have hdescent : baseEnd_240473 < baseStart_240473 := by decide
  rcases family_descends (prefixWord ++ tailWord_240473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240570 : List Nat := [3, 1, 1, 1, 2, 1, 6, 4]
def baseStart_240570 : Nat := 118140960795 + 240570 * 2 ^ 59
def prefixEnd_240570 : Nat := 4983230072969 + 3 ^ 40 * 240570 * 2
def baseEnd_240570 : Nat := 73201802105024594055493

theorem tailTrace_240570 : CollatzResearch.WordTrace tailWord_240570 prefixEnd_240570 73201802105024594055493 := by
  unfold tailWord_240570
  simp only [CollatzResearch.WordTrace]
  refine ⟨2193577184615862732519791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5849539158975633953386109 2193577184615862732519791)
  ·
    refine ⟨3290365776923794098779687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2193577184615862732519791 3290365776923794098779687)
    ·
      refine ⟨4935548665385691148169531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3290365776923794098779687 4935548665385691148169531)
      ·
        refine ⟨7403322998078536722254297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4935548665385691148169531 7403322998078536722254297)
        ·
          refine ⟨5552492248558902541690723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7403322998078536722254297 5552492248558902541690723)
          ·
            refine ⟨8328738372838353812536085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5552492248558902541690723 8328738372838353812536085)
            ·
              refine ⟨390409611226797834962629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8328738372838353812536085 390409611226797834962629)
              ·
                refine ⟨73201802105024594055493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 390409611226797834962629 73201802105024594055493)
                ·
                  rfl

theorem cell19_240570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_240570 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240570 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240570 prefixEnd_240570 := by exact prefixLift 240570
  have htrace : WordTrace (prefixWord ++ tailWord_240570) baseStart_240570 baseEnd_240570 := by
    simpa [prefixWord, tailWord_240570, baseEnd_240570] using wordTrace_append hprefix tailTrace_240570
  have hstable : (prefixWord ++ tailWord_240570).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240570).length < 2 ^ (prefixWord ++ tailWord_240570).sum := by decide
  have hdescent : baseEnd_240570 < baseStart_240570 := by decide
  rcases family_descends (prefixWord ++ tailWord_240570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240625 : List Nat := [1, 2, 2, 2, 4, 3, 1, 4]
def baseStart_240625 : Nat := 118140960795 + 240625 * 2 ^ 59
def prefixEnd_240625 : Nat := 4983230072969 + 3 ^ 40 * 240625 * 2
def baseEnd_240625 : Nat := 73218537770800762833121

theorem tailTrace_240625 : CollatzResearch.WordTrace tailWord_240625 prefixEnd_240625 73218537770800762833121 := by
  unfold tailWord_240625
  simp only [CollatzResearch.WordTrace]
  refine ⟨8776314753264195323331329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5850876502176130215554219 8776314753264195323331329)
  ·
    refine ⟨6582236064948146492498497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8776314753264195323331329 6582236064948146492498497)
    ·
      refine ⟨4936677048711109869373873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6582236064948146492498497 4936677048711109869373873)
      ·
        refine ⟨3702507786533332402030405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4936677048711109869373873 3702507786533332402030405)
        ·
          refine ⟨694220209974999825380701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3702507786533332402030405 694220209974999825380701)
          ·
            refine ⟨260332578740624934517763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 694220209974999825380701 260332578740624934517763)
            ·
              refine ⟨390498868110937401776645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260332578740624934517763 390498868110937401776645)
              ·
                refine ⟨73218537770800762833121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 390498868110937401776645 73218537770800762833121)
                ·
                  rfl

theorem cell19_240625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 4].length) (baseStart_240625 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240625 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240625 prefixEnd_240625 := by exact prefixLift 240625
  have htrace : WordTrace (prefixWord ++ tailWord_240625) baseStart_240625 baseEnd_240625 := by
    simpa [prefixWord, tailWord_240625, baseEnd_240625] using wordTrace_append hprefix tailTrace_240625
  have hstable : (prefixWord ++ tailWord_240625).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240625).length < 2 ^ (prefixWord ++ tailWord_240625).sum := by decide
  have hdescent : baseEnd_240625 < baseStart_240625 := by decide
  rcases family_descends (prefixWord ++ tailWord_240625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240701 : List Nat := [1, 4, 1, 3, 1, 2, 4, 3]
def baseStart_240701 : Nat := 118140960795 + 240701 * 2 ^ 59
def prefixEnd_240701 : Nat := 4983230072969 + 3 ^ 40 * 240701 * 2
def baseEnd_240701 : Nat := 73241663418055105144025

theorem tailTrace_240701 : CollatzResearch.WordTrace tailWord_240701 prefixEnd_240701 73241663418055105144025 := by
  unfold tailWord_240701
  simp only [CollatzResearch.WordTrace]
  refine ⟨8779086700988860303097957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5852724467325906868731971 8779086700988860303097957)
  ·
    refine ⟨1646078756435411306830867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8779086700988860303097957 1646078756435411306830867)
    ·
      refine ⟨2469118134653116960246301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1646078756435411306830867 2469118134653116960246301)
      ·
        refine ⟨925919300494918860092363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2469118134653116960246301 925919300494918860092363)
        ·
          refine ⟨1388878950742378290138545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925919300494918860092363 1388878950742378290138545)
          ·
            refine ⟨1041659213056783717603909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1388878950742378290138545 1041659213056783717603909)
            ·
              refine ⟨195311102448146947050733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1041659213056783717603909 195311102448146947050733)
              ·
                refine ⟨73241663418055105144025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195311102448146947050733 73241663418055105144025)
                ·
                  rfl

theorem cell19_240701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 3].length) (baseStart_240701 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240701 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240701 prefixEnd_240701 := by exact prefixLift 240701
  have htrace : WordTrace (prefixWord ++ tailWord_240701) baseStart_240701 baseEnd_240701 := by
    simpa [prefixWord, tailWord_240701, baseEnd_240701] using wordTrace_append hprefix tailTrace_240701
  have hstable : (prefixWord ++ tailWord_240701).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240701).length < 2 ^ (prefixWord ++ tailWord_240701).sum := by decide
  have hdescent : baseEnd_240701 < baseStart_240701 := by decide
  rcases family_descends (prefixWord ++ tailWord_240701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240722 : List Nat := [3, 2, 2, 1, 3, 1, 7]
def baseStart_240722 : Nat := 118140960795 + 240722 * 2 ^ 59
def prefixEnd_240722 : Nat := 4983230072969 + 3 ^ 40 * 240722 * 2
def baseEnd_240722 : Nat := 24416017799844426225767

theorem tailTrace_240722 : CollatzResearch.WordTrace tailWord_240722 prefixEnd_240722 24416017799844426225767 := by
  unfold tailWord_240722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2194963158478195222403105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5853235089275187259741613 2194963158478195222403105)
  ·
    refine ⟨1646222368858646416802329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2194963158478195222403105 1646222368858646416802329)
    ·
      refine ⟨1234666776643984812601747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1646222368858646416802329 1234666776643984812601747)
      ·
        refine ⟨1852000164965977218902621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1234666776643984812601747 1852000164965977218902621)
        ·
          refine ⟨694500061862241457088483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1852000164965977218902621 694500061862241457088483)
          ·
            refine ⟨1041750092793362185632725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694500061862241457088483 1041750092793362185632725)
            ·
              refine ⟨24416017799844426225767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1041750092793362185632725 24416017799844426225767)
              ·
                rfl

theorem cell19_240722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 7].length) (baseStart_240722 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240722 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240722 prefixEnd_240722 := by exact prefixLift 240722
  have htrace : WordTrace (prefixWord ++ tailWord_240722) baseStart_240722 baseEnd_240722 := by
    simpa [prefixWord, tailWord_240722, baseEnd_240722] using wordTrace_append hprefix tailTrace_240722
  have hstable : (prefixWord ++ tailWord_240722).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240722).length < 2 ^ (prefixWord ++ tailWord_240722).sum := by decide
  have hdescent : baseEnd_240722 < baseStart_240722 := by decide
  rcases family_descends (prefixWord ++ tailWord_240722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240741 : List Nat := [1, 3, 1, 3, 2, 1, 4, 4]
def baseStart_240741 : Nat := 118140960795 + 240741 * 2 ^ 59
def prefixEnd_240741 : Nat := 4983230072969 + 3 ^ 40 * 240741 * 2
def baseEnd_240741 : Nat := 73253834811346864255027

theorem tailTrace_240741 : CollatzResearch.WordTrace tailWord_240741 prefixEnd_240741 73253834811346864255027 := by
  unfold tailWord_240741
  simp only [CollatzResearch.WordTrace]
  refine ⟨8780545620843947134554077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5853697080562631423036051 8780545620843947134554077)
  ·
    refine ⟨3292704607816480175457779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8780545620843947134554077 3292704607816480175457779)
    ·
      refine ⟨4939056911724720263186669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3292704607816480175457779 4939056911724720263186669)
      ·
        refine ⟨1852146341896770098695001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4939056911724720263186669 1852146341896770098695001)
        ·
          refine ⟨1389109756422577574021251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1852146341896770098695001 1389109756422577574021251)
          ·
            refine ⟨2083664634633866361031877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389109756422577574021251 2083664634633866361031877)
            ·
              refine ⟨390687118993849942693477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2083664634633866361031877 390687118993849942693477)
              ·
                refine ⟨73253834811346864255027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 390687118993849942693477 73253834811346864255027)
                ·
                  rfl

theorem cell19_240741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 4].length) (baseStart_240741 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240741 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240741 prefixEnd_240741 := by exact prefixLift 240741
  have htrace : WordTrace (prefixWord ++ tailWord_240741) baseStart_240741 baseEnd_240741 := by
    simpa [prefixWord, tailWord_240741, baseEnd_240741] using wordTrace_append hprefix tailTrace_240741
  have hstable : (prefixWord ++ tailWord_240741).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240741).length < 2 ^ (prefixWord ++ tailWord_240741).sum := by decide
  have hdescent : baseEnd_240741 < baseStart_240741 := by decide
  rcases family_descends (prefixWord ++ tailWord_240741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240796 : List Nat := [2, 2, 3, 2, 1, 4, 1, 4]
def baseStart_240796 : Nat := 118140960795 + 240796 * 2 ^ 59
def prefixEnd_240796 : Nat := 4983230072969 + 3 ^ 40 * 240796 * 2
def baseEnd_240796 : Nat := 73270570477123033032655

theorem tailTrace_240796 : CollatzResearch.WordTrace tailWord_240796 prefixEnd_240796 73270570477123033032655 := by
  unfold tailWord_240796
  simp only [CollatzResearch.WordTrace]
  refine ⟨4391275817822345763903121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5855034423763127685204161 4391275817822345763903121)
  ·
    refine ⟨3293456863366759322927341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4391275817822345763903121 3293456863366759322927341)
    ·
      refine ⟨1235046323762534746097753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3293456863366759322927341 1235046323762534746097753)
      ·
        refine ⟨926284742821901059573315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1235046323762534746097753 926284742821901059573315)
        ·
          refine ⟨1389427114232851589359973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926284742821901059573315 1389427114232851589359973)
          ·
            refine ⟨260517583918659673004995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1389427114232851589359973 260517583918659673004995)
            ·
              refine ⟨390776375877989509507493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260517583918659673004995 390776375877989509507493)
              ·
                refine ⟨73270570477123033032655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 390776375877989509507493 73270570477123033032655)
                ·
                  rfl

theorem cell19_240796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_240796 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240796 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240796 prefixEnd_240796 := by exact prefixLift 240796
  have htrace : WordTrace (prefixWord ++ tailWord_240796) baseStart_240796 baseEnd_240796 := by
    simpa [prefixWord, tailWord_240796, baseEnd_240796] using wordTrace_append hprefix tailTrace_240796
  have hstable : (prefixWord ++ tailWord_240796).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240796).length < 2 ^ (prefixWord ++ tailWord_240796).sum := by decide
  have hdescent : baseEnd_240796 < baseStart_240796 := by decide
  rcases family_descends (prefixWord ++ tailWord_240796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240813 : List Nat := [1, 5, 2, 1, 3, 1, 3, 3]
def baseStart_240813 : Nat := 118140960795 + 240813 * 2 ^ 59
def prefixEnd_240813 : Nat := 4983230072969 + 3 ^ 40 * 240813 * 2
def baseEnd_240813 : Nat := 73275743319272030654831

theorem tailTrace_240813 : CollatzResearch.WordTrace tailWord_240813 prefixEnd_240813 73275743319272030654831 := by
  unfold tailWord_240813
  simp only [CollatzResearch.WordTrace]
  refine ⟨8783171676583103431175093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5855447784388735620783395 8783171676583103431175093)
  ·
    refine ⟨823422344679665946672665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8783171676583103431175093 823422344679665946672665)
    ·
      refine ⟨617566758509749460004499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 823422344679665946672665 617566758509749460004499)
      ·
        refine ⟨926350137764624190006749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617566758509749460004499 926350137764624190006749)
        ·
          refine ⟨347381301661734071252531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 926350137764624190006749 347381301661734071252531)
          ·
            refine ⟨521071952492601106878797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347381301661734071252531 521071952492601106878797)
            ·
              refine ⟨195401982184725415079549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 521071952492601106878797 195401982184725415079549)
              ·
                refine ⟨73275743319272030654831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195401982184725415079549 73275743319272030654831)
                ·
                  rfl

theorem cell19_240813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 3].length) (baseStart_240813 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240813 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240813 prefixEnd_240813 := by exact prefixLift 240813
  have htrace : WordTrace (prefixWord ++ tailWord_240813) baseStart_240813 baseEnd_240813 := by
    simpa [prefixWord, tailWord_240813, baseEnd_240813] using wordTrace_append hprefix tailTrace_240813
  have hstable : (prefixWord ++ tailWord_240813).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240813).length < 2 ^ (prefixWord ++ tailWord_240813).sum := by decide
  have hdescent : baseEnd_240813 < baseStart_240813 := by decide
  rcases family_descends (prefixWord ++ tailWord_240813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240819 : List Nat := [1, 1, 1, 2, 3, 2, 2, 7]
def baseStart_240819 : Nat := 118140960795 + 240819 * 2 ^ 59
def prefixEnd_240819 : Nat := 4983230072969 + 3 ^ 40 * 240819 * 2
def baseEnd_240819 : Nat := 73277569028265794521481

theorem tailTrace_240819 : CollatzResearch.WordTrace tailWord_240819 prefixEnd_240819 73277569028265794521481 := by
  unfold tailWord_240819
  simp only [CollatzResearch.WordTrace]
  refine ⟨8783390514561366455893511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5855593676374244303929007 8783390514561366455893511)
  ·
    refine ⟨13175085771842049683840267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8783390514561366455893511 13175085771842049683840267)
    ·
      refine ⟨19762628657763074525760401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13175085771842049683840267 19762628657763074525760401)
      ·
        refine ⟨14821971493322305894320301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19762628657763074525760401 14821971493322305894320301)
        ·
          refine ⟨5558239309995864710370113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14821971493322305894320301 5558239309995864710370113)
          ·
            refine ⟨4168679482496898532777585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5558239309995864710370113 4168679482496898532777585)
            ·
              refine ⟨3126509611872673899583189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4168679482496898532777585 3126509611872673899583189)
              ·
                refine ⟨73277569028265794521481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3126509611872673899583189 73277569028265794521481)
                ·
                  rfl

theorem cell19_240819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_240819 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240819 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240819 prefixEnd_240819 := by exact prefixLift 240819
  have htrace : WordTrace (prefixWord ++ tailWord_240819) baseStart_240819 baseEnd_240819 := by
    simpa [prefixWord, tailWord_240819, baseEnd_240819] using wordTrace_append hprefix tailTrace_240819
  have hstable : (prefixWord ++ tailWord_240819).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240819).length < 2 ^ (prefixWord ++ tailWord_240819).sum := by decide
  have hdescent : baseEnd_240819 < baseStart_240819 := by decide
  rcases family_descends (prefixWord ++ tailWord_240819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240857 : List Nat := [1, 2, 1, 2, 3, 1, 1, 8]
def baseStart_240857 : Nat := 118140960795 + 240857 * 2 ^ 59
def prefixEnd_240857 : Nat := 4983230072969 + 3 ^ 40 * 240857 * 2
def baseEnd_240857 : Nat := 73289131851892965676933

theorem tailTrace_240857 : CollatzResearch.WordTrace tailWord_240857 prefixEnd_240857 73289131851892965676933 := by
  unfold tailWord_240857
  simp only [CollatzResearch.WordTrace]
  refine ⟨8784776488423698945776825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5856517658949132630517883 8784776488423698945776825)
  ·
    refine ⟨6588582366317774209332619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8784776488423698945776825 6588582366317774209332619)
    ·
      refine ⟨9882873549476661313998929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6588582366317774209332619 9882873549476661313998929)
      ·
        refine ⟨7412155162107495985499197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9882873549476661313998929 7412155162107495985499197)
        ·
          refine ⟨2779558185790310994562199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7412155162107495985499197 2779558185790310994562199)
          ·
            refine ⟨4169337278685466491843299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2779558185790310994562199 4169337278685466491843299)
            ·
              refine ⟨6254005918028199737764949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4169337278685466491843299 6254005918028199737764949)
              ·
                refine ⟨73289131851892965676933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6254005918028199737764949 73289131851892965676933)
                ·
                  rfl

theorem cell19_240857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_240857 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240857 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240857 prefixEnd_240857 := by exact prefixLift 240857
  have htrace : WordTrace (prefixWord ++ tailWord_240857) baseStart_240857 baseEnd_240857 := by
    simpa [prefixWord, tailWord_240857, baseEnd_240857] using wordTrace_append hprefix tailTrace_240857
  have hstable : (prefixWord ++ tailWord_240857).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240857).length < 2 ^ (prefixWord ++ tailWord_240857).sum := by decide
  have hdescent : baseEnd_240857 < baseStart_240857 := by decide
  rcases family_descends (prefixWord ++ tailWord_240857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240874 : List Nat := [3, 1, 3, 1, 1, 4, 1, 5]
def baseStart_240874 : Nat := 118140960795 + 240874 * 2 ^ 59
def prefixEnd_240874 : Nat := 4983230072969 + 3 ^ 40 * 240874 * 2
def baseEnd_240874 : Nat := 73294304694041963299109

theorem tailTrace_240874 : CollatzResearch.WordTrace tailWord_240874 prefixEnd_240874 73294304694041963299109 := by
  unfold tailWord_240874
  simp only [CollatzResearch.WordTrace]
  refine ⟨2196349132340527712286419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5856931019574740566097117 2196349132340527712286419)
  ·
    refine ⟨3294523698510791568429629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2196349132340527712286419 3294523698510791568429629)
    ·
      refine ⟨1235446386941546838161111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3294523698510791568429629 1235446386941546838161111)
      ·
        refine ⟨1853169580412320257241667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1235446386941546838161111 1853169580412320257241667)
        ·
          refine ⟨2779754370618480385862501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1853169580412320257241667 2779754370618480385862501)
          ·
            refine ⟨521203944490965072349219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2779754370618480385862501 521203944490965072349219)
            ·
              refine ⟨781805916736447608523829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521203944490965072349219 781805916736447608523829)
              ·
                refine ⟨73294304694041963299109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 781805916736447608523829 73294304694041963299109)
                ·
                  rfl

theorem cell19_240874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_240874 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240874 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240874 prefixEnd_240874 := by exact prefixLift 240874
  have htrace : WordTrace (prefixWord ++ tailWord_240874) baseStart_240874 baseEnd_240874 := by
    simpa [prefixWord, tailWord_240874, baseEnd_240874] using wordTrace_append hprefix tailTrace_240874
  have hstable : (prefixWord ++ tailWord_240874).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240874).length < 2 ^ (prefixWord ++ tailWord_240874).sum := by decide
  have hdescent : baseEnd_240874 < baseStart_240874 := by decide
  rcases family_descends (prefixWord ++ tailWord_240874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240895 : List Nat := [1, 1, 2, 2, 1, 5, 7]
def baseStart_240895 : Nat := 118140960795 + 240895 * 2 ^ 59
def prefixEnd_240895 : Nat := 4983230072969 + 3 ^ 40 * 240895 * 2
def baseEnd_240895 : Nat := 24433564891840045610795

theorem tailTrace_240895 : CollatzResearch.WordTrace tailWord_240895 prefixEnd_240895 24433564891840045610795 := by
  unfold tailWord_240895
  simp only [CollatzResearch.WordTrace]
  refine ⟨8786162462286031435660139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5857441641524020957106759 8786162462286031435660139)
  ·
    refine ⟨13179243693429047153490209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8786162462286031435660139 13179243693429047153490209)
    ·
      refine ⟨9884432770071785365117657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13179243693429047153490209 9884432770071785365117657)
      ·
        refine ⟨7413324577553839023838243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9884432770071785365117657 7413324577553839023838243)
        ·
          refine ⟨11119986866330758535757365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7413324577553839023838243 11119986866330758535757365)
          ·
            refine ⟨1042498768718508612727253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11119986866330758535757365 1042498768718508612727253)
            ·
              refine ⟨24433564891840045610795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1042498768718508612727253 24433564891840045610795)
              ·
                rfl

theorem cell19_240895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 7].length) (baseStart_240895 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_240895 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_240895 prefixEnd_240895 := by exact prefixLift 240895
  have htrace : WordTrace (prefixWord ++ tailWord_240895) baseStart_240895 baseEnd_240895 := by
    simpa [prefixWord, tailWord_240895, baseEnd_240895] using wordTrace_append hprefix tailTrace_240895
  have hstable : (prefixWord ++ tailWord_240895).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240895).length < 2 ^ (prefixWord ++ tailWord_240895).sum := by decide
  have hdescent : baseEnd_240895 < baseStart_240895 := by decide
  rcases family_descends (prefixWord ++ tailWord_240895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241045 : List Nat := [1, 3, 2, 1, 1, 2, 6, 3]
def baseStart_241045 : Nat := 118140960795 + 241045 * 2 ^ 59
def prefixEnd_241045 : Nat := 4983230072969 + 3 ^ 40 * 241045 * 2
def baseEnd_241045 : Nat := 73346337400364233498643

theorem tailTrace_241045 : CollatzResearch.WordTrace tailWord_241045 prefixEnd_241045 73346337400364233498643 := by
  unfold tailWord_241045
  simp only [CollatzResearch.WordTrace]
  refine ⟨8791633411742607053620589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5861088941161738035747059 8791633411742607053620589)
  ·
    refine ⟨3296862529403477645107721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8791633411742607053620589 3296862529403477645107721)
    ·
      refine ⟨2472646897052608233830791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3296862529403477645107721 2472646897052608233830791)
      ·
        refine ⟨3708970345578912350746187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2472646897052608233830791 3708970345578912350746187)
        ·
          refine ⟨5563455518368368526119281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3708970345578912350746187 5563455518368368526119281)
          ·
            refine ⟨4172591638776276394589461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5563455518368368526119281 4172591638776276394589461)
            ·
              refine ⟨195590233067637955996381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4172591638776276394589461 195590233067637955996381)
              ·
                refine ⟨73346337400364233498643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195590233067637955996381 73346337400364233498643)
                ·
                  rfl

theorem cell19_241045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 3].length) (baseStart_241045 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_241045 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_241045 prefixEnd_241045 := by exact prefixLift 241045
  have htrace : WordTrace (prefixWord ++ tailWord_241045) baseStart_241045 baseEnd_241045 := by
    simpa [prefixWord, tailWord_241045, baseEnd_241045] using wordTrace_append hprefix tailTrace_241045
  have hstable : (prefixWord ++ tailWord_241045).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241045).length < 2 ^ (prefixWord ++ tailWord_241045).sum := by decide
  have hdescent : baseEnd_241045 < baseStart_241045 := by decide
  rcases family_descends (prefixWord ++ tailWord_241045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241123 : List Nat := [1, 1, 1, 6, 2, 8]
def baseStart_241123 : Nat := 118140960795 + 241123 * 2 ^ 59
def prefixEnd_241123 : Nat := 4983230072969 + 3 ^ 40 * 241123 * 2
def baseEnd_241123 : Nat := 8152230179698129307233

theorem tailTrace_241123 : CollatzResearch.WordTrace tailWord_241123 prefixEnd_241123 8152230179698129307233 := by
  unfold tailWord_241123
  simp only [CollatzResearch.WordTrace]
  refine ⟨8794478305460026374960023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5862985536973350916640015 8794478305460026374960023)
  ·
    refine ⟨13191717458190039562440035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8794478305460026374960023 13191717458190039562440035)
    ·
      refine ⟨19787576187285059343660053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13191717458190039562440035 19787576187285059343660053)
      ·
        refine ⟨927542633778987156734065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19787576187285059343660053 927542633778987156734065)
        ·
          refine ⟨695656975334240367550549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 927542633778987156734065 695656975334240367550549)
          ·
            refine ⟨8152230179698129307233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 695656975334240367550549 8152230179698129307233)
            ·
              rfl

theorem cell19_241123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 8].length) (baseStart_241123 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_241123 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_241123 prefixEnd_241123 := by exact prefixLift 241123
  have htrace : WordTrace (prefixWord ++ tailWord_241123) baseStart_241123 baseEnd_241123 := by
    simpa [prefixWord, tailWord_241123, baseEnd_241123] using wordTrace_append hprefix tailTrace_241123
  have hstable : (prefixWord ++ tailWord_241123).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241123).length < 2 ^ (prefixWord ++ tailWord_241123).sum := by decide
  have hdescent : baseEnd_241123 < baseStart_241123 := by decide
  rcases family_descends (prefixWord ++ tailWord_241123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241138 : List Nat := [3, 2, 1, 4, 1, 3, 1, 4]
def baseStart_241138 : Nat := 118140960795 + 241138 * 2 ^ 59
def prefixEnd_241138 : Nat := 4983230072969 + 3 ^ 40 * 241138 * 2
def baseEnd_241138 : Nat := 73374635889767573431723

theorem tailTrace_241138 : CollatzResearch.WordTrace tailWord_241138 prefixEnd_241138 73374635889767573431723 := by
  unfold tailWord_241138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2198756350101420984189017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5863350266937122624504045 2198756350101420984189017)
  ·
    refine ⟨1649067262576065738141763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2198756350101420984189017 1649067262576065738141763)
    ·
      refine ⟨2473600893864098607212645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1649067262576065738141763 2473600893864098607212645)
      ·
        refine ⟨463800167599518488852371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2473600893864098607212645 463800167599518488852371)
        ·
          refine ⟨695700251399277733278557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463800167599518488852371 695700251399277733278557)
          ·
            refine ⟨260887594274729149979459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 695700251399277733278557 260887594274729149979459)
            ·
              refine ⟨391331391412093724969189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260887594274729149979459 391331391412093724969189)
              ·
                refine ⟨73374635889767573431723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 391331391412093724969189 73374635889767573431723)
                ·
                  rfl

theorem cell19_241138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_241138 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_241138 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_241138 prefixEnd_241138 := by exact prefixLift 241138
  have htrace : WordTrace (prefixWord ++ tailWord_241138) baseStart_241138 baseEnd_241138 := by
    simpa [prefixWord, tailWord_241138, baseEnd_241138] using wordTrace_append hprefix tailTrace_241138
  have hstable : (prefixWord ++ tailWord_241138).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241138).length < 2 ^ (prefixWord ++ tailWord_241138).sum := by decide
  have hdescent : baseEnd_241138 < baseStart_241138 := by decide
  rcases family_descends (prefixWord ++ tailWord_241138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241180 : List Nat := [2, 2, 3, 1, 2, 1, 8]
def baseStart_241180 : Nat := 118140960795 + 241180 * 2 ^ 59
def prefixEnd_241180 : Nat := 4983230072969 + 3 ^ 40 * 241180 * 2
def baseEnd_241180 : Nat := 24462471950907973499425

theorem tailTrace_241180 : CollatzResearch.WordTrace tailWord_241180 prefixEnd_241180 24462471950907973499425 := by
  unfold tailWord_241180
  simp only [CollatzResearch.WordTrace]
  refine ⟨4398278633126762554892497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5864371510835683406523329 4398278633126762554892497)
  ·
    refine ⟨3298708974845071916169373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4398278633126762554892497 3298708974845071916169373)
    ·
      refine ⟨1237015865566901968563515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3298708974845071916169373 1237015865566901968563515)
      ·
        refine ⟨1855523798350352952845273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1237015865566901968563515 1855523798350352952845273)
        ·
          refine ⟨1391642848762764714633955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1855523798350352952845273 1391642848762764714633955)
          ·
            refine ⟨2087464273144147071950933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391642848762764714633955 2087464273144147071950933)
            ·
              refine ⟨24462471950907973499425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2087464273144147071950933 24462471950907973499425)
              ·
                rfl

theorem cell19_241180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 8].length) (baseStart_241180 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_241180 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_241180 prefixEnd_241180 := by exact prefixLift 241180
  have htrace : WordTrace (prefixWord ++ tailWord_241180) baseStart_241180 baseEnd_241180 := by
    simpa [prefixWord, tailWord_241180, baseEnd_241180] using wordTrace_append hprefix tailTrace_241180
  have hstable : (prefixWord ++ tailWord_241180).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241180).length < 2 ^ (prefixWord ++ tailWord_241180).sum := by decide
  have hdescent : baseEnd_241180 < baseStart_241180 := by decide
  rcases family_descends (prefixWord ++ tailWord_241180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241212 : List Nat := [2, 2, 2, 2, 5, 1, 2, 3]
def baseStart_241212 : Nat := 118140960795 + 241212 * 2 ^ 59
def prefixEnd_241212 : Nat := 4983230072969 + 3 ^ 40 * 241212 * 2
def baseEnd_241212 : Nat := 73397152967357327787077

theorem tailTrace_241212 : CollatzResearch.WordTrace tailWord_241212 prefixEnd_241212 73397152967357327787077 := by
  unfold tailWord_241212
  simp only [CollatzResearch.WordTrace]
  refine ⟨4398862201068797287474945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5865149601425063049966593 4398862201068797287474945)
  ·
    refine ⟨3299146650801597965606209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4398862201068797287474945 3299146650801597965606209)
    ·
      refine ⟨2474359988101198474204657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3299146650801597965606209 2474359988101198474204657)
      ·
        refine ⟨1855769991075898855653493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2474359988101198474204657 1855769991075898855653493)
        ·
          refine ⟨173978436663365517717515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1855769991075898855653493 173978436663365517717515)
          ·
            refine ⟨260967654995048276576273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173978436663365517717515 260967654995048276576273)
            ·
              refine ⟨195725741246286207432205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260967654995048276576273 195725741246286207432205)
              ·
                refine ⟨73397152967357327787077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195725741246286207432205 73397152967357327787077)
                ·
                  rfl

theorem cell19_241212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 3].length) (baseStart_241212 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_241212 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_241212 prefixEnd_241212 := by exact prefixLift 241212
  have htrace : WordTrace (prefixWord ++ tailWord_241212) baseStart_241212 baseEnd_241212 := by
    simpa [prefixWord, tailWord_241212, baseEnd_241212] using wordTrace_append hprefix tailTrace_241212
  have hstable : (prefixWord ++ tailWord_241212).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241212).length < 2 ^ (prefixWord ++ tailWord_241212).sum := by decide
  have hdescent : baseEnd_241212 < baseStart_241212 := by decide
  rcases family_descends (prefixWord ++ tailWord_241212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241294 : List Nat := [4, 1, 1, 3, 1, 9]
def baseStart_241294 : Nat := 118140960795 + 241294 * 2 ^ 59
def prefixEnd_241294 : Nat := 4983230072969 + 3 ^ 40 * 241294 * 2
def baseEnd_241294 : Nat := 8158011591511714884959

theorem tailTrace_241294 : CollatzResearch.WordTrace tailWord_241294 prefixEnd_241294 8158011591511714884959 := by
  unfold tailWord_241294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1100089398480065322429367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5867143458560348386289957 1100089398480065322429367)
  ·
    refine ⟨1650134097720097983644051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1100089398480065322429367 1650134097720097983644051)
    ·
      refine ⟨2475201146580146975466077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1650134097720097983644051 2475201146580146975466077)
      ·
        refine ⟨928200429967555115799779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2475201146580146975466077 928200429967555115799779)
        ·
          refine ⟨1392300644951332673699669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928200429967555115799779 1392300644951332673699669)
          ·
            refine ⟨8158011591511714884959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1392300644951332673699669 8158011591511714884959)
            ·
              rfl

theorem cell19_241294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 9].length) (baseStart_241294 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_241294 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_241294 prefixEnd_241294 := by exact prefixLift 241294
  have htrace : WordTrace (prefixWord ++ tailWord_241294) baseStart_241294 baseEnd_241294 := by
    simpa [prefixWord, tailWord_241294, baseEnd_241294] using wordTrace_append hprefix tailTrace_241294
  have hstable : (prefixWord ++ tailWord_241294).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241294).length < 2 ^ (prefixWord ++ tailWord_241294).sum := by decide
  have hdescent : baseEnd_241294 < baseStart_241294 := by decide
  rcases family_descends (prefixWord ++ tailWord_241294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241326 : List Nat := [4, 1, 4, 1, 2, 1, 3, 3]
def baseStart_241326 : Nat := 118140960795 + 241326 * 2 ^ 59
def prefixEnd_241326 : Nat := 4983230072969 + 3 ^ 40 * 241326 * 2
def baseEnd_241326 : Nat := 73431841438238841253433

theorem tailTrace_241326 : CollatzResearch.WordTrace tailWord_241326 prefixEnd_241326 73431841438238841253433 := by
  unfold tailWord_241326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1100235290465574005574979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5867921549149728029733221 1100235290465574005574979)
  ·
    refine ⟨1650352935698361008362469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1100235290465574005574979 1650352935698361008362469)
    ·
      refine ⟨309441175443442689067963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1650352935698361008362469 309441175443442689067963)
      ·
        refine ⟨464161763165164033601945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309441175443442689067963 464161763165164033601945)
        ·
          refine ⟨348121322373873025201459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464161763165164033601945 348121322373873025201459)
          ·
            refine ⟨522181983560809537802189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348121322373873025201459 522181983560809537802189)
            ·
              refine ⟨195818243835303576675821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 522181983560809537802189 195818243835303576675821)
              ·
                refine ⟨73431841438238841253433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195818243835303576675821 73431841438238841253433)
                ·
                  rfl

theorem cell19_241326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_241326 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_241326 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_241326 prefixEnd_241326 := by exact prefixLift 241326
  have htrace : WordTrace (prefixWord ++ tailWord_241326) baseStart_241326 baseEnd_241326 := by
    simpa [prefixWord, tailWord_241326, baseEnd_241326] using wordTrace_append hprefix tailTrace_241326
  have hstable : (prefixWord ++ tailWord_241326).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241326).length < 2 ^ (prefixWord ++ tailWord_241326).sum := by decide
  have hdescent : baseEnd_241326 < baseStart_241326 := by decide
  rcases family_descends (prefixWord ++ tailWord_241326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241383 : List Nat := [1, 1, 5, 4, 1, 2, 2, 3]
def baseStart_241383 : Nat := 118140960795 + 241383 * 2 ^ 59
def prefixEnd_241383 : Nat := 4983230072969 + 3 ^ 40 * 241383 * 2
def baseEnd_241383 : Nat := 73449185673679597986611

theorem tailTrace_241383 : CollatzResearch.WordTrace tailWord_241383 prefixEnd_241383 73449185673679597986611 := by
  unfold tailWord_241383
  simp only [CollatzResearch.WordTrace]
  refine ⟨8803961284518090779424803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5869307523012060519616535 8803961284518090779424803)
  ·
    refine ⟨13205941926777136169137205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8803961284518090779424803 13205941926777136169137205)
    ·
      refine ⟨1238057055635356515856613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13205941926777136169137205 1238057055635356515856613)
      ·
        refine ⟨232135697931629346723115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1238057055635356515856613 232135697931629346723115)
        ·
          refine ⟨348203546897444020084673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232135697931629346723115 348203546897444020084673)
          ·
            refine ⟨261152660173083015063505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348203546897444020084673 261152660173083015063505)
            ·
              refine ⟨195864495129812261297629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261152660173083015063505 195864495129812261297629)
              ·
                refine ⟨73449185673679597986611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195864495129812261297629 73449185673679597986611)
                ·
                  rfl

theorem cell19_241383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 3].length) (baseStart_241383 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_241383 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_241383 prefixEnd_241383 := by exact prefixLift 241383
  have htrace : WordTrace (prefixWord ++ tailWord_241383) baseStart_241383 baseEnd_241383 := by
    simpa [prefixWord, tailWord_241383, baseEnd_241383] using wordTrace_append hprefix tailTrace_241383
  have hstable : (prefixWord ++ tailWord_241383).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241383).length < 2 ^ (prefixWord ++ tailWord_241383).sum := by decide
  have hdescent : baseEnd_241383 < baseStart_241383 := by decide
  rcases family_descends (prefixWord ++ tailWord_241383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241465 : List Nat := [1, 2, 1, 7, 8]
def baseStart_241465 : Nat := 118140960795 + 241465 * 2 ^ 59
def prefixEnd_241465 : Nat := 4983230072969 + 3 ^ 40 * 241465 * 2
def baseEnd_241465 : Nat := 2721264334441766820895

theorem tailTrace_241465 : CollatzResearch.WordTrace tailWord_241465 prefixEnd_241465 2721264334441766820895 := by
  unfold tailWord_241465
  simp only [CollatzResearch.WordTrace]
  refine ⟨8806952070221018783909849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5871301380147345855939899 8806952070221018783909849)
  ·
    refine ⟨6605214052665764087932387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8806952070221018783909849 6605214052665764087932387)
    ·
      refine ⟨9907821078998646131898581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6605214052665764087932387 9907821078998646131898581)
      ·
        refine ⟨232214556539030768716373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 9907821078998646131898581 232214556539030768716373)
        ·
          refine ⟨2721264334441766820895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 232214556539030768716373 2721264334441766820895)
          ·
            rfl

theorem cell19_241465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 8].length) (baseStart_241465 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_241465 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_241465 prefixEnd_241465 := by exact prefixLift 241465
  have htrace : WordTrace (prefixWord ++ tailWord_241465) baseStart_241465 baseEnd_241465 := by
    simpa [prefixWord, tailWord_241465, baseEnd_241465] using wordTrace_append hprefix tailTrace_241465
  have hstable : (prefixWord ++ tailWord_241465).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241465).length < 2 ^ (prefixWord ++ tailWord_241465).sum := by decide
  have hdescent : baseEnd_241465 < baseStart_241465 := by decide
  rcases family_descends (prefixWord ++ tailWord_241465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241478 : List Nat := [6, 1, 1, 2, 1, 3, 1, 4]
def baseStart_241478 : Nat := 118140960795 + 241478 * 2 ^ 59
def prefixEnd_241478 : Nat := 4983230072969 + 3 ^ 40 * 241478 * 2
def baseEnd_241478 : Nat := 73478092732747525875241

theorem tailTrace_241478 : CollatzResearch.WordTrace tailWord_241478 prefixEnd_241478 73478092732747525875241 := by
  unfold tailWord_241478
  simp only [CollatzResearch.WordTrace]
  refine ⟨275232069349185062629159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5871617479449281336088725 275232069349185062629159)
  ·
    refine ⟨412848104023777593943739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 275232069349185062629159 412848104023777593943739)
    ·
      refine ⟨619272156035666390915609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 412848104023777593943739 619272156035666390915609)
      ·
        refine ⟨464454117026749793186707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 619272156035666390915609 464454117026749793186707)
        ·
          refine ⟨696681175540124689780061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464454117026749793186707 696681175540124689780061)
          ·
            refine ⟨261255440827546758667523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 696681175540124689780061 261255440827546758667523)
            ·
              refine ⟨391883161241320138001285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261255440827546758667523 391883161241320138001285)
              ·
                refine ⟨73478092732747525875241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 391883161241320138001285 73478092732747525875241)
                ·
                  rfl

theorem cell19_241478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_241478 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_241478 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_241478 prefixEnd_241478 := by exact prefixLift 241478
  have htrace : WordTrace (prefixWord ++ tailWord_241478) baseStart_241478 baseEnd_241478 := by
    simpa [prefixWord, tailWord_241478, baseEnd_241478] using wordTrace_append hprefix tailTrace_241478
  have hstable : (prefixWord ++ tailWord_241478).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241478).length < 2 ^ (prefixWord ++ tailWord_241478).sum := by decide
  have hdescent : baseEnd_241478 < baseStart_241478 := by decide
  rcases family_descends (prefixWord ++ tailWord_241478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241556 : List Nat := [2, 4, 2, 1, 1, 4, 2, 3]
def baseStart_241556 : Nat := 118140960795 + 241556 * 2 ^ 59
def prefixEnd_241556 : Nat := 4983230072969 + 3 ^ 40 * 241556 * 2
def baseEnd_241556 : Nat := 73501826949666456141695

theorem tailTrace_241556 : CollatzResearch.WordTrace tailWord_241556 prefixEnd_241556 73501826949666456141695 := by
  unfold tailWord_241556
  simp only [CollatzResearch.WordTrace]
  refine ⟨4405135556445670662736261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5873514075260894216981681 4405135556445670662736261)
  ·
    refine ⟨825962916833563249263049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4405135556445670662736261 825962916833563249263049)
    ·
      refine ⟨619472187625172436947287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 825962916833563249263049 619472187625172436947287)
      ·
        refine ⟨929208281437758655420931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619472187625172436947287 929208281437758655420931)
        ·
          refine ⟨1393812422156637983131397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929208281437758655420931 1393812422156637983131397)
          ·
            refine ⟨261339829154369621837137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1393812422156637983131397 261339829154369621837137)
            ·
              refine ⟨196004871865777216377853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261339829154369621837137 196004871865777216377853)
              ·
                refine ⟨73501826949666456141695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196004871865777216377853 73501826949666456141695)
                ·
                  rfl

theorem cell19_241556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 3].length) (baseStart_241556 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_241556 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_241556 prefixEnd_241556 := by exact prefixLift 241556
  have htrace : WordTrace (prefixWord ++ tailWord_241556) baseStart_241556 baseEnd_241556 := by
    simpa [prefixWord, tailWord_241556, baseEnd_241556] using wordTrace_append hprefix tailTrace_241556
  have hstable : (prefixWord ++ tailWord_241556).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241556).length < 2 ^ (prefixWord ++ tailWord_241556).sum := by decide
  have hdescent : baseEnd_241556 < baseStart_241556 := by decide
  rcases family_descends (prefixWord ++ tailWord_241556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241598 : List Nat := [4, 2, 1, 1, 1, 3, 1, 6]
def baseStart_241598 : Nat := 118140960795 + 241598 * 2 ^ 59
def prefixEnd_241598 : Nat := 4983230072969 + 3 ^ 40 * 241598 * 2
def baseEnd_241598 : Nat := 73514606912622803208247

theorem tailTrace_241598 : CollatzResearch.WordTrace tailWord_241598 prefixEnd_241598 73514606912622803208247 := by
  unfold tailWord_241598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1101475372342397812312681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5874535319159454999000965 1101475372342397812312681)
  ·
    refine ⟨826106529256798359234511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1101475372342397812312681 826106529256798359234511)
    ·
      refine ⟨1239159793885197538851767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 826106529256798359234511 1239159793885197538851767)
      ·
        refine ⟨1858739690827796308277651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1239159793885197538851767 1858739690827796308277651)
        ·
          refine ⟨2788109536241694462416477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1858739690827796308277651 2788109536241694462416477)
          ·
            refine ⟨1045541076090635423406179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2788109536241694462416477 1045541076090635423406179)
            ·
              refine ⟨1568311614135953135109269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045541076090635423406179 1568311614135953135109269)
              ·
                refine ⟨73514606912622803208247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1568311614135953135109269 73514606912622803208247)
                ·
                  rfl

theorem cell19_241598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_241598 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_241598 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_241598 prefixEnd_241598 := by exact prefixLift 241598
  have htrace : WordTrace (prefixWord ++ tailWord_241598) baseStart_241598 baseEnd_241598 := by
    simpa [prefixWord, tailWord_241598, baseEnd_241598] using wordTrace_append hprefix tailTrace_241598
  have hstable : (prefixWord ++ tailWord_241598).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241598).length < 2 ^ (prefixWord ++ tailWord_241598).sum := by decide
  have hdescent : baseEnd_241598 < baseStart_241598 := by decide
  rcases family_descends (prefixWord ++ tailWord_241598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241634 : List Nat := [3, 3, 3, 1, 2, 7]
def baseStart_241634 : Nat := 118140960795 + 241634 * 2 ^ 59
def prefixEnd_241634 : Nat := 4983230072969 + 3 ^ 40 * 241634 * 2
def baseEnd_241634 : Nat := 8169506796287265156461

theorem tailTrace_241634 : CollatzResearch.WordTrace tailWord_241634 prefixEnd_241634 8169506796287265156461 := by
  unfold tailWord_241634
  simp only [CollatzResearch.WordTrace]
  refine ⟨2203279001652190161702989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5875410671072507097874637 2203279001652190161702989)
  ·
    refine ⟨826229625619571310638621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2203279001652190161702989 826229625619571310638621)
    ·
      refine ⟨309836109607339241489483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 826229625619571310638621 309836109607339241489483)
      ·
        refine ⟨464754164411008862234225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309836109607339241489483 464754164411008862234225)
        ·
          refine ⟨348565623308256646675669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464754164411008862234225 348565623308256646675669)
          ·
            refine ⟨8169506796287265156461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 348565623308256646675669 8169506796287265156461)
            ·
              rfl

theorem cell19_241634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 7].length) (baseStart_241634 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_241634 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_241634 prefixEnd_241634 := by exact prefixLift 241634
  have htrace : WordTrace (prefixWord ++ tailWord_241634) baseStart_241634 baseEnd_241634 := by
    simpa [prefixWord, tailWord_241634, baseEnd_241634] using wordTrace_append hprefix tailTrace_241634
  have hstable : (prefixWord ++ tailWord_241634).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241634).length < 2 ^ (prefixWord ++ tailWord_241634).sum := by decide
  have hdescent : baseEnd_241634 < baseStart_241634 := by decide
  rcases family_descends (prefixWord ++ tailWord_241634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241693 : List Nat := [1, 4, 2, 2, 2, 2, 6]
def baseStart_241693 : Nat := 118140960795 + 241693 * 2 ^ 59
def prefixEnd_241693 : Nat := 4983230072969 + 3 ^ 40 * 241693 * 2
def baseEnd_241693 : Nat := 24514504657230243698959

theorem tailTrace_241693 : CollatzResearch.WordTrace tailWord_241693 prefixEnd_241693 24514504657230243698959 := by
  unfold tailWord_241693
  simp only [CollatzResearch.WordTrace]
  refine ⟨8815267913395013723209733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5876845275596675815473155 8815267913395013723209733)
  ·
    refine ⟨1652862733761565073101825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8815267913395013723209733 1652862733761565073101825)
    ·
      refine ⟨1239647050321173804826369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1652862733761565073101825 1239647050321173804826369)
      ·
        refine ⟨929735287740880353619777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1239647050321173804826369 929735287740880353619777)
        ·
          refine ⟨697301465805660265214833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 929735287740880353619777 697301465805660265214833)
          ·
            refine ⟨522976099354245198911125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 697301465805660265214833 522976099354245198911125)
            ·
              refine ⟨24514504657230243698959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 522976099354245198911125 24514504657230243698959)
              ·
                rfl

theorem cell19_241693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 6].length) (baseStart_241693 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_241693 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_241693 prefixEnd_241693 := by exact prefixLift 241693
  have htrace : WordTrace (prefixWord ++ tailWord_241693) baseStart_241693 baseEnd_241693 := by
    simpa [prefixWord, tailWord_241693, baseEnd_241693] using wordTrace_append hprefix tailTrace_241693
  have hstable : (prefixWord ++ tailWord_241693).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241693).length < 2 ^ (prefixWord ++ tailWord_241693).sum := by decide
  have hdescent : baseEnd_241693 < baseStart_241693 := by decide
  rcases family_descends (prefixWord ++ tailWord_241693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241695 : List Nat := [1, 1, 2, 4, 1, 2, 8]
def baseStart_241695 : Nat := 118140960795 + 241695 * 2 ^ 59
def prefixEnd_241695 : Nat := 4983230072969 + 3 ^ 40 * 241695 * 2
def baseEnd_241695 : Nat := 24514707513785106350809

theorem tailTrace_241695 : CollatzResearch.WordTrace tailWord_241695 prefixEnd_241695 24514707513785106350809 := by
  unfold tailWord_241695
  simp only [CollatzResearch.WordTrace]
  refine ⟨8815340859387768064782539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5876893906258512043188359 8815340859387768064782539)
  ·
    refine ⟨13223011289081652097173809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8815340859387768064782539 13223011289081652097173809)
    ·
      refine ⟨9917258466811239072880357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13223011289081652097173809 9917258466811239072880357)
      ·
        refine ⟨1859485962527107326165067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9917258466811239072880357 1859485962527107326165067)
        ·
          refine ⟨2789228943790660989247601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1859485962527107326165067 2789228943790660989247601)
          ·
            refine ⟨2091921707842995741935701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2789228943790660989247601 2091921707842995741935701)
            ·
              refine ⟨24514707513785106350809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2091921707842995741935701 24514707513785106350809)
              ·
                rfl

theorem cell19_241695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 8].length) (baseStart_241695 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_241695 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_241695 prefixEnd_241695 := by exact prefixLift 241695
  have htrace : WordTrace (prefixWord ++ tailWord_241695) baseStart_241695 baseEnd_241695 := by
    simpa [prefixWord, tailWord_241695, baseEnd_241695] using wordTrace_append hprefix tailTrace_241695
  have hstable : (prefixWord ++ tailWord_241695).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241695).length < 2 ^ (prefixWord ++ tailWord_241695).sum := by decide
  have hdescent : baseEnd_241695 < baseStart_241695 := by decide
  rcases family_descends (prefixWord ++ tailWord_241695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241729 : List Nat := [1, 2, 5, 1, 2, 1, 4, 3]
def baseStart_241729 : Nat := 118140960795 + 241729 * 2 ^ 59
def prefixEnd_241729 : Nat := 4983230072969 + 3 ^ 40 * 241729 * 2
def baseEnd_241729 : Nat := 73554468225653314296779

theorem tailTrace_241729 : CollatzResearch.WordTrace tailWord_241729 prefixEnd_241729 73554468225653314296779 := by
  unfold tailWord_241729
  simp only [CollatzResearch.WordTrace]
  refine ⟨8816580941264591871520241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5877720627509727914346827 8816580941264591871520241)
  ·
    refine ⟨6612435705948443903640181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8816580941264591871520241 6612435705948443903640181)
    ·
      refine ⟨619915847432666615966267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6612435705948443903640181 619915847432666615966267)
      ·
        refine ⟨929873771148999923949401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619915847432666615966267 929873771148999923949401)
        ·
          refine ⟨697405328361749942962051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 929873771148999923949401 697405328361749942962051)
          ·
            refine ⟨1046107992542624914443077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697405328361749942962051 1046107992542624914443077)
            ·
              refine ⟨196145248601742171458077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1046107992542624914443077 196145248601742171458077)
              ·
                refine ⟨73554468225653314296779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196145248601742171458077 73554468225653314296779)
                ·
                  rfl

theorem cell19_241729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 3].length) (baseStart_241729 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_241729 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_241729 prefixEnd_241729 := by exact prefixLift 241729
  have htrace : WordTrace (prefixWord ++ tailWord_241729) baseStart_241729 baseEnd_241729 := by
    simpa [prefixWord, tailWord_241729, baseEnd_241729] using wordTrace_append hprefix tailTrace_241729
  have hstable : (prefixWord ++ tailWord_241729).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241729).length < 2 ^ (prefixWord ++ tailWord_241729).sum := by decide
  have hdescent : baseEnd_241729 < baseStart_241729 := by decide
  rcases family_descends (prefixWord ++ tailWord_241729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241752 : List Nat := [2, 1, 2, 2, 1, 4, 7]
def baseStart_241752 : Nat := 118140960795 + 241752 * 2 ^ 59
def prefixEnd_241752 : Nat := 4983230072969 + 3 ^ 40 * 241752 * 2
def baseEnd_241752 : Nat := 24520488925598691928535

theorem tailTrace_241752 : CollatzResearch.WordTrace tailWord_241752 prefixEnd_241752 24520488925598691928535 := by
  unfold tailWord_241752
  simp only [CollatzResearch.WordTrace]
  refine ⟨4408709910090633399803755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5878279880120844533071673 4408709910090633399803755)
  ·
    refine ⟨6613064865135950099705633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4408709910090633399803755 6613064865135950099705633)
    ·
      refine ⟨4959798648851962574779225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6613064865135950099705633 4959798648851962574779225)
      ·
        refine ⟨3719848986638971931084419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4959798648851962574779225 3719848986638971931084419)
        ·
          refine ⟨5579773479958457896626629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3719848986638971931084419 5579773479958457896626629)
          ·
            refine ⟨1046207527492210855617493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5579773479958457896626629 1046207527492210855617493)
            ·
              refine ⟨24520488925598691928535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1046207527492210855617493 24520488925598691928535)
              ·
                rfl

theorem cell19_241752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 7].length) (baseStart_241752 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_241752 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_241752 prefixEnd_241752 := by exact prefixLift 241752
  have htrace : WordTrace (prefixWord ++ tailWord_241752) baseStart_241752 baseEnd_241752 := by
    simpa [prefixWord, tailWord_241752, baseEnd_241752] using wordTrace_append hprefix tailTrace_241752
  have hstable : (prefixWord ++ tailWord_241752).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241752).length < 2 ^ (prefixWord ++ tailWord_241752).sum := by decide
  have hdescent : baseEnd_241752 < baseStart_241752 := by decide
  rcases family_descends (prefixWord ++ tailWord_241752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241822 : List Nat := [4, 3, 1, 1, 3, 2, 1, 4]
def baseStart_241822 : Nat := 118140960795 + 241822 * 2 ^ 59
def prefixEnd_241822 : Nat := 4983230072969 + 3 ^ 40 * 241822 * 2
def baseEnd_241822 : Nat := 73582766715056654229859

theorem tailTrace_241822 : CollatzResearch.WordTrace tailWord_241822 prefixEnd_241822 73582766715056654229859 := by
  unfold tailWord_241822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1102496616240958594331965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5879981953285112503103813 1102496616240958594331965)
  ·
    refine ⟨413436231090359472874487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1102496616240958594331965 413436231090359472874487)
    ·
      refine ⟨620154346635539209311731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 413436231090359472874487 620154346635539209311731)
      ·
        refine ⟨930231519953308813967597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 620154346635539209311731 930231519953308813967597)
        ·
          refine ⟨348836819982490805237849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 930231519953308813967597 348836819982490805237849)
          ·
            refine ⟨261627614986868103928387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348836819982490805237849 261627614986868103928387)
            ·
              refine ⟨392441422480302155892581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261627614986868103928387 392441422480302155892581)
              ·
                refine ⟨73582766715056654229859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 392441422480302155892581 73582766715056654229859)
                ·
                  rfl

theorem cell19_241822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_241822 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_241822 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_241822 prefixEnd_241822 := by exact prefixLift 241822
  have htrace : WordTrace (prefixWord ++ tailWord_241822) baseStart_241822 baseEnd_241822 := by
    simpa [prefixWord, tailWord_241822, baseEnd_241822] using wordTrace_append hprefix tailTrace_241822
  have hstable : (prefixWord ++ tailWord_241822).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241822).length < 2 ^ (prefixWord ++ tailWord_241822).sum := by decide
  have hdescent : baseEnd_241822 < baseStart_241822 := by decide
  rcases family_descends (prefixWord ++ tailWord_241822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241866 : List Nat := [3, 1, 2, 1, 3, 1, 8]
def baseStart_241866 : Nat := 118140960795 + 241866 * 2 ^ 59
def prefixEnd_241866 : Nat := 4983230072969 + 3 ^ 40 * 241866 * 2
def baseEnd_241866 : Nat := 24532051749225863083987

theorem tailTrace_241866 : CollatzResearch.WordTrace tailWord_241866 prefixEnd_241866 24532051749225863083987 := by
  unfold tailWord_241866
  simp only [CollatzResearch.WordTrace]
  refine ⟨2205394435442066067314363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5881051827845509512838301 2205394435442066067314363)
  ·
    refine ⟨3308091653163099100971545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2205394435442066067314363 3308091653163099100971545)
    ·
      refine ⟨2481068739872324325728659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3308091653163099100971545 2481068739872324325728659)
      ·
        refine ⟨3721603109808486488592989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2481068739872324325728659 3721603109808486488592989)
        ·
          refine ⟨1395601166178182433222371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3721603109808486488592989 1395601166178182433222371)
          ·
            refine ⟨2093401749267273649833557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1395601166178182433222371 2093401749267273649833557)
            ·
              refine ⟨24532051749225863083987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2093401749267273649833557 24532051749225863083987)
              ·
                rfl

theorem cell19_241866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 8].length) (baseStart_241866 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_241866 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_241866 prefixEnd_241866 := by exact prefixLift 241866
  have htrace : WordTrace (prefixWord ++ tailWord_241866) baseStart_241866 baseEnd_241866 := by
    simpa [prefixWord, tailWord_241866, baseEnd_241866] using wordTrace_append hprefix tailTrace_241866
  have hstable : (prefixWord ++ tailWord_241866).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241866).length < 2 ^ (prefixWord ++ tailWord_241866).sum := by decide
  have hdescent : baseEnd_241866 < baseStart_241866 := by decide
  rcases family_descends (prefixWord ++ tailWord_241866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242012 : List Nat := [2, 2, 4, 3, 1, 1, 3, 3]
def baseStart_242012 : Nat := 118140960795 + 242012 * 2 ^ 59
def prefixEnd_242012 : Nat := 4983230072969 + 3 ^ 40 * 242012 * 2
def baseEnd_242012 : Nat := 73640580833192510007119

theorem tailTrace_242012 : CollatzResearch.WordTrace tailWord_242012 prefixEnd_242012 73640580833192510007119 := by
  unfold tailWord_242012
  simp only [CollatzResearch.WordTrace]
  refine ⟨4413451399619665602036145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5884601866159554136048193 4413451399619665602036145)
  ·
    refine ⟨3310088549714749201527109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4413451399619665602036145 3310088549714749201527109)
    ·
      refine ⟨620641603071515475286333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3310088549714749201527109 620641603071515475286333)
      ·
        refine ⟨232740601151818303232375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 620641603071515475286333 232740601151818303232375)
        ·
          refine ⟨349110901727727454848563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232740601151818303232375 349110901727727454848563)
          ·
            refine ⟨523666352591591182272845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349110901727727454848563 523666352591591182272845)
            ·
              refine ⟨196374882221846693352317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 523666352591591182272845 196374882221846693352317)
              ·
                refine ⟨73640580833192510007119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196374882221846693352317 73640580833192510007119)
                ·
                  rfl

theorem cell19_242012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 3].length) (baseStart_242012 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242012 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242012 prefixEnd_242012 := by exact prefixLift 242012
  have htrace : WordTrace (prefixWord ++ tailWord_242012) baseStart_242012 baseEnd_242012 := by
    simpa [prefixWord, tailWord_242012, baseEnd_242012] using wordTrace_append hprefix tailTrace_242012
  have hstable : (prefixWord ++ tailWord_242012).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242012).length < 2 ^ (prefixWord ++ tailWord_242012).sum := by decide
  have hdescent : baseEnd_242012 < baseStart_242012 := by decide
  rcases family_descends (prefixWord ++ tailWord_242012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242056 : List Nat := [2, 1, 3, 3, 1, 1, 2, 6]
def baseStart_242056 : Nat := 118140960795 + 242056 * 2 ^ 59
def prefixEnd_242056 : Nat := 4983230072969 + 3 ^ 40 * 242056 * 2
def baseEnd_242056 : Nat := 73653969365813445029221

theorem tailTrace_242056 : CollatzResearch.WordTrace tailWord_242056 prefixEnd_242056 73653969365813445029221 := by
  unfold tailWord_242056
  simp only [CollatzResearch.WordTrace]
  refine ⟨4414253805539963359337011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5885671740719951145782681 4414253805539963359337011)
  ·
    refine ⟨6621380708309945039005517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4414253805539963359337011 6621380708309945039005517)
    ·
      refine ⟨2483017765616229389627069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6621380708309945039005517 2483017765616229389627069)
      ·
        refine ⟨931131662106086021110151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2483017765616229389627069 931131662106086021110151)
        ·
          refine ⟨1396697493159129031665227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931131662106086021110151 1396697493159129031665227)
          ·
            refine ⟨2095046239738693547497841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396697493159129031665227 2095046239738693547497841)
            ·
              refine ⟨1571284679804020160623381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2095046239738693547497841 1571284679804020160623381)
              ·
                refine ⟨73653969365813445029221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1571284679804020160623381 73653969365813445029221)
                ·
                  rfl

theorem cell19_242056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_242056 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242056 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242056 prefixEnd_242056 := by exact prefixLift 242056
  have htrace : WordTrace (prefixWord ++ tailWord_242056) baseStart_242056 baseEnd_242056 := by
    simpa [prefixWord, tailWord_242056, baseEnd_242056] using wordTrace_append hprefix tailTrace_242056
  have hstable : (prefixWord ++ tailWord_242056).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242056).length < 2 ^ (prefixWord ++ tailWord_242056).sum := by decide
  have hdescent : baseEnd_242056 < baseStart_242056 := by decide
  rcases family_descends (prefixWord ++ tailWord_242056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242149 : List Nat := [1, 3, 1, 5, 3, 6]
def baseStart_242149 : Nat := 118140960795 + 242149 * 2 ^ 59
def prefixEnd_242149 : Nat := 4983230072969 + 3 ^ 40 * 242149 * 2
def baseEnd_242149 : Nat := 8186918650579642773589

theorem tailTrace_242149 : CollatzResearch.WordTrace tailWord_242149 prefixEnd_242149 8186918650579642773589 := by
  unfold tailWord_242149
  simp only [CollatzResearch.WordTrace]
  refine ⟨8831899599743003601809501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5887933066495335734539667 8831899599743003601809501)
  ·
    refine ⟨3311962349903626350678563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8831899599743003601809501 3311962349903626350678563)
    ·
      refine ⟨4967943524855439526017845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3311962349903626350678563 4967943524855439526017845)
      ·
        refine ⟨465744705455197455564173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4967943524855439526017845 465744705455197455564173)
        ·
          refine ⟨174654264545699045836565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 465744705455197455564173 174654264545699045836565)
          ·
            refine ⟨8186918650579642773589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 174654264545699045836565 8186918650579642773589)
            ·
              rfl

theorem cell19_242149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 6].length) (baseStart_242149 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242149 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242149 prefixEnd_242149 := by exact prefixLift 242149
  have htrace : WordTrace (prefixWord ++ tailWord_242149) baseStart_242149 baseEnd_242149 := by
    simpa [prefixWord, tailWord_242149, baseEnd_242149] using wordTrace_append hprefix tailTrace_242149
  have hstable : (prefixWord ++ tailWord_242149).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242149).length < 2 ^ (prefixWord ++ tailWord_242149).sum := by decide
  have hdescent : baseEnd_242149 < baseStart_242149 := by decide
  rcases family_descends (prefixWord ++ tailWord_242149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242187 : List Nat := [1, 1, 1, 1, 7, 2, 3, 3]
def baseStart_242187 : Nat := 118140960795 + 242187 * 2 ^ 59
def prefixEnd_242187 : Nat := 4983230072969 + 3 ^ 40 * 242187 * 2
def baseEnd_242187 : Nat := 73693830678843956117753

theorem tailTrace_242187 : CollatzResearch.WordTrace tailWord_242187 prefixEnd_242187 73693830678843956117753 := by
  unfold tailWord_242187
  simp only [CollatzResearch.WordTrace]
  refine ⟨8833285573605336091692815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5888857049070224061128543 8833285573605336091692815)
  ·
    refine ⟨13249928360408004137539223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8833285573605336091692815 13249928360408004137539223)
    ·
      refine ⟨19874892540612006206308835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13249928360408004137539223 19874892540612006206308835)
      ·
        refine ⟨29812338810918009309463253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19874892540612006206308835 29812338810918009309463253)
        ·
          refine ⟨698726690880890843190545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 29812338810918009309463253 698726690880890843190545)
          ·
            refine ⟨524045018160668132392909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 698726690880890843190545 524045018160668132392909)
            ·
              refine ⟨196516881810250549647341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 524045018160668132392909 196516881810250549647341)
              ·
                refine ⟨73693830678843956117753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196516881810250549647341 73693830678843956117753)
                ·
                  rfl

theorem cell19_242187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 3].length) (baseStart_242187 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242187 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242187 prefixEnd_242187 := by exact prefixLift 242187
  have htrace : WordTrace (prefixWord ++ tailWord_242187) baseStart_242187 baseEnd_242187 := by
    simpa [prefixWord, tailWord_242187, baseEnd_242187] using wordTrace_append hprefix tailTrace_242187
  have hstable : (prefixWord ++ tailWord_242187).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242187).length < 2 ^ (prefixWord ++ tailWord_242187).sum := by decide
  have hdescent : baseEnd_242187 < baseStart_242187 := by decide
  rcases family_descends (prefixWord ++ tailWord_242187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242238 : List Nat := [4, 2, 1, 4, 2, 1, 2, 3]
def baseStart_242238 : Nat := 118140960795 + 242238 * 2 ^ 59
def prefixEnd_242238 : Nat := 4983230072969 + 3 ^ 40 * 242238 * 2
def baseEnd_242238 : Nat := 73709349205290948984281

theorem tailTrace_242238 : CollatzResearch.WordTrace tailWord_242238 prefixEnd_242238 73709349205290948984281 := by
  unfold tailWord_242238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1104393212052571475224921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5890097130947047867866245 1104393212052571475224921)
  ·
    refine ⟨828294909039428606418691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1104393212052571475224921 828294909039428606418691)
    ·
      refine ⟨1242442363559142909628037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 828294909039428606418691 1242442363559142909628037)
      ·
        refine ⟨232957943167339295555257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1242442363559142909628037 232957943167339295555257)
        ·
          refine ⟨174718457375504471666443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232957943167339295555257 174718457375504471666443)
          ·
            refine ⟨262077686063256707499665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174718457375504471666443 262077686063256707499665)
            ·
              refine ⟨196558264547442530624749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262077686063256707499665 196558264547442530624749)
              ·
                refine ⟨73709349205290948984281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196558264547442530624749 73709349205290948984281)
                ·
                  rfl

theorem cell19_242238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_242238 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242238 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242238 prefixEnd_242238 := by exact prefixLift 242238
  have htrace : WordTrace (prefixWord ++ tailWord_242238) baseStart_242238 baseEnd_242238 := by
    simpa [prefixWord, tailWord_242238, baseEnd_242238] using wordTrace_append hprefix tailTrace_242238
  have hstable : (prefixWord ++ tailWord_242238).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242238).length < 2 ^ (prefixWord ++ tailWord_242238).sum := by decide
  have hdescent : baseEnd_242238 < baseStart_242238 := by decide
  rcases family_descends (prefixWord ++ tailWord_242238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242322 : List Nat := [3, 2, 3, 1, 2, 8]
def baseStart_242322 : Nat := 118140960795 + 242322 * 2 ^ 59
def prefixEnd_242322 : Nat := 4983230072969 + 3 ^ 40 * 242322 * 2
def baseEnd_242322 : Nat := 8192767681244849235265

theorem tailTrace_242322 : CollatzResearch.WordTrace tailWord_242322 prefixEnd_242322 8192767681244849235265 := by
  unfold tailWord_242322
  simp only [CollatzResearch.WordTrace]
  refine ⟨2209552357029063536964305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5892139618744169431904813 2209552357029063536964305)
  ·
    refine ⟨1657164267771797652723229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2209552357029063536964305 1657164267771797652723229)
    ·
      refine ⟨621436600414424119771211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1657164267771797652723229 621436600414424119771211)
      ·
        refine ⟨932154900621636179656817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621436600414424119771211 932154900621636179656817)
        ·
          refine ⟨699116175466227134742613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 932154900621636179656817 699116175466227134742613)
          ·
            refine ⟨8192767681244849235265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 699116175466227134742613 8192767681244849235265)
            ·
              rfl

theorem cell19_242322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 8].length) (baseStart_242322 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242322 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242322 prefixEnd_242322 := by exact prefixLift 242322
  have htrace : WordTrace (prefixWord ++ tailWord_242322) baseStart_242322 baseEnd_242322 := by
    simpa [prefixWord, tailWord_242322, baseEnd_242322] using wordTrace_append hprefix tailTrace_242322
  have hstable : (prefixWord ++ tailWord_242322).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242322).length < 2 ^ (prefixWord ++ tailWord_242322).sum := by decide
  have hdescent : baseEnd_242322 < baseStart_242322 := by decide
  rcases family_descends (prefixWord ++ tailWord_242322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242337 : List Nat := [1, 2, 3, 3, 4, 1, 1, 4]
def baseStart_242337 : Nat := 118140960795 + 242337 * 2 ^ 59
def prefixEnd_242337 : Nat := 4983230072969 + 3 ^ 40 * 242337 * 2
def baseEnd_242337 : Nat := 73739473403688052784011

theorem tailTrace_242337 : CollatzResearch.WordTrace tailWord_242337 prefixEnd_242337 73739473403688052784011 := by
  unfold tailWord_242337
  simp only [CollatzResearch.WordTrace]
  refine ⟨8838756523061911709653265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5892504348707941139768843 8838756523061911709653265)
  ·
    refine ⟨6629067392296433782239949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8838756523061911709653265 6629067392296433782239949)
    ·
      refine ⟨2485900272111162668339981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6629067392296433782239949 2485900272111162668339981)
      ·
        refine ⟨932212602041686000627493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2485900272111162668339981 932212602041686000627493)
        ·
          refine ⟨174789862882816125117655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 932212602041686000627493 174789862882816125117655)
          ·
            refine ⟨262184794324224187676483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174789862882816125117655 262184794324224187676483)
            ·
              refine ⟨393277191486336281514725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262184794324224187676483 393277191486336281514725)
              ·
                refine ⟨73739473403688052784011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 393277191486336281514725 73739473403688052784011)
                ·
                  rfl

theorem cell19_242337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 4].length) (baseStart_242337 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242337 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242337 prefixEnd_242337 := by exact prefixLift 242337
  have htrace : WordTrace (prefixWord ++ tailWord_242337) baseStart_242337 baseEnd_242337 := by
    simpa [prefixWord, tailWord_242337, baseEnd_242337] using wordTrace_append hprefix tailTrace_242337
  have hstable : (prefixWord ++ tailWord_242337).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242337).length < 2 ^ (prefixWord ++ tailWord_242337).sum := by decide
  have hdescent : baseEnd_242337 < baseStart_242337 := by decide
  rcases family_descends (prefixWord ++ tailWord_242337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242400 : List Nat := [2, 1, 1, 3, 1, 2, 1, 8]
def baseStart_242400 : Nat := 118140960795 + 242400 * 2 ^ 59
def prefixEnd_242400 : Nat := 4983230072969 + 3 ^ 40 * 242400 * 2
def baseEnd_242400 : Nat := 73758643348122573383839

theorem tailTrace_242400 : CollatzResearch.WordTrace tailWord_242400 prefixEnd_242400 73758643348122573383839 := by
  unfold tailWord_242400
  simp only [CollatzResearch.WordTrace]
  refine ⟨4420527160916836734598327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5894036214555782312797769 4420527160916836734598327)
  ·
    refine ⟨6630790741375255101897491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4420527160916836734598327 6630790741375255101897491)
    ·
      refine ⟨9946186112062882652846237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6630790741375255101897491 9946186112062882652846237)
      ·
        refine ⟨3729819792023580994817339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9946186112062882652846237 3729819792023580994817339)
        ·
          refine ⟨5594729688035371492226009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3729819792023580994817339 5594729688035371492226009)
          ·
            refine ⟨4196047266026528619169507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5594729688035371492226009 4196047266026528619169507)
            ·
              refine ⟨6294070899039792928754261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4196047266026528619169507 6294070899039792928754261)
              ·
                refine ⟨73758643348122573383839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6294070899039792928754261 73758643348122573383839)
                ·
                  rfl

theorem cell19_242400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_242400 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242400 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242400 prefixEnd_242400 := by exact prefixLift 242400
  have htrace : WordTrace (prefixWord ++ tailWord_242400) baseStart_242400 baseEnd_242400 := by
    simpa [prefixWord, tailWord_242400, baseEnd_242400] using wordTrace_append hprefix tailTrace_242400
  have hstable : (prefixWord ++ tailWord_242400).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242400).length < 2 ^ (prefixWord ++ tailWord_242400).sum := by decide
  have hdescent : baseEnd_242400 < baseStart_242400 := by decide
  rcases family_descends (prefixWord ++ tailWord_242400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242415 : List Nat := [1, 1, 2, 1, 5, 4, 2, 3]
def baseStart_242415 : Nat := 118140960795 + 242415 * 2 ^ 59
def prefixEnd_242415 : Nat := 4983230072969 + 3 ^ 40 * 242415 * 2
def baseEnd_242415 : Nat := 73763207620606983050465

theorem tailTrace_242415 : CollatzResearch.WordTrace tailWord_242415 prefixEnd_242415 73763207620606983050465 := by
  unfold tailWord_242415
  simp only [CollatzResearch.WordTrace]
  refine ⟨8841601416779331030992699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5894400944519554020661799 8841601416779331030992699)
  ·
    refine ⟨13262402125168996546489049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8841601416779331030992699 13262402125168996546489049)
    ·
      refine ⟨9946801593876747409866787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13262402125168996546489049 9946801593876747409866787)
      ·
        refine ⟨14920202390815121114800181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9946801593876747409866787 14920202390815121114800181)
        ·
          refine ⟨1398768974138917604512517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14920202390815121114800181 1398768974138917604512517)
          ·
            refine ⟨262269182651047050846097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1398768974138917604512517 262269182651047050846097)
            ·
              refine ⟨196701886988285288134573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262269182651047050846097 196701886988285288134573)
              ·
                refine ⟨73763207620606983050465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196701886988285288134573 73763207620606983050465)
                ·
                  rfl

theorem cell19_242415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 3].length) (baseStart_242415 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242415 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242415 prefixEnd_242415 := by exact prefixLift 242415
  have htrace : WordTrace (prefixWord ++ tailWord_242415) baseStart_242415 baseEnd_242415 := by
    simpa [prefixWord, tailWord_242415, baseEnd_242415] using wordTrace_append hprefix tailTrace_242415
  have hstable : (prefixWord ++ tailWord_242415).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242415).length < 2 ^ (prefixWord ++ tailWord_242415).sum := by decide
  have hdescent : baseEnd_242415 < baseStart_242415 := by decide
  rcases family_descends (prefixWord ++ tailWord_242415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242434 : List Nat := [3, 4, 1, 1, 1, 4, 5]
def baseStart_242434 : Nat := 118140960795 + 242434 * 2 ^ 59
def prefixEnd_242434 : Nat := 4983230072969 + 3 ^ 40 * 242434 * 2
def baseEnd_242434 : Nat := 24589663010806856209397

theorem tailTrace_242434 : CollatzResearch.WordTrace tailWord_242434 prefixEnd_242434 24589663010806856209397 := by
  unfold tailWord_242434
  simp only [CollatzResearch.WordTrace]
  refine ⟨2210573600927624318983589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5894862935806998183956237 2210573600927624318983589)
  ·
    refine ⟨414482550173929559809423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2210573600927624318983589 414482550173929559809423)
    ·
      refine ⟨621723825260894339714135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414482550173929559809423 621723825260894339714135)
      ·
        refine ⟨932585737891341509571203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621723825260894339714135 932585737891341509571203)
        ·
          refine ⟨1398878606837012264356805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 932585737891341509571203 1398878606837012264356805)
          ·
            refine ⟨262289738781939799566901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1398878606837012264356805 262289738781939799566901)
            ·
              refine ⟨24589663010806856209397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 262289738781939799566901 24589663010806856209397)
              ·
                rfl

theorem cell19_242434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 5].length) (baseStart_242434 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242434 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242434 prefixEnd_242434 := by exact prefixLift 242434
  have htrace : WordTrace (prefixWord ++ tailWord_242434) baseStart_242434 baseEnd_242434 := by
    simpa [prefixWord, tailWord_242434, baseEnd_242434] using wordTrace_append hprefix tailTrace_242434
  have hstable : (prefixWord ++ tailWord_242434).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242434).length < 2 ^ (prefixWord ++ tailWord_242434).sum := by decide
  have hdescent : baseEnd_242434 < baseStart_242434 := by decide
  rcases family_descends (prefixWord ++ tailWord_242434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242476 : List Nat := [2, 2, 1, 1, 1, 4, 1, 7]
def baseStart_242476 : Nat := 118140960795 + 242476 * 2 ^ 59
def prefixEnd_242476 : Nat := 4983230072969 + 3 ^ 40 * 242476 * 2
def baseEnd_242476 : Nat := 73781768995376915694743

theorem tailTrace_242476 : CollatzResearch.WordTrace tailWord_242476 prefixEnd_242476 73781768995376915694743 := by
  unfold tailWord_242476
  simp only [CollatzResearch.WordTrace]
  refine ⟨4421913134779169224481641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5895884179705558965975521 4421913134779169224481641)
  ·
    refine ⟨3316434851084376918361231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4421913134779169224481641 3316434851084376918361231)
    ·
      refine ⟨4974652276626565377541847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3316434851084376918361231 4974652276626565377541847)
      ·
        refine ⟨7461978414939848066312771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4974652276626565377541847 7461978414939848066312771)
        ·
          refine ⟨11192967622409772099469157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7461978414939848066312771 11192967622409772099469157)
          ·
            refine ⟨2098681429201832268650467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11192967622409772099469157 2098681429201832268650467)
            ·
              refine ⟨3148022143802748402975701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2098681429201832268650467 3148022143802748402975701)
              ·
                refine ⟨73781768995376915694743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3148022143802748402975701 73781768995376915694743)
                ·
                  rfl

theorem cell19_242476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_242476 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242476 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242476 prefixEnd_242476 := by exact prefixLift 242476
  have htrace : WordTrace (prefixWord ++ tailWord_242476) baseStart_242476 baseEnd_242476 := by
    simpa [prefixWord, tailWord_242476, baseEnd_242476] using wordTrace_append hprefix tailTrace_242476
  have hstable : (prefixWord ++ tailWord_242476).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242476).length < 2 ^ (prefixWord ++ tailWord_242476).sum := by decide
  have hdescent : baseEnd_242476 < baseStart_242476 := by decide
  rcases family_descends (prefixWord ++ tailWord_242476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242493 : List Nat := [1, 4, 1, 4, 2, 7]
def baseStart_242493 : Nat := 118140960795 + 242493 * 2 ^ 59
def prefixEnd_242493 : Nat := 4983230072969 + 3 ^ 40 * 242493 * 2
def baseEnd_242493 : Nat := 8198549093058434812991

theorem tailTrace_242493 : CollatzResearch.WordTrace tailWord_242493 prefixEnd_242493 8198549093058434812991 := by
  unfold tailWord_242493
  simp only [CollatzResearch.WordTrace]
  refine ⟨8844446310496750352332133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5896297540331166901554755 8844446310496750352332133)
  ·
    refine ⟨1658333683218140691062275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8844446310496750352332133 1658333683218140691062275)
    ·
      refine ⟨2487500524827211036593413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1658333683218140691062275 2487500524827211036593413)
      ·
        refine ⟨466406348405102069361265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2487500524827211036593413 466406348405102069361265)
        ·
          refine ⟨349804761303826552020949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466406348405102069361265 349804761303826552020949)
          ·
            refine ⟨8198549093058434812991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 349804761303826552020949 8198549093058434812991)
            ·
              rfl

theorem cell19_242493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 7].length) (baseStart_242493 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242493 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242493 prefixEnd_242493 := by exact prefixLift 242493
  have htrace : WordTrace (prefixWord ++ tailWord_242493) baseStart_242493 baseEnd_242493 := by
    simpa [prefixWord, tailWord_242493, baseEnd_242493] using wordTrace_append hprefix tailTrace_242493
  have hstable : (prefixWord ++ tailWord_242493).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242493).length < 2 ^ (prefixWord ++ tailWord_242493).sum := by decide
  have hdescent : baseEnd_242493 < baseStart_242493 := by decide
  rcases family_descends (prefixWord ++ tailWord_242493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242495 : List Nat := [1, 1, 2, 2, 5, 8]
def baseStart_242495 : Nat := 118140960795 + 242495 * 2 ^ 59
def prefixEnd_242495 : Nat := 4983230072969 + 3 ^ 40 * 242495 * 2
def baseEnd_242495 : Nat := 8198616711910055696941

theorem tailTrace_242495 : CollatzResearch.WordTrace tailWord_242495 prefixEnd_242495 8198616711910055696941 := by
  unfold tailWord_242495
  simp only [CollatzResearch.WordTrace]
  refine ⟨8844519256489504693904939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5896346170993003129269959 8844519256489504693904939)
  ·
    refine ⟨13266778884734257040857409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8844519256489504693904939 13266778884734257040857409)
    ·
      refine ⟨9950084163550692780643057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13266778884734257040857409 9950084163550692780643057)
      ·
        refine ⟨7462563122663019585482293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9950084163550692780643057 7462563122663019585482293)
        ·
          refine ⟨699615292749658086138965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7462563122663019585482293 699615292749658086138965)
          ·
            refine ⟨8198616711910055696941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 699615292749658086138965 8198616711910055696941)
            ·
              rfl

theorem cell19_242495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 8].length) (baseStart_242495 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242495 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242495 prefixEnd_242495 := by exact prefixLift 242495
  have htrace : WordTrace (prefixWord ++ tailWord_242495) baseStart_242495 baseEnd_242495 := by
    simpa [prefixWord, tailWord_242495, baseEnd_242495] using wordTrace_append hprefix tailTrace_242495
  have hstable : (prefixWord ++ tailWord_242495).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242495).length < 2 ^ (prefixWord ++ tailWord_242495).sum := by decide
  have hdescent : baseEnd_242495 < baseStart_242495 := by decide
  rcases family_descends (prefixWord ++ tailWord_242495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242533 : List Nat := [1, 3, 1, 3, 1, 1, 2, 7]
def baseStart_242533 : Nat := 118140960795 + 242533 * 2 ^ 59
def prefixEnd_242533 : Nat := 4983230072969 + 3 ^ 40 * 242533 * 2
def baseEnd_242533 : Nat := 73799113230817672427921

theorem tailTrace_242533 : CollatzResearch.WordTrace tailWord_242533 prefixEnd_242533 73799113230817672427921 := by
  unfold tailWord_242533
  simp only [CollatzResearch.WordTrace]
  refine ⟨8845905230351837183788253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5897270153567891455858835 8845905230351837183788253)
  ·
    refine ⟨3317214461381938943920595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8845905230351837183788253 3317214461381938943920595)
    ·
      refine ⟨4975821692072908415880893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3317214461381938943920595 4975821692072908415880893)
      ·
        refine ⟨1865933134527340655955335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4975821692072908415880893 1865933134527340655955335)
        ·
          refine ⟨2798899701791010983933003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1865933134527340655955335 2798899701791010983933003)
          ·
            refine ⟨4198349552686516475899505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2798899701791010983933003 4198349552686516475899505)
            ·
              refine ⟨3148762164514887356924629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4198349552686516475899505 3148762164514887356924629)
              ·
                refine ⟨73799113230817672427921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3148762164514887356924629 73799113230817672427921)
                ·
                  rfl

theorem cell19_242533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_242533 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242533 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242533 prefixEnd_242533 := by exact prefixLift 242533
  have htrace : WordTrace (prefixWord ++ tailWord_242533) baseStart_242533 baseEnd_242533 := by
    simpa [prefixWord, tailWord_242533, baseEnd_242533] using wordTrace_append hprefix tailTrace_242533
  have hstable : (prefixWord ++ tailWord_242533).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242533).length < 2 ^ (prefixWord ++ tailWord_242533).sum := by decide
  have hdescent : baseEnd_242533 < baseStart_242533 := by decide
  rcases family_descends (prefixWord ++ tailWord_242533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242582 : List Nat := [5, 3, 1, 1, 1, 1, 4, 3]
def baseStart_242582 : Nat := 118140960795 + 242582 * 2 ^ 59
def prefixEnd_242582 : Nat := 4983230072969 + 3 ^ 40 * 242582 * 2
def baseEnd_242582 : Nat := 73814023187600077338899

theorem tailTrace_242582 : CollatzResearch.WordTrace tailWord_242582 prefixEnd_242582 73814023187600077338899 := by
  unfold tailWord_242582
  simp only [CollatzResearch.WordTrace]
  refine ⟨552980775448394909520125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5898461604782879034881333 552980775448394909520125)
  ·
    refine ⟨207367790793148091070047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 552980775448394909520125 207367790793148091070047)
    ·
      refine ⟨311051686189722136605071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207367790793148091070047 311051686189722136605071)
      ·
        refine ⟨466577529284583204907607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311051686189722136605071 466577529284583204907607)
        ·
          refine ⟨699866293926874807361411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466577529284583204907607 699866293926874807361411)
          ·
            refine ⟨1049799440890312211042117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699866293926874807361411 1049799440890312211042117)
            ·
              refine ⟨196837395166933539570397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1049799440890312211042117 196837395166933539570397)
              ·
                refine ⟨73814023187600077338899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196837395166933539570397 73814023187600077338899)
                ·
                  rfl

theorem cell19_242582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_242582 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242582 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242582 prefixEnd_242582 := by exact prefixLift 242582
  have htrace : WordTrace (prefixWord ++ tailWord_242582) baseStart_242582 baseEnd_242582 := by
    simpa [prefixWord, tailWord_242582, baseEnd_242582] using wordTrace_append hprefix tailTrace_242582
  have hstable : (prefixWord ++ tailWord_242582).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242582).length < 2 ^ (prefixWord ++ tailWord_242582).sum := by decide
  have hdescent : baseEnd_242582 < baseStart_242582 := by decide
  rcases family_descends (prefixWord ++ tailWord_242582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242666 : List Nat := [3, 1, 3, 1, 2, 9]
def baseStart_242666 : Nat := 118140960795 + 242666 * 2 ^ 59
def prefixEnd_242666 : Nat := 4983230072969 + 3 ^ 40 * 242666 * 2
def baseEnd_242666 : Nat := 8204398123723641274667

theorem tailTrace_242666 : CollatzResearch.WordTrace tailWord_242666 prefixEnd_242666 8204398123723641274667 := by
  unfold tailWord_242666
  simp only [CollatzResearch.WordTrace]
  refine ⟨2212689034717500224594963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5900504092580000598919901 2212689034717500224594963)
  ·
    refine ⟨3319033552076250336892445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2212689034717500224594963 3319033552076250336892445)
    ·
      refine ⟨1244637582028593876334667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3319033552076250336892445 1244637582028593876334667)
      ·
        refine ⟨1866956373042890814502001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1244637582028593876334667 1866956373042890814502001)
        ·
          refine ⟨1400217279782168110876501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1866956373042890814502001 1400217279782168110876501)
          ·
            refine ⟨8204398123723641274667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1400217279782168110876501 8204398123723641274667)
            ·
              rfl

theorem cell19_242666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 9].length) (baseStart_242666 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242666 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242666 prefixEnd_242666 := by exact prefixLift 242666
  have htrace : WordTrace (prefixWord ++ tailWord_242666) baseStart_242666 baseEnd_242666 := by
    simpa [prefixWord, tailWord_242666, baseEnd_242666] using wordTrace_append hprefix tailTrace_242666
  have hstable : (prefixWord ++ tailWord_242666).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242666).length < 2 ^ (prefixWord ++ tailWord_242666).sum := by decide
  have hdescent : baseEnd_242666 < baseStart_242666 := by decide
  rcases family_descends (prefixWord ++ tailWord_242666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242677 : List Nat := [1, 3, 5, 2, 2, 1, 1, 4]
def baseStart_242677 : Nat := 118140960795 + 242677 * 2 ^ 59
def prefixEnd_242677 : Nat := 4983230072969 + 3 ^ 40 * 242677 * 2
def baseEnd_242677 : Nat := 73842930246668005227529

theorem tailTrace_242677 : CollatzResearch.WordTrace tailWord_242677 prefixEnd_242677 73842930246668005227529 := by
  unfold tailWord_242677
  simp only [CollatzResearch.WordTrace]
  refine ⟨8851157341830149777030285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5900771561220099851353523 8851157341830149777030285)
  ·
    refine ⟨3319184003186306166386357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8851157341830149777030285 3319184003186306166386357)
    ·
      refine ⟨311173500298716203098721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3319184003186306166386357 311173500298716203098721)
      ·
        refine ⟨233380125224037152324041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311173500298716203098721 233380125224037152324041)
        ·
          refine ⟨175035093918027864243031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233380125224037152324041 175035093918027864243031)
          ·
            refine ⟨262552640877041796364547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175035093918027864243031 262552640877041796364547)
            ·
              refine ⟨393828961315562694546821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262552640877041796364547 393828961315562694546821)
              ·
                refine ⟨73842930246668005227529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 393828961315562694546821 73842930246668005227529)
                ·
                  rfl

theorem cell19_242677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 4].length) (baseStart_242677 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242677 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242677 prefixEnd_242677 := by exact prefixLift 242677
  have htrace : WordTrace (prefixWord ++ tailWord_242677) baseStart_242677 baseEnd_242677 := by
    simpa [prefixWord, tailWord_242677, baseEnd_242677] using wordTrace_append hprefix tailTrace_242677
  have hstable : (prefixWord ++ tailWord_242677).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242677).length < 2 ^ (prefixWord ++ tailWord_242677).sum := by decide
  have hdescent : baseEnd_242677 < baseStart_242677 := by decide
  rcases family_descends (prefixWord ++ tailWord_242677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242723 : List Nat := [1, 1, 1, 4, 3, 3, 6]
def baseStart_242723 : Nat := 118140960795 + 242723 * 2 ^ 59
def prefixEnd_242723 : Nat := 4983230072969 + 3 ^ 40 * 242723 * 2
def baseEnd_242723 : Nat := 24618975782984509401727

theorem tailTrace_242723 : CollatzResearch.WordTrace tailWord_242723 prefixEnd_242723 24618975782984509401727 := by
  unfold tailWord_242723
  simp only [CollatzResearch.WordTrace]
  refine ⟨8852835099663499633204823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5901890066442333088803215 8852835099663499633204823)
  ·
    refine ⟨13279252649495249449807235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8852835099663499633204823 13279252649495249449807235)
    ·
      refine ⟨19918878974242874174710853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13279252649495249449807235 19918878974242874174710853)
      ·
        refine ⟨3734789807670538907758285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19918878974242874174710853 3734789807670538907758285)
        ·
          refine ⟨1400546177876452090409357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3734789807670538907758285 1400546177876452090409357)
          ·
            refine ⟨525204816703669533903509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1400546177876452090409357 525204816703669533903509)
            ·
              refine ⟨24618975782984509401727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 525204816703669533903509 24618975782984509401727)
              ·
                rfl

theorem cell19_242723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 6].length) (baseStart_242723 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242723 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242723 prefixEnd_242723 := by exact prefixLift 242723
  have htrace : WordTrace (prefixWord ++ tailWord_242723) baseStart_242723 baseEnd_242723 := by
    simpa [prefixWord, tailWord_242723, baseEnd_242723] using wordTrace_append hprefix tailTrace_242723
  have hstable : (prefixWord ++ tailWord_242723).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242723).length < 2 ^ (prefixWord ++ tailWord_242723).sum := by decide
  have hdescent : baseEnd_242723 < baseStart_242723 := by decide
  rcases family_descends (prefixWord ++ tailWord_242723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242759 : List Nat := [1, 1, 4, 1, 3, 2, 4, 3]
def baseStart_242759 : Nat := 118140960795 + 242759 * 2 ^ 59
def prefixEnd_242759 : Nat := 4983230072969 + 3 ^ 40 * 242759 * 2
def baseEnd_242759 : Nat := 73867881602916111405083

theorem tailTrace_242759 : CollatzResearch.WordTrace tailWord_242759 prefixEnd_242759 73867881602916111405083 := by
  unfold tailWord_242759
  simp only [CollatzResearch.WordTrace]
  refine ⟨8854148127533077781515331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5902765418355385187676887 8854148127533077781515331)
  ·
    refine ⟨13281222191299616672272997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8854148127533077781515331 13281222191299616672272997)
    ·
      refine ⟨2490229160868678126051187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13281222191299616672272997 2490229160868678126051187)
      ·
        refine ⟨3735343741303017189076781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2490229160868678126051187 3735343741303017189076781)
        ·
          refine ⟨1400753902988631445903793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3735343741303017189076781 1400753902988631445903793)
          ·
            refine ⟨1050565427241473584427845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1400753902988631445903793 1050565427241473584427845)
            ·
              refine ⟨196981017607776297080221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1050565427241473584427845 196981017607776297080221)
              ·
                refine ⟨73867881602916111405083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196981017607776297080221 73867881602916111405083)
                ·
                  rfl

theorem cell19_242759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 3].length) (baseStart_242759 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242759 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242759 prefixEnd_242759 := by exact prefixLift 242759
  have htrace : WordTrace (prefixWord ++ tailWord_242759) baseStart_242759 baseEnd_242759 := by
    simpa [prefixWord, tailWord_242759, baseEnd_242759] using wordTrace_append hprefix tailTrace_242759
  have hstable : (prefixWord ++ tailWord_242759).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242759).length < 2 ^ (prefixWord ++ tailWord_242759).sum := by decide
  have hdescent : baseEnd_242759 < baseStart_242759 := by decide
  rcases family_descends (prefixWord ++ tailWord_242759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242774 : List Nat := [5, 2, 2, 1, 2, 2, 5]
def baseStart_242774 : Nat := 118140960795 + 242774 * 2 ^ 59
def prefixEnd_242774 : Nat := 4983230072969 + 3 ^ 40 * 242774 * 2
def baseEnd_242774 : Nat := 24624148625133507023903

theorem tailTrace_242774 : CollatzResearch.WordTrace tailWord_242774 prefixEnd_242774 24624148625133507023903 := by
  unfold tailWord_242774
  simp only [CollatzResearch.WordTrace]
  refine ⟨553418451404920958956961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5903130148319156895540917 553418451404920958956961)
  ·
    refine ⟨415063838553690719217721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 553418451404920958956961 415063838553690719217721)
    ·
      refine ⟨311297878915268039413291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415063838553690719217721 311297878915268039413291)
      ·
        refine ⟨466946818372902059119937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311297878915268039413291 466946818372902059119937)
        ·
          refine ⟨350210113779676544339953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 466946818372902059119937 350210113779676544339953)
          ·
            refine ⟨262657585334757408254965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350210113779676544339953 262657585334757408254965)
            ·
              refine ⟨24624148625133507023903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 262657585334757408254965 24624148625133507023903)
              ·
                rfl

theorem cell19_242774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 5].length) (baseStart_242774 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242774 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242774 prefixEnd_242774 := by exact prefixLift 242774
  have htrace : WordTrace (prefixWord ++ tailWord_242774) baseStart_242774 baseEnd_242774 := by
    simpa [prefixWord, tailWord_242774, baseEnd_242774] using wordTrace_append hprefix tailTrace_242774
  have hstable : (prefixWord ++ tailWord_242774).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242774).length < 2 ^ (prefixWord ++ tailWord_242774).sum := by decide
  have hdescent : baseEnd_242774 < baseStart_242774 := by decide
  rcases family_descends (prefixWord ++ tailWord_242774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242797 : List Nat := [1, 5, 1, 1, 2, 3, 2, 4]
def baseStart_242797 : Nat := 118140960795 + 242797 * 2 ^ 59
def prefixEnd_242797 : Nat := 4983230072969 + 3 ^ 40 * 242797 * 2
def baseEnd_242797 : Nat := 73879444426543282560535

theorem tailTrace_242797 : CollatzResearch.WordTrace tailWord_242797 prefixEnd_242797 73879444426543282560535 := by
  unfold tailWord_242797
  simp only [CollatzResearch.WordTrace]
  refine ⟨8855534101395410271398645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5903689400930273514265763 8855534101395410271398645)
  ·
    refine ⟨830206322005819712943623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8855534101395410271398645 830206322005819712943623)
    ·
      refine ⟨1245309483008729569415435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 830206322005819712943623 1245309483008729569415435)
      ·
        refine ⟨1867964224513094354123153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1245309483008729569415435 1867964224513094354123153)
        ·
          refine ⟨1400973168384820765592365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1867964224513094354123153 1400973168384820765592365)
          ·
            refine ⟨525364938144307787097137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1400973168384820765592365 525364938144307787097137)
            ·
              refine ⟨394023703608230840322853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 525364938144307787097137 394023703608230840322853)
              ·
                refine ⟨73879444426543282560535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 394023703608230840322853 73879444426543282560535)
                ·
                  rfl

theorem cell19_242797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 4].length) (baseStart_242797 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242797 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242797 prefixEnd_242797 := by exact prefixLift 242797
  have htrace : WordTrace (prefixWord ++ tailWord_242797) baseStart_242797 baseEnd_242797 := by
    simpa [prefixWord, tailWord_242797, baseEnd_242797] using wordTrace_append hprefix tailTrace_242797
  have hstable : (prefixWord ++ tailWord_242797).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242797).length < 2 ^ (prefixWord ++ tailWord_242797).sum := by decide
  have hdescent : baseEnd_242797 < baseStart_242797 := by decide
  rcases family_descends (prefixWord ++ tailWord_242797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242799 : List Nat := [1, 1, 2, 1, 3, 3, 4, 4]
def baseStart_242799 : Nat := 118140960795 + 242799 * 2 ^ 59
def prefixEnd_242799 : Nat := 4983230072969 + 3 ^ 40 * 242799 * 2
def baseEnd_242799 : Nat := 73880052996207870516085

theorem tailTrace_242799 : CollatzResearch.WordTrace tailWord_242799 prefixEnd_242799 73880052996207870516085 := by
  unfold tailWord_242799
  simp only [CollatzResearch.WordTrace]
  refine ⟨8855607047388164612971451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5903738031592109741980967 8855607047388164612971451)
  ·
    refine ⟨13283410571082246919457177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8855607047388164612971451 13283410571082246919457177)
    ·
      refine ⟨9962557928311685189592883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13283410571082246919457177 9962557928311685189592883)
      ·
        refine ⟨14943836892467527784389325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9962557928311685189592883 14943836892467527784389325)
        ·
          refine ⟨5603938834675322919145997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14943836892467527784389325 5603938834675322919145997)
          ·
            refine ⟨2101477063003246094679749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5603938834675322919145997 2101477063003246094679749)
            ·
              refine ⟨394026949313108642752453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2101477063003246094679749 394026949313108642752453)
              ·
                refine ⟨73880052996207870516085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 394026949313108642752453 73880052996207870516085)
                ·
                  rfl

theorem cell19_242799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 4].length) (baseStart_242799 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242799 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242799 prefixEnd_242799 := by exact prefixLift 242799
  have htrace : WordTrace (prefixWord ++ tailWord_242799) baseStart_242799 baseEnd_242799 := by
    simpa [prefixWord, tailWord_242799, baseEnd_242799] using wordTrace_append hprefix tailTrace_242799
  have hstable : (prefixWord ++ tailWord_242799).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242799).length < 2 ^ (prefixWord ++ tailWord_242799).sum := by decide
  have hdescent : baseEnd_242799 < baseStart_242799 := by decide
  rcases family_descends (prefixWord ++ tailWord_242799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242850 : List Nat := [3, 3, 1, 3, 3, 1, 1, 4]
def baseStart_242850 : Nat := 118140960795 + 242850 * 2 ^ 59
def prefixEnd_242850 : Nat := 4983230072969 + 3 ^ 40 * 242850 * 2
def baseEnd_242850 : Nat := 73895571522654863382613

theorem tailTrace_242850 : CollatzResearch.WordTrace tailWord_242850 prefixEnd_242850 73895571522654863382613 := by
  unfold tailWord_242850
  simp only [CollatzResearch.WordTrace]
  refine ⟨2214366792550850080769501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5904978113468933548718669 2214366792550850080769501)
  ·
    refine ⟨830387547206568780288563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2214366792550850080769501 830387547206568780288563)
    ·
      refine ⟨1245581320809853170432845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 830387547206568780288563 1245581320809853170432845)
      ·
        refine ⟨467092995303694938912317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1245581320809853170432845 467092995303694938912317)
        ·
          refine ⟨175159873238885602092119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467092995303694938912317 175159873238885602092119)
          ·
            refine ⟨262739809858328403138179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175159873238885602092119 262739809858328403138179)
            ·
              refine ⟨394109714787492604707269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262739809858328403138179 394109714787492604707269)
              ·
                refine ⟨73895571522654863382613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 394109714787492604707269 73895571522654863382613)
                ·
                  rfl

theorem cell19_242850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_242850 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242850 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242850 prefixEnd_242850 := by exact prefixLift 242850
  have htrace : WordTrace (prefixWord ++ tailWord_242850) baseStart_242850 baseEnd_242850 := by
    simpa [prefixWord, tailWord_242850, baseEnd_242850] using wordTrace_append hprefix tailTrace_242850
  have hstable : (prefixWord ++ tailWord_242850).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242850).length < 2 ^ (prefixWord ++ tailWord_242850).sum := by decide
  have hdescent : baseEnd_242850 < baseStart_242850 := by decide
  rcases family_descends (prefixWord ++ tailWord_242850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242873 : List Nat := [1, 2, 1, 4, 1, 4, 3, 3]
def baseStart_242873 : Nat := 118140960795 + 242873 * 2 ^ 59
def prefixEnd_242873 : Nat := 4983230072969 + 3 ^ 40 * 242873 * 2
def baseEnd_242873 : Nat := 73902570073797624871439

theorem tailTrace_242873 : CollatzResearch.WordTrace tailWord_242873 prefixEnd_242873 73902570073797624871439 := by
  unfold tailWord_242873
  simp only [CollatzResearch.WordTrace]
  refine ⟨8858306049120075251165273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5905537366080050167443515 8858306049120075251165273)
  ·
    refine ⟨6643729536840056438373955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8858306049120075251165273 6643729536840056438373955)
    ·
      refine ⟨9965594305260084657560933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6643729536840056438373955 9965594305260084657560933)
      ·
        refine ⟨1868548932236265873292675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9965594305260084657560933 1868548932236265873292675)
        ·
          refine ⟨2802823398354398809939013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1868548932236265873292675 2802823398354398809939013)
          ·
            refine ⟨525529387191449776863565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2802823398354398809939013 525529387191449776863565)
            ·
              refine ⟨197073520196793666323837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 525529387191449776863565 197073520196793666323837)
              ·
                refine ⟨73902570073797624871439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197073520196793666323837 73902570073797624871439)
                ·
                  rfl

theorem cell19_242873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 3].length) (baseStart_242873 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242873 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242873 prefixEnd_242873 := by exact prefixLift 242873
  have htrace : WordTrace (prefixWord ++ tailWord_242873) baseStart_242873 baseEnd_242873 := by
    simpa [prefixWord, tailWord_242873, baseEnd_242873] using wordTrace_append hprefix tailTrace_242873
  have hstable : (prefixWord ++ tailWord_242873).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242873).length < 2 ^ (prefixWord ++ tailWord_242873).sum := by decide
  have hdescent : baseEnd_242873 < baseStart_242873 := by decide
  rcases family_descends (prefixWord ++ tailWord_242873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242930 : List Nat := [3, 2, 1, 3, 3, 1, 1, 5]
def baseStart_242930 : Nat := 118140960795 + 242930 * 2 ^ 59
def prefixEnd_242930 : Nat := 4983230072969 + 3 ^ 40 * 242930 * 2
def baseEnd_242930 : Nat := 73919914309238381604617

theorem tailTrace_242930 : CollatzResearch.WordTrace tailWord_242930 prefixEnd_242930 73919914309238381604617 := by
  unfold tailWord_242930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2215096252478393496497561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5906923339942382657326829 2215096252478393496497561)
  ·
    refine ⟨1661322189358795122373171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2215096252478393496497561 1661322189358795122373171)
    ·
      refine ⟨2491983284038192683559757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1661322189358795122373171 2491983284038192683559757)
      ·
        refine ⟨934493731514322256334909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2491983284038192683559757 934493731514322256334909)
        ·
          refine ⟨350435149317870846125591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 934493731514322256334909 350435149317870846125591)
          ·
            refine ⟨525652723976806269188387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350435149317870846125591 525652723976806269188387)
            ·
              refine ⟨788479085965209403782581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525652723976806269188387 788479085965209403782581)
              ·
                refine ⟨73919914309238381604617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 788479085965209403782581 73919914309238381604617)
                ·
                  rfl

theorem cell19_242930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_242930 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242930 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242930 prefixEnd_242930 := by exact prefixLift 242930
  have htrace : WordTrace (prefixWord ++ tailWord_242930) baseStart_242930 baseEnd_242930 := by
    simpa [prefixWord, tailWord_242930, baseEnd_242930] using wordTrace_append hprefix tailTrace_242930
  have hstable : (prefixWord ++ tailWord_242930).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242930).length < 2 ^ (prefixWord ++ tailWord_242930).sum := by decide
  have hdescent : baseEnd_242930 < baseStart_242930 := by decide
  rcases family_descends (prefixWord ++ tailWord_242930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242970 : List Nat := [3, 1, 1, 3, 3, 1, 1, 6]
def baseStart_242970 : Nat := 118140960795 + 242970 * 2 ^ 59
def prefixEnd_242970 : Nat := 4983230072969 + 3 ^ 40 * 242970 * 2
def baseEnd_242970 : Nat := 73932085702530140715619

theorem tailTrace_242970 : CollatzResearch.WordTrace tailWord_242970 prefixEnd_242970 73932085702530140715619 := by
  unfold tailWord_242970
  simp only [CollatzResearch.WordTrace]
  refine ⟨2215460982442165204361591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5907895953179107211630909 2215460982442165204361591)
  ·
    refine ⟨3323191473663247806542387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2215460982442165204361591 3323191473663247806542387)
    ·
      refine ⟨4984787210494871709813581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3323191473663247806542387 4984787210494871709813581)
      ·
        refine ⟨1869295203935576891180093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4984787210494871709813581 1869295203935576891180093)
        ·
          refine ⟨700985701475841334192535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1869295203935576891180093 700985701475841334192535)
          ·
            refine ⟨1051478552213762001288803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 700985701475841334192535 1051478552213762001288803)
            ·
              refine ⟨1577217828320643001933205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051478552213762001288803 1577217828320643001933205)
              ·
                refine ⟨73932085702530140715619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1577217828320643001933205 73932085702530140715619)
                ·
                  rfl

theorem cell19_242970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_242970 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_242970 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_242970 prefixEnd_242970 := by exact prefixLift 242970
  have htrace : WordTrace (prefixWord ++ tailWord_242970) baseStart_242970 baseEnd_242970 := by
    simpa [prefixWord, tailWord_242970, baseEnd_242970] using wordTrace_append hprefix tailTrace_242970
  have hstable : (prefixWord ++ tailWord_242970).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242970).length < 2 ^ (prefixWord ++ tailWord_242970).sum := by decide
  have hdescent : baseEnd_242970 < baseStart_242970 := by decide
  rcases family_descends (prefixWord ++ tailWord_242970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243010 : List Nat := [3, 16]
def baseStart_243010 : Nat := 118140960795 + 243010 * 2 ^ 59
def prefixEnd_243010 : Nat := 4983230072969 + 3 ^ 40 * 243010 * 2
def baseEnd_243010 : Nat := 101432451434597942149

theorem tailTrace_243010 : CollatzResearch.WordTrace tailWord_243010 prefixEnd_243010 101432451434597942149 := by
  unfold tailWord_243010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2215825712405936912225621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5908868566415831765934989 2215825712405936912225621)
  ·
    refine ⟨101432451434597942149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 16 2215825712405936912225621 101432451434597942149)
    ·
      rfl

theorem cell19_243010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 16].length) (baseStart_243010 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243010 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243010 prefixEnd_243010 := by exact prefixLift 243010
  have htrace : WordTrace (prefixWord ++ tailWord_243010) baseStart_243010 baseEnd_243010 := by
    simpa [prefixWord, tailWord_243010, baseEnd_243010] using wordTrace_append hprefix tailTrace_243010
  have hstable : (prefixWord ++ tailWord_243010).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243010).length < 2 ^ (prefixWord ++ tailWord_243010).sum := by decide
  have hdescent : baseEnd_243010 < baseStart_243010 := by decide
  rcases family_descends (prefixWord ++ tailWord_243010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243021 : List Nat := [1, 6, 1, 3, 1, 2, 1, 4]
def baseStart_243021 : Nat := 118140960795 + 243021 * 2 ^ 59
def prefixEnd_243021 : Nat := 4983230072969 + 3 ^ 40 * 243021 * 2
def baseEnd_243021 : Nat := 73947604228977133582147

theorem tailTrace_243021 : CollatzResearch.WordTrace tailWord_243021 prefixEnd_243021 73947604228977133582147 := by
  unfold tailWord_243021
  simp only [CollatzResearch.WordTrace]
  refine ⟨8863704052583896527552917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5909136035055931018368611 8863704052583896527552917)
  ·
    refine ⟨415486127464870149729043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8863704052583896527552917 415486127464870149729043)
    ·
      refine ⟨623229191197305224593565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415486127464870149729043 623229191197305224593565)
      ·
        refine ⟨233710946698989459222587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 623229191197305224593565 233710946698989459222587)
        ·
          refine ⟨350566420048484188833881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233710946698989459222587 350566420048484188833881)
          ·
            refine ⟨262924815036363141625411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350566420048484188833881 262924815036363141625411)
            ·
              refine ⟨394387222554544712438117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262924815036363141625411 394387222554544712438117)
              ·
                refine ⟨73947604228977133582147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 394387222554544712438117 73947604228977133582147)
                ·
                  rfl

theorem cell19_243021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 4].length) (baseStart_243021 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243021 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243021 prefixEnd_243021 := by exact prefixLift 243021
  have htrace : WordTrace (prefixWord ++ tailWord_243021) baseStart_243021 baseEnd_243021 := by
    simpa [prefixWord, tailWord_243021, baseEnd_243021] using wordTrace_append hprefix tailTrace_243021
  have hstable : (prefixWord ++ tailWord_243021).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243021).length < 2 ^ (prefixWord ++ tailWord_243021).sum := by decide
  have hdescent : baseEnd_243021 < baseStart_243021 := by decide
  rcases family_descends (prefixWord ++ tailWord_243021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243044 : List Nat := [2, 3, 1, 1, 3, 3, 3, 3]
def baseStart_243044 : Nat := 118140960795 + 243044 * 2 ^ 59
def prefixEnd_243044 : Nat := 4983230072969 + 3 ^ 40 * 243044 * 2
def baseEnd_243044 : Nat := 73954602780119895070973

theorem tailTrace_243044 : CollatzResearch.WordTrace tailWord_243044 prefixEnd_243044 73954602780119895070973 := by
  unfold tailWord_243044
  simp only [CollatzResearch.WordTrace]
  refine ⟨4432271465750285727820093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5909695287667047637093457 4432271465750285727820093)
  ·
    refine ⟨1662101799656357147932535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4432271465750285727820093 1662101799656357147932535)
    ·
      refine ⟨2493152699484535721898803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1662101799656357147932535 2493152699484535721898803)
      ·
        refine ⟨3739729049226803582848205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2493152699484535721898803 3739729049226803582848205)
        ·
          refine ⟨1402398393460051343568077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3739729049226803582848205 1402398393460051343568077)
          ·
            refine ⟨525899397547519253838029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1402398393460051343568077 525899397547519253838029)
            ·
              refine ⟨197212274080319720189261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 525899397547519253838029 197212274080319720189261)
              ·
                refine ⟨73954602780119895070973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197212274080319720189261 73954602780119895070973)
                ·
                  rfl

theorem cell19_243044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 3].length) (baseStart_243044 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243044 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243044 prefixEnd_243044 := by exact prefixLift 243044
  have htrace : WordTrace (prefixWord ++ tailWord_243044) baseStart_243044 baseEnd_243044 := by
    simpa [prefixWord, tailWord_243044, baseEnd_243044] using wordTrace_append hprefix tailTrace_243044
  have hstable : (prefixWord ++ tailWord_243044).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243044).length < 2 ^ (prefixWord ++ tailWord_243044).sum := by decide
  have hdescent : baseEnd_243044 < baseStart_243044 := by decide
  rcases family_descends (prefixWord ++ tailWord_243044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243067 : List Nat := [1, 1, 1, 1, 1, 6, 8]
def baseStart_243067 : Nat := 118140960795 + 243067 * 2 ^ 59
def prefixEnd_243067 : Nat := 4983230072969 + 3 ^ 40 * 243067 * 2
def baseEnd_243067 : Nat := 24653867110420885519933

theorem tailTrace_243067 : CollatzResearch.WordTrace tailWord_243067 prefixEnd_243067 24653867110420885519933 := by
  unfold tailWord_243067
  simp only [CollatzResearch.WordTrace]
  refine ⟨8865381810417246383727455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5910254540278164255818303 8865381810417246383727455)
  ·
    refine ⟨13298072715625869575591183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8865381810417246383727455 13298072715625869575591183)
    ·
      refine ⟨19947109073438804363386775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13298072715625869575591183 19947109073438804363386775)
      ·
        refine ⟨29920663610158206545080163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19947109073438804363386775 29920663610158206545080163)
        ·
          refine ⟨44880995415237309817620245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29920663610158206545080163 44880995415237309817620245)
          ·
            refine ⟨2103796660089248897700949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44880995415237309817620245 2103796660089248897700949)
            ·
              refine ⟨24653867110420885519933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2103796660089248897700949 24653867110420885519933)
              ·
                rfl

theorem cell19_243067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 8].length) (baseStart_243067 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243067 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243067 prefixEnd_243067 := by exact prefixLift 243067
  have htrace : WordTrace (prefixWord ++ tailWord_243067) baseStart_243067 baseEnd_243067 := by
    simpa [prefixWord, tailWord_243067, baseEnd_243067] using wordTrace_append hprefix tailTrace_243067
  have hstable : (prefixWord ++ tailWord_243067).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243067).length < 2 ^ (prefixWord ++ tailWord_243067).sum := by decide
  have hdescent : baseEnd_243067 < baseStart_243067 := by decide
  rcases family_descends (prefixWord ++ tailWord_243067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243101 : List Nat := [1, 4, 2, 1, 3, 1, 4, 3]
def baseStart_243101 : Nat := 118140960795 + 243101 * 2 ^ 59
def prefixEnd_243101 : Nat := 4983230072969 + 3 ^ 40 * 243101 * 2
def baseEnd_243101 : Nat := 73971947015560651804151

theorem tailTrace_243101 : CollatzResearch.WordTrace tailWord_243101 prefixEnd_243101 73971947015560651804151 := by
  unfold tailWord_243101
  simp only [CollatzResearch.WordTrace]
  refine ⟨8866621892294070190465157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5911081261529380126976771 8866621892294070190465157)
  ·
    refine ⟨1662491604805138160712217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8866621892294070190465157 1662491604805138160712217)
    ·
      refine ⟨1246868703603853620534163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1662491604805138160712217 1246868703603853620534163)
      ·
        refine ⟨1870303055405780430801245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1246868703603853620534163 1870303055405780430801245)
        ·
          refine ⟨701363645777167661550467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1870303055405780430801245 701363645777167661550467)
          ·
            refine ⟨1052045468665751492325701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701363645777167661550467 1052045468665751492325701)
            ·
              refine ⟨197258525374828404811069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1052045468665751492325701 197258525374828404811069)
              ·
                refine ⟨73971947015560651804151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197258525374828404811069 73971947015560651804151)
                ·
                  rfl

theorem cell19_243101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 3].length) (baseStart_243101 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243101 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243101 prefixEnd_243101 := by exact prefixLift 243101
  have htrace : WordTrace (prefixWord ++ tailWord_243101) baseStart_243101 baseEnd_243101 := by
    simpa [prefixWord, tailWord_243101, baseEnd_243101] using wordTrace_append hprefix tailTrace_243101
  have hstable : (prefixWord ++ tailWord_243101).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243101).length < 2 ^ (prefixWord ++ tailWord_243101).sum := by decide
  have hdescent : baseEnd_243101 < baseStart_243101 := by decide
  rcases family_descends (prefixWord ++ tailWord_243101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243103 : List Nat := [1, 1, 2, 5, 1, 3, 1, 5]
def baseStart_243103 : Nat := 118140960795 + 243103 * 2 ^ 59
def prefixEnd_243103 : Nat := 4983230072969 + 3 ^ 40 * 243103 * 2
def baseEnd_243103 : Nat := 73972555585225239759701

theorem tailTrace_243103 : CollatzResearch.WordTrace tailWord_243103 prefixEnd_243103 73972555585225239759701 := by
  unfold tailWord_243103
  simp only [CollatzResearch.WordTrace]
  refine ⟨8866694838286824532037963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5911129892191216354691975 8866694838286824532037963)
  ·
    refine ⟨13300042257430236798056945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8866694838286824532037963 13300042257430236798056945)
    ·
      refine ⟨9975031693072677598542709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13300042257430236798056945 9975031693072677598542709)
      ·
        refine ⟨935159221225563524863379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9975031693072677598542709 935159221225563524863379)
        ·
          refine ⟨1402738831838345287295069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935159221225563524863379 1402738831838345287295069)
          ·
            refine ⟨526027061939379482735651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1402738831838345287295069 526027061939379482735651)
            ·
              refine ⟨789040592909069224103477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526027061939379482735651 789040592909069224103477)
              ·
                refine ⟨73972555585225239759701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 789040592909069224103477 73972555585225239759701)
                ·
                  rfl

theorem cell19_243103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 5].length) (baseStart_243103 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243103 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243103 prefixEnd_243103 := by exact prefixLift 243103
  have htrace : WordTrace (prefixWord ++ tailWord_243103) baseStart_243103 baseEnd_243103 := by
    simpa [prefixWord, tailWord_243103, baseEnd_243103] using wordTrace_append hprefix tailTrace_243103
  have hstable : (prefixWord ++ tailWord_243103).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243103).length < 2 ^ (prefixWord ++ tailWord_243103).sum := by decide
  have hdescent : baseEnd_243103 < baseStart_243103 := by decide
  rcases family_descends (prefixWord ++ tailWord_243103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243158 : List Nat := [5, 2, 1, 1, 1, 2, 2, 5]
def baseStart_243158 : Nat := 118140960795 + 243158 * 2 ^ 59
def prefixEnd_243158 : Nat := 4983230072969 + 3 ^ 40 * 243158 * 2
def baseEnd_243158 : Nat := 73989291251001408537329

theorem tailTrace_243158 : CollatzResearch.WordTrace tailWord_243158 prefixEnd_243158 73989291251001408537329 := by
  unfold tailWord_243158
  simp only [CollatzResearch.WordTrace]
  refine ⟨554293803317973057830633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5912467235391712616860085 554293803317973057830633)
  ·
    refine ⟨415720352488479793372975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 554293803317973057830633 415720352488479793372975)
    ·
      refine ⟨623580528732719690059463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415720352488479793372975 623580528732719690059463)
      ·
        refine ⟨935370793099079535089195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623580528732719690059463 935370793099079535089195)
        ·
          refine ⟨1403056189648619302633793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935370793099079535089195 1403056189648619302633793)
          ·
            refine ⟨1052292142236464476975345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1403056189648619302633793 1052292142236464476975345)
            ·
              refine ⟨789219106677348357731509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1052292142236464476975345 789219106677348357731509)
              ·
                refine ⟨73989291251001408537329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 789219106677348357731509 73989291251001408537329)
                ·
                  rfl

theorem cell19_243158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_243158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243158 prefixEnd_243158 := by exact prefixLift 243158
  have htrace : WordTrace (prefixWord ++ tailWord_243158) baseStart_243158 baseEnd_243158 := by
    simpa [prefixWord, tailWord_243158, baseEnd_243158] using wordTrace_append hprefix tailTrace_243158
  have hstable : (prefixWord ++ tailWord_243158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243158).length < 2 ^ (prefixWord ++ tailWord_243158).sum := by decide
  have hdescent : baseEnd_243158 < baseStart_243158 := by decide
  rcases family_descends (prefixWord ++ tailWord_243158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243217 : List Nat := [1, 2, 2, 1, 1, 2, 7, 3]
def baseStart_243217 : Nat := 118140960795 + 243217 * 2 ^ 59
def prefixEnd_243217 : Nat := 4983230072969 + 3 ^ 40 * 243217 * 2
def baseEnd_243217 : Nat := 74007244056106753226057

theorem tailTrace_243217 : CollatzResearch.WordTrace tailWord_243217 prefixEnd_243217 74007244056106753226057 := by
  unfold tailWord_243217
  simp only [CollatzResearch.WordTrace]
  refine ⟨8870852759873822001687905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5913901839915881334458603 8870852759873822001687905)
  ·
    refine ⟨6653139569905366501265929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8870852759873822001687905 6653139569905366501265929)
    ·
      refine ⟨4989854677429024875949447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6653139569905366501265929 4989854677429024875949447)
      ·
        refine ⟨7484782016143537313924171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4989854677429024875949447 7484782016143537313924171)
        ·
          refine ⟨11227173024215305970886257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7484782016143537313924171 11227173024215305970886257)
          ·
            refine ⟨8420379768161479478164693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11227173024215305970886257 8420379768161479478164693)
            ·
              refine ⟨197352650816284675269485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 8420379768161479478164693 197352650816284675269485)
              ·
                refine ⟨74007244056106753226057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197352650816284675269485 74007244056106753226057)
                ·
                  rfl

theorem cell19_243217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 3].length) (baseStart_243217 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243217 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243217 prefixEnd_243217 := by exact prefixLift 243217
  have htrace : WordTrace (prefixWord ++ tailWord_243217) baseStart_243217 baseEnd_243217 := by
    simpa [prefixWord, tailWord_243217, baseEnd_243217] using wordTrace_append hprefix tailTrace_243217
  have hstable : (prefixWord ++ tailWord_243217).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243217).length < 2 ^ (prefixWord ++ tailWord_243217).sum := by decide
  have hdescent : baseEnd_243217 < baseStart_243217 := by decide
  rcases family_descends (prefixWord ++ tailWord_243217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243230 : List Nat := [4, 3, 3, 1, 1, 1, 6]
def baseStart_243230 : Nat := 118140960795 + 243230 * 2 ^ 59
def prefixEnd_243230 : Nat := 4983230072969 + 3 ^ 40 * 243230 * 2
def baseEnd_243230 : Nat := 24670399919642191645711

theorem tailTrace_243230 : CollatzResearch.WordTrace tailWord_243230 prefixEnd_243230 24670399919642191645711 := by
  unfold tailWord_243230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1108915863603340652738893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5914217939217816814607429 1108915863603340652738893)
  ·
    refine ⟨415843448851252744777085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1108915863603340652738893 415843448851252744777085)
    ·
      refine ⟨155941293319219779291407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415843448851252744777085 155941293319219779291407)
      ·
        refine ⟨233911939978829668937111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155941293319219779291407 233911939978829668937111)
        ·
          refine ⟨350867909968244503405667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233911939978829668937111 350867909968244503405667)
          ·
            refine ⟨526301864952366755108501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350867909968244503405667 526301864952366755108501)
            ·
              refine ⟨24670399919642191645711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 526301864952366755108501 24670399919642191645711)
              ·
                rfl

theorem cell19_243230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 6].length) (baseStart_243230 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243230 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243230 prefixEnd_243230 := by exact prefixLift 243230
  have htrace : WordTrace (prefixWord ++ tailWord_243230) baseStart_243230 baseEnd_243230 := by
    simpa [prefixWord, tailWord_243230, baseEnd_243230] using wordTrace_append hprefix tailTrace_243230
  have hstable : (prefixWord ++ tailWord_243230).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243230).length < 2 ^ (prefixWord ++ tailWord_243230).sum := by decide
  have hdescent : baseEnd_243230 < baseStart_243230 := by decide
  rcases family_descends (prefixWord ++ tailWord_243230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243270 : List Nat := [6, 1, 1, 1, 3, 1, 1, 5]
def baseStart_243270 : Nat := 118140960795 + 243270 * 2 ^ 59
def prefixEnd_243270 : Nat := 4983230072969 + 3 ^ 40 * 243270 * 2
def baseEnd_243270 : Nat := 74023371152218334048135

theorem tailTrace_243270 : CollatzResearch.WordTrace tailWord_243270 prefixEnd_243270 74023371152218334048135 := by
  unfold tailWord_243270
  simp only [CollatzResearch.WordTrace]
  refine ⟨277274557146306626667727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5915190552454541368911509 277274557146306626667727)
  ·
    refine ⟨415911835719459940001591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277274557146306626667727 415911835719459940001591)
    ·
      refine ⟨623867753579189910002387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415911835719459940001591 623867753579189910002387)
      ·
        refine ⟨935801630368784865003581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623867753579189910002387 935801630368784865003581)
        ·
          refine ⟨350925611388294324376343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 935801630368784865003581 350925611388294324376343)
          ·
            refine ⟨526388417082441486564515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350925611388294324376343 526388417082441486564515)
            ·
              refine ⟨789582625623662229846773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526388417082441486564515 789582625623662229846773)
              ·
                refine ⟨74023371152218334048135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 789582625623662229846773 74023371152218334048135)
                ·
                  rfl

theorem cell19_243270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_243270 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243270 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243270 prefixEnd_243270 := by exact prefixLift 243270
  have htrace : WordTrace (prefixWord ++ tailWord_243270) baseStart_243270 baseEnd_243270 := by
    simpa [prefixWord, tailWord_243270, baseEnd_243270] using wordTrace_append hprefix tailTrace_243270
  have hstable : (prefixWord ++ tailWord_243270).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243270).length < 2 ^ (prefixWord ++ tailWord_243270).sum := by decide
  have hdescent : baseEnd_243270 < baseStart_243270 := by decide
  rcases family_descends (prefixWord ++ tailWord_243270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243310 : List Nat := [4, 1, 2, 2, 3, 1, 2, 4]
def baseStart_243310 : Nat := 118140960795 + 243310 * 2 ^ 59
def prefixEnd_243310 : Nat := 4983230072969 + 3 ^ 40 * 243310 * 2
def baseEnd_243310 : Nat := 74035542545510093159137

theorem tailTrace_243310 : CollatzResearch.WordTrace tailWord_243310 prefixEnd_243310 74035542545510093159137 := by
  unfold tailWord_243310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1109280593567112360602923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5916163165691265923215589 1109280593567112360602923)
  ·
    refine ⟨1663920890350668540904385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1109280593567112360602923 1663920890350668540904385)
    ·
      refine ⟨1247940667763001405678289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1663920890350668540904385 1247940667763001405678289)
      ·
        refine ⟨935955500822251054258717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1247940667763001405678289 935955500822251054258717)
        ·
          refine ⟨350983312808344145347019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 935955500822251054258717 350983312808344145347019)
          ·
            refine ⟨526474969212516218020529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350983312808344145347019 526474969212516218020529)
            ·
              refine ⟨394856226909387163515397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526474969212516218020529 394856226909387163515397)
              ·
                refine ⟨74035542545510093159137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 394856226909387163515397 74035542545510093159137)
                ·
                  rfl

theorem cell19_243310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_243310 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243310 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243310 prefixEnd_243310 := by exact prefixLift 243310
  have htrace : WordTrace (prefixWord ++ tailWord_243310) baseStart_243310 baseEnd_243310 := by
    simpa [prefixWord, tailWord_243310, baseEnd_243310] using wordTrace_append hprefix tailTrace_243310
  have hstable : (prefixWord ++ tailWord_243310).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243310).length < 2 ^ (prefixWord ++ tailWord_243310).sum := by decide
  have hdescent : baseEnd_243310 < baseStart_243310 := by decide
  rcases family_descends (prefixWord ++ tailWord_243310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243312 : List Nat := [2, 1, 1, 1, 6, 2, 2, 4]
def baseStart_243312 : Nat := 118140960795 + 243312 * 2 ^ 59
def prefixEnd_243312 : Nat := 4983230072969 + 3 ^ 40 * 243312 * 2
def baseEnd_243312 : Nat := 74036151115174681114687

theorem tailTrace_243312 : CollatzResearch.WordTrace tailWord_243312 prefixEnd_243312 74036151115174681114687 := by
  unfold tailWord_243312
  simp only [CollatzResearch.WordTrace]
  refine ⟨4437158847264826613198095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5916211796353102150930793 4437158847264826613198095)
  ·
    refine ⟨6655738270897239919797143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4437158847264826613198095 6655738270897239919797143)
    ·
      refine ⟨9983607406345859879695715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6655738270897239919797143 9983607406345859879695715)
      ·
        refine ⟨14975411109518789819543573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9983607406345859879695715 14975411109518789819543573)
        ·
          refine ⟨701972395758693272791105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14975411109518789819543573 701972395758693272791105)
          ·
            refine ⟨526479296819019954593329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701972395758693272791105 526479296819019954593329)
            ·
              refine ⟨394859472614264965944997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526479296819019954593329 394859472614264965944997)
              ·
                refine ⟨74036151115174681114687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 394859472614264965944997 74036151115174681114687)
                ·
                  rfl

theorem cell19_243312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_243312 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243312 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243312 prefixEnd_243312 := by exact prefixLift 243312
  have htrace : WordTrace (prefixWord ++ tailWord_243312) baseStart_243312 baseEnd_243312 := by
    simpa [prefixWord, tailWord_243312, baseEnd_243312] using wordTrace_append hprefix tailTrace_243312
  have hstable : (prefixWord ++ tailWord_243312).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243312).length < 2 ^ (prefixWord ++ tailWord_243312).sum := by decide
  have hdescent : baseEnd_243312 < baseStart_243312 := by decide
  rcases family_descends (prefixWord ++ tailWord_243312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243333 : List Nat := [1, 3, 1, 1, 4, 1, 1, 7]
def baseStart_243333 : Nat := 118140960795 + 243333 * 2 ^ 59
def prefixEnd_243333 : Nat := 4983230072969 + 3 ^ 40 * 243333 * 2
def baseEnd_243333 : Nat := 74042541096652854647963

theorem tailTrace_243333 : CollatzResearch.WordTrace tailWord_243333 prefixEnd_243333 74042541096652854647963 := by
  unfold tailWord_243333
  simp only [CollatzResearch.WordTrace]
  refine ⟨8875083627453573812910653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5916722418302382541940435 8875083627453573812910653)
  ·
    refine ⟨3328156360295090179841495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8875083627453573812910653 3328156360295090179841495)
    ·
      refine ⟨4992234540442635269762243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3328156360295090179841495 4992234540442635269762243)
      ·
        refine ⟨7488351810663952904643365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4992234540442635269762243 7488351810663952904643365)
        ·
          refine ⟨1404065964499491169620631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7488351810663952904643365 1404065964499491169620631)
          ·
            refine ⟨2106098946749236754430947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1404065964499491169620631 2106098946749236754430947)
            ·
              refine ⟨3159148420123855131646421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2106098946749236754430947 3159148420123855131646421)
              ·
                refine ⟨74042541096652854647963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3159148420123855131646421 74042541096652854647963)
                ·
                  rfl

theorem cell19_243333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_243333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243333 prefixEnd_243333 := by exact prefixLift 243333
  have htrace : WordTrace (prefixWord ++ tailWord_243333) baseStart_243333 baseEnd_243333 := by
    simpa [prefixWord, tailWord_243333, baseEnd_243333] using wordTrace_append hprefix tailTrace_243333
  have hstable : (prefixWord ++ tailWord_243333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243333).length < 2 ^ (prefixWord ++ tailWord_243333).sum := by decide
  have hdescent : baseEnd_243333 < baseStart_243333 := by decide
  rcases family_descends (prefixWord ++ tailWord_243333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243348 : List Nat := [2, 4, 2, 2, 3, 6]
def baseStart_243348 : Nat := 118140960795 + 243348 * 2 ^ 59
def prefixEnd_243348 : Nat := 4983230072969 + 3 ^ 40 * 243348 * 2
def baseEnd_243348 : Nat := 8227456152126362701621

theorem tailTrace_243348 : CollatzResearch.WordTrace tailWord_243348 prefixEnd_243348 8227456152126362701621 := by
  unfold tailWord_243348
  simp only [CollatzResearch.WordTrace]
  refine ⟨4437815361199615687353349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5917087148266154249804465 4437815361199615687353349)
  ·
    refine ⟨832090380224927941378753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4437815361199615687353349 832090380224927941378753)
    ·
      refine ⟨624067785168695956034065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 832090380224927941378753 624067785168695956034065)
      ·
        refine ⟨468050838876521967025549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 624067785168695956034065 468050838876521967025549)
        ·
          refine ⟨175519064578695737634581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 468050838876521967025549 175519064578695737634581)
          ·
            refine ⟨8227456152126362701621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 175519064578695737634581 8227456152126362701621)
            ·
              rfl

theorem cell19_243348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 6].length) (baseStart_243348 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243348 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243348 prefixEnd_243348 := by exact prefixLift 243348
  have htrace : WordTrace (prefixWord ++ tailWord_243348) baseStart_243348 baseEnd_243348 := by
    simpa [prefixWord, tailWord_243348, baseEnd_243348] using wordTrace_append hprefix tailTrace_243348
  have hstable : (prefixWord ++ tailWord_243348).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243348).length < 2 ^ (prefixWord ++ tailWord_243348).sum := by decide
  have hdescent : baseEnd_243348 < baseStart_243348 := by decide
  rcases family_descends (prefixWord ++ tailWord_243348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243350 : List Nat := [5, 3, 11]
def baseStart_243350 : Nat := 118140960795 + 243350 * 2 ^ 59
def prefixEnd_243350 : Nat := 4983230072969 + 3 ^ 40 * 243350 * 2
def baseEnd_243350 : Nat := 304723102628814206873

theorem tailTrace_243350 : CollatzResearch.WordTrace tailWord_243350 prefixEnd_243350 304723102628814206873 := by
  unfold tailWord_243350
  simp only [CollatzResearch.WordTrace]
  refine ⟨554731479274499107267469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5917135778927990477519669 554731479274499107267469)
  ·
    refine ⟨208024304727937165225301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 554731479274499107267469 208024304727937165225301)
    ·
      refine ⟨304723102628814206873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 11 208024304727937165225301 304723102628814206873)
      ·
        rfl

theorem cell19_243350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 11].length) (baseStart_243350 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243350 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243350 prefixEnd_243350 := by exact prefixLift 243350
  have htrace : WordTrace (prefixWord ++ tailWord_243350) baseStart_243350 baseEnd_243350 := by
    simpa [prefixWord, tailWord_243350, baseEnd_243350] using wordTrace_append hprefix tailTrace_243350
  have hstable : (prefixWord ++ tailWord_243350).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243350).length < 2 ^ (prefixWord ++ tailWord_243350).sum := by decide
  have hdescent : baseEnd_243350 < baseStart_243350 := by decide
  rcases family_descends (prefixWord ++ tailWord_243350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243352 : List Nat := [2, 1, 2, 4, 1, 9]
def baseStart_243352 : Nat := 118140960795 + 243352 * 2 ^ 59
def prefixEnd_243352 : Nat := 4983230072969 + 3 ^ 40 * 243352 * 2
def baseEnd_243352 : Nat := 8227591389829604469521

theorem tailTrace_243352 : CollatzResearch.WordTrace tailWord_243352 prefixEnd_243352 8227591389829604469521 := by
  unfold tailWord_243352
  simp only [CollatzResearch.WordTrace]
  refine ⟨4437888307192370028926155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5917184409589826705234873 4437888307192370028926155)
  ·
    refine ⟨6656832460788555043389233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4437888307192370028926155 6656832460788555043389233)
    ·
      refine ⟨4992624345591416282541925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6656832460788555043389233 4992624345591416282541925)
      ·
        refine ⟨936117064798390552976611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4992624345591416282541925 936117064798390552976611)
        ·
          refine ⟨1404175597197585829464917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 936117064798390552976611 1404175597197585829464917)
          ·
            refine ⟨8227591389829604469521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1404175597197585829464917 8227591389829604469521)
            ·
              rfl

theorem cell19_243352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 9].length) (baseStart_243352 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243352 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243352 prefixEnd_243352 := by exact prefixLift 243352
  have htrace : WordTrace (prefixWord ++ tailWord_243352) baseStart_243352 baseEnd_243352 := by
    simpa [prefixWord, tailWord_243352, baseEnd_243352] using wordTrace_append hprefix tailTrace_243352
  have hstable : (prefixWord ++ tailWord_243352).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243352).length < 2 ^ (prefixWord ++ tailWord_243352).sum := by decide
  have hdescent : baseEnd_243352 < baseStart_243352 := by decide
  rcases family_descends (prefixWord ++ tailWord_243352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243405 : List Nat := [1, 6, 2, 1, 1, 2, 6]
def baseStart_243405 : Nat := 118140960795 + 243405 * 2 ^ 59
def prefixEnd_243405 : Nat := 4983230072969 + 3 ^ 40 * 243405 * 2
def baseEnd_243405 : Nat := 24688149868192673682589

theorem tailTrace_243405 : CollatzResearch.WordTrace tailWord_243405 prefixEnd_243405 24688149868192673682589 := by
  unfold tailWord_243405
  simp only [CollatzResearch.WordTrace]
  refine ⟨8877709683192730109531669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5918473122128486739687779 8877709683192730109531669)
  ·
    refine ⟨416142641399659223884297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8877709683192730109531669 416142641399659223884297)
    ·
      refine ⟨312106981049744417913223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416142641399659223884297 312106981049744417913223)
      ·
        refine ⟨468160471574616626869835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312106981049744417913223 468160471574616626869835)
        ·
          refine ⟨702240707361924940304753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468160471574616626869835 702240707361924940304753)
          ·
            refine ⟨526680530521443705228565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 702240707361924940304753 526680530521443705228565)
            ·
              refine ⟨24688149868192673682589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 526680530521443705228565 24688149868192673682589)
              ·
                rfl

theorem cell19_243405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 6].length) (baseStart_243405 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243405 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243405 prefixEnd_243405 := by exact prefixLift 243405
  have htrace : WordTrace (prefixWord ++ tailWord_243405) baseStart_243405 baseEnd_243405 := by
    simpa [prefixWord, tailWord_243405, baseEnd_243405] using wordTrace_append hprefix tailTrace_243405
  have hstable : (prefixWord ++ tailWord_243405).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243405).length < 2 ^ (prefixWord ++ tailWord_243405).sum := by decide
  have hdescent : baseEnd_243405 < baseStart_243405 := by decide
  rcases family_descends (prefixWord ++ tailWord_243405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243409 : List Nat := [1, 2, 2, 1, 2, 5, 6]
def baseStart_243409 : Nat := 118140960795 + 243409 * 2 ^ 59
def prefixEnd_243409 : Nat := 4983230072969 + 3 ^ 40 * 243409 * 2
def baseEnd_243409 : Nat := 24688555581302398986289

theorem tailTrace_243409 : CollatzResearch.WordTrace tailWord_243409 prefixEnd_243409 24688555581302398986289 := by
  unfold tailWord_243409
  simp only [CollatzResearch.WordTrace]
  refine ⟨8877855575178238792677281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5918570383452159195118187 8877855575178238792677281)
  ·
    refine ⟨6658391681383679094507961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8877855575178238792677281 6658391681383679094507961)
    ·
      refine ⟨4993793761037759320880971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6658391681383679094507961 4993793761037759320880971)
      ·
        refine ⟨7490690641556638981321457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4993793761037759320880971 7490690641556638981321457)
        ·
          refine ⟨5618017981167479235991093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7490690641556638981321457 5618017981167479235991093)
          ·
            refine ⟨526689185734451178374165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5618017981167479235991093 526689185734451178374165)
            ·
              refine ⟨24688555581302398986289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 526689185734451178374165 24688555581302398986289)
              ·
                rfl

theorem cell19_243409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 6].length) (baseStart_243409 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243409 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243409 prefixEnd_243409 := by exact prefixLift 243409
  have htrace : WordTrace (prefixWord ++ tailWord_243409) baseStart_243409 baseEnd_243409 := by
    simpa [prefixWord, tailWord_243409, baseEnd_243409] using wordTrace_append hprefix tailTrace_243409
  have hstable : (prefixWord ++ tailWord_243409).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243409).length < 2 ^ (prefixWord ++ tailWord_243409).sum := by decide
  have hdescent : baseEnd_243409 < baseStart_243409 := by decide
  rcases family_descends (prefixWord ++ tailWord_243409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243428 : List Nat := [2, 3, 1, 1, 1, 3, 2, 6]
def baseStart_243428 : Nat := 118140960795 + 243428 * 2 ^ 59
def prefixEnd_243428 : Nat := 4983230072969 + 3 ^ 40 * 243428 * 2
def baseEnd_243428 : Nat := 74071448155720782536593

theorem tailTrace_243428 : CollatzResearch.WordTrace tailWord_243428 prefixEnd_243428 74071448155720782536593 := by
  unfold tailWord_243428
  simp only [CollatzResearch.WordTrace]
  refine ⟨4439274281054702518809469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5919032374739603358412625 4439274281054702518809469)
  ·
    refine ⟨1664727855395513444553551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4439274281054702518809469 1664727855395513444553551)
    ·
      refine ⟨2497091783093270166830327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1664727855395513444553551 2497091783093270166830327)
      ·
        refine ⟨3745637674639905250245491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2497091783093270166830327 3745637674639905250245491)
        ·
          refine ⟨5618456511959857875368237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3745637674639905250245491 5618456511959857875368237)
          ·
            refine ⟨2106921191984946703263089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5618456511959857875368237 2106921191984946703263089)
            ·
              refine ⟨1580190893988710027447317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2106921191984946703263089 1580190893988710027447317)
              ·
                refine ⟨74071448155720782536593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1580190893988710027447317 74071448155720782536593)
                ·
                  rfl

theorem cell19_243428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_243428 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243428 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243428 prefixEnd_243428 := by exact prefixLift 243428
  have htrace : WordTrace (prefixWord ++ tailWord_243428) baseStart_243428 baseEnd_243428 := by
    simpa [prefixWord, tailWord_243428, baseEnd_243428] using wordTrace_append hprefix tailTrace_243428
  have hstable : (prefixWord ++ tailWord_243428).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243428).length < 2 ^ (prefixWord ++ tailWord_243428).sum := by decide
  have hdescent : baseEnd_243428 < baseStart_243428 := by decide
  rcases family_descends (prefixWord ++ tailWord_243428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243466 : List Nat := [3, 1, 2, 2, 1, 3, 7]
def baseStart_243466 : Nat := 118140960795 + 243466 * 2 ^ 59
def prefixEnd_243466 : Nat := 4983230072969 + 3 ^ 40 * 243466 * 2
def baseEnd_243466 : Nat := 24694336993115984564015

theorem tailTrace_243466 : CollatzResearch.WordTrace tailWord_243466 prefixEnd_243466 24694336993115984564015 := by
  unfold tailWord_243466
  simp only [CollatzResearch.WordTrace]
  refine ⟨2219983633992934381875563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5919956357314491685001501 2219983633992934381875563)
  ·
    refine ⟨3329975450989401572813345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2219983633992934381875563 3329975450989401572813345)
    ·
      refine ⟨2497481588242051179610009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3329975450989401572813345 2497481588242051179610009)
      ·
        refine ⟨1873111191181538384707507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2497481588242051179610009 1873111191181538384707507)
        ·
          refine ⟨2809666786772307577061261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873111191181538384707507 2809666786772307577061261)
          ·
            refine ⟨1053625045039615341397973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2809666786772307577061261 1053625045039615341397973)
            ·
              refine ⟨24694336993115984564015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1053625045039615341397973 24694336993115984564015)
              ·
                rfl

theorem cell19_243466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 7].length) (baseStart_243466 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243466 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243466 prefixEnd_243466 := by exact prefixLift 243466
  have htrace : WordTrace (prefixWord ++ tailWord_243466) baseStart_243466 baseEnd_243466 := by
    simpa [prefixWord, tailWord_243466, baseEnd_243466] using wordTrace_append hprefix tailTrace_243466
  have hstable : (prefixWord ++ tailWord_243466).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243466).length < 2 ^ (prefixWord ++ tailWord_243466).sum := by decide
  have hdescent : baseEnd_243466 < baseStart_243466 := by decide
  rcases family_descends (prefixWord ++ tailWord_243466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243540 : List Nat := [2, 4, 1, 1, 3, 1, 3, 4]
def baseStart_243540 : Nat := 118140960795 + 243540 * 2 ^ 59
def prefixEnd_243540 : Nat := 4983230072969 + 3 ^ 40 * 243540 * 2
def baseEnd_243540 : Nat := 74105528056937708047399

theorem tailTrace_243540 : CollatzResearch.WordTrace tailWord_243540 prefixEnd_243540 74105528056937708047399 := by
  unfold tailWord_243540
  simp only [CollatzResearch.WordTrace]
  refine ⟨4441316768851824082848037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5921755691802432110464049 4441316768851824082848037)
  ·
    refine ⟨832746894159717015534007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4441316768851824082848037 832746894159717015534007)
    ·
      refine ⟨1249120341239575523301011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 832746894159717015534007 1249120341239575523301011)
      ·
        refine ⟨1873680511859363284951517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1249120341239575523301011 1873680511859363284951517)
        ·
          refine ⟨702630191947261231856819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1873680511859363284951517 702630191947261231856819)
          ·
            refine ⟨1053945287920891847785229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702630191947261231856819 1053945287920891847785229)
            ·
              refine ⟨395229482970334442919461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1053945287920891847785229 395229482970334442919461)
              ·
                refine ⟨74105528056937708047399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 395229482970334442919461 74105528056937708047399)
                ·
                  rfl

theorem cell19_243540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_243540 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243540 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243540 prefixEnd_243540 := by exact prefixLift 243540
  have htrace : WordTrace (prefixWord ++ tailWord_243540) baseStart_243540 baseEnd_243540 := by
    simpa [prefixWord, tailWord_243540, baseEnd_243540] using wordTrace_append hprefix tailTrace_243540
  have hstable : (prefixWord ++ tailWord_243540).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243540).length < 2 ^ (prefixWord ++ tailWord_243540).sum := by decide
  have hdescent : baseEnd_243540 < baseStart_243540 := by decide
  rcases family_descends (prefixWord ++ tailWord_243540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243559 : List Nat := [1, 1, 5, 1, 2, 1, 5, 3]
def baseStart_243559 : Nat := 118140960795 + 243559 * 2 ^ 59
def prefixEnd_243559 : Nat := 4983230072969 + 3 ^ 40 * 243559 * 2
def baseEnd_243559 : Nat := 74111309468751293625125

theorem tailTrace_243559 : CollatzResearch.WordTrace tailWord_243559 prefixEnd_243559 74111309468751293625125 := by
  unfold tailWord_243559
  simp only [CollatzResearch.WordTrace]
  refine ⟨8883326524634814410637731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5922217683089876273758487 8883326524634814410637731)
  ·
    refine ⟨13324989786952221615956597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8883326524634814410637731 13324989786952221615956597)
    ·
      refine ⟨1249217792526770776495931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13324989786952221615956597 1249217792526770776495931)
      ·
        refine ⟨1873826688790156164743897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1249217792526770776495931 1873826688790156164743897)
        ·
          refine ⟨1405370016592617123557923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1873826688790156164743897 1405370016592617123557923)
          ·
            refine ⟨2108055024888925685336885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1405370016592617123557923 2108055024888925685336885)
            ·
              refine ⟨197630158583336783000333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2108055024888925685336885 197630158583336783000333)
              ·
                refine ⟨74111309468751293625125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197630158583336783000333 74111309468751293625125)
                ·
                  rfl

theorem cell19_243559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 3].length) (baseStart_243559 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243559 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243559 prefixEnd_243559 := by exact prefixLift 243559
  have htrace : WordTrace (prefixWord ++ tailWord_243559) baseStart_243559 baseEnd_243559 := by
    simpa [prefixWord, tailWord_243559, baseEnd_243559] using wordTrace_append hprefix tailTrace_243559
  have hstable : (prefixWord ++ tailWord_243559).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243559).length < 2 ^ (prefixWord ++ tailWord_243559).sum := by decide
  have hdescent : baseEnd_243559 < baseStart_243559 := by decide
  rcases family_descends (prefixWord ++ tailWord_243559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243637 : List Nat := [1, 3, 3, 2, 1, 2, 7]
def baseStart_243637 : Nat := 118140960795 + 243637 * 2 ^ 59
def prefixEnd_243637 : Nat := 4983230072969 + 3 ^ 40 * 243637 * 2
def baseEnd_243637 : Nat := 24711681228556741297193

theorem tailTrace_243637 : CollatzResearch.WordTrace tailWord_243637 prefixEnd_243637 24711681228556741297193 := by
  unfold tailWord_243637
  simp only [CollatzResearch.WordTrace]
  refine ⟨8886171418352233731977165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5924114278901489154651443 8886171418352233731977165)
  ·
    refine ⟨3332314281882087649491437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8886171418352233731977165 3332314281882087649491437)
    ·
      refine ⟨1249617855705782868559289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3332314281882087649491437 1249617855705782868559289)
      ·
        refine ⟨937213391779337151419467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1249617855705782868559289 937213391779337151419467)
        ·
          refine ⟨1405820087669005727129201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 937213391779337151419467 1405820087669005727129201)
          ·
            refine ⟨1054365065751754295346901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1405820087669005727129201 1054365065751754295346901)
            ·
              refine ⟨24711681228556741297193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1054365065751754295346901 24711681228556741297193)
              ·
                rfl

theorem cell19_243637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 7].length) (baseStart_243637 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243637 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243637 prefixEnd_243637 := by exact prefixLift 243637
  have htrace : WordTrace (prefixWord ++ tailWord_243637) baseStart_243637 baseEnd_243637 := by
    simpa [prefixWord, tailWord_243637, baseEnd_243637] using wordTrace_append hprefix tailTrace_243637
  have hstable : (prefixWord ++ tailWord_243637).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243637).length < 2 ^ (prefixWord ++ tailWord_243637).sum := by decide
  have hdescent : baseEnd_243637 < baseStart_243637 := by decide
  rcases family_descends (prefixWord ++ tailWord_243637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243656 : List Nat := [2, 1, 3, 1, 4, 1, 1, 6]
def baseStart_243656 : Nat := 118140960795 + 243656 * 2 ^ 59
def prefixEnd_243656 : Nat := 4983230072969 + 3 ^ 40 * 243656 * 2
def baseEnd_243656 : Nat := 74140825097483809469305

theorem tailTrace_243656 : CollatzResearch.WordTrace tailWord_243656 prefixEnd_243656 74140825097483809469305 := by
  unfold tailWord_243656
  simp only [CollatzResearch.WordTrace]
  refine ⟨4443432202641699988459411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5924576270188933317945881 4443432202641699988459411)
  ·
    refine ⟨6665148303962549982689117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4443432202641699988459411 6665148303962549982689117)
    ·
      refine ⟨2499430613985956243508419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6665148303962549982689117 2499430613985956243508419)
      ·
        refine ⟨3749145920978934365262629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2499430613985956243508419 3749145920978934365262629)
        ·
          refine ⟨702964860183550193486743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3749145920978934365262629 702964860183550193486743)
          ·
            refine ⟨1054447290275325290230115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702964860183550193486743 1054447290275325290230115)
            ·
              refine ⟨1581670935412987935345173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1054447290275325290230115 1581670935412987935345173)
              ·
                refine ⟨74140825097483809469305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1581670935412987935345173 74140825097483809469305)
                ·
                  rfl

theorem cell19_243656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_243656 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243656 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243656 prefixEnd_243656 := by exact prefixLift 243656
  have htrace : WordTrace (prefixWord ++ tailWord_243656) baseStart_243656 baseEnd_243656 := by
    simpa [prefixWord, tailWord_243656, baseEnd_243656] using wordTrace_append hprefix tailTrace_243656
  have hstable : (prefixWord ++ tailWord_243656).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243656).length < 2 ^ (prefixWord ++ tailWord_243656).sum := by decide
  have hdescent : baseEnd_243656 < baseStart_243656 := by decide
  rcases family_descends (prefixWord ++ tailWord_243656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243694 : List Nat := [4, 1, 2, 1, 3, 8]
def baseStart_243694 : Nat := 118140960795 + 243694 * 2 ^ 59
def prefixEnd_243694 : Nat := 4983230072969 + 3 ^ 40 * 243694 * 2
def baseEnd_243694 : Nat := 8239154213456775624973

theorem tailTrace_243694 : CollatzResearch.WordTrace tailWord_243694 prefixEnd_243694 8239154213456775624973 := by
  unfold tailWord_243694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1111031297393216558350267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5925500252763821644534757 1111031297393216558350267)
  ·
    refine ⟨1666546946089824837525401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1111031297393216558350267 1666546946089824837525401)
    ·
      refine ⟨1249910209567368628144051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1666546946089824837525401 1249910209567368628144051)
      ·
        refine ⟨1874865314351052942216077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1249910209567368628144051 1874865314351052942216077)
        ·
          refine ⟨703074492881644853331029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1874865314351052942216077 703074492881644853331029)
          ·
            refine ⟨8239154213456775624973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 703074492881644853331029 8239154213456775624973)
            ·
              rfl

theorem cell19_243694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 8].length) (baseStart_243694 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243694 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243694 prefixEnd_243694 := by exact prefixLift 243694
  have htrace : WordTrace (prefixWord ++ tailWord_243694) baseStart_243694 baseEnd_243694 := by
    simpa [prefixWord, tailWord_243694, baseEnd_243694] using wordTrace_append hprefix tailTrace_243694
  have hstable : (prefixWord ++ tailWord_243694).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243694).length < 2 ^ (prefixWord ++ tailWord_243694).sum := by decide
  have hdescent : baseEnd_243694 < baseStart_243694 := by decide
  rcases family_descends (prefixWord ++ tailWord_243694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243791 : List Nat := [1, 1, 2, 1, 1, 2, 2, 9]
def baseStart_243791 : Nat := 118140960795 + 243791 * 2 ^ 59
def prefixEnd_243791 : Nat := 4983230072969 + 3 ^ 40 * 243791 * 2
def baseEnd_243791 : Nat := 74181903549843496468937

theorem tailTrace_243791 : CollatzResearch.WordTrace tailWord_243791 prefixEnd_243791 74181903549843496468937 := by
  unfold tailWord_243791
  simp only [CollatzResearch.WordTrace]
  refine ⟨8891788259794318033083227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5927858839862878688722151 8891788259794318033083227)
  ·
    refine ⟨13337682389691477049624841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8891788259794318033083227 13337682389691477049624841)
    ·
      refine ⟨10003261792268607787218631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13337682389691477049624841 10003261792268607787218631)
      ·
        refine ⟨15004892688402911680827947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10003261792268607787218631 15004892688402911680827947)
        ·
          refine ⟨22507339032604367521241921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15004892688402911680827947 22507339032604367521241921)
          ·
            refine ⟨16880504274453275640931441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22507339032604367521241921 16880504274453275640931441)
            ·
              refine ⟨12660378205839956730698581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16880504274453275640931441 12660378205839956730698581)
              ·
                refine ⟨74181903549843496468937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12660378205839956730698581 74181903549843496468937)
                ·
                  rfl

theorem cell19_243791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_243791 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243791 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243791 prefixEnd_243791 := by exact prefixLift 243791
  have htrace : WordTrace (prefixWord ++ tailWord_243791) baseStart_243791 baseEnd_243791 := by
    simpa [prefixWord, tailWord_243791, baseEnd_243791] using wordTrace_append hprefix tailTrace_243791
  have hstable : (prefixWord ++ tailWord_243791).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243791).length < 2 ^ (prefixWord ++ tailWord_243791).sum := by decide
  have hdescent : baseEnd_243791 < baseStart_243791 := by decide
  rcases family_descends (prefixWord ++ tailWord_243791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243808 : List Nat := [2, 1, 1, 3, 2, 5, 5]
def baseStart_243808 : Nat := 118140960795 + 243808 * 2 ^ 59
def prefixEnd_243808 : Nat := 4983230072969 + 3 ^ 40 * 243808 * 2
def baseEnd_243808 : Nat := 24729025463997498030371

theorem tailTrace_243808 : CollatzResearch.WordTrace tailWord_243808 prefixEnd_243808 24729025463997498030371 := by
  unfold tailWord_243808
  simp only [CollatzResearch.WordTrace]
  refine ⟨4446204150366364968226039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5928272200488486624301385 4446204150366364968226039)
  ·
    refine ⟨6669306225549547452339059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4446204150366364968226039 6669306225549547452339059)
    ·
      refine ⟨10003959338324321178508589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6669306225549547452339059 10003959338324321178508589)
      ·
        refine ⟨3751484751871620441940721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10003959338324321178508589 3751484751871620441940721)
        ·
          refine ⟨2813613563903715331455541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3751484751871620441940721 2813613563903715331455541)
          ·
            refine ⟨263776271615973312323957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2813613563903715331455541 263776271615973312323957)
            ·
              refine ⟨24729025463997498030371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263776271615973312323957 24729025463997498030371)
              ·
                rfl

theorem cell19_243808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 5].length) (baseStart_243808 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243808 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243808 prefixEnd_243808 := by exact prefixLift 243808
  have htrace : WordTrace (prefixWord ++ tailWord_243808) baseStart_243808 baseEnd_243808 := by
    simpa [prefixWord, tailWord_243808, baseEnd_243808] using wordTrace_append hprefix tailTrace_243808
  have hstable : (prefixWord ++ tailWord_243808).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243808).length < 2 ^ (prefixWord ++ tailWord_243808).sum := by decide
  have hdescent : baseEnd_243808 < baseStart_243808 := by decide
  rcases family_descends (prefixWord ++ tailWord_243808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243922 : List Nat := [3, 2, 2, 2, 1, 3, 6]
def baseStart_243922 : Nat := 118140960795 + 243922 * 2 ^ 59
def prefixEnd_243922 : Nat := 4983230072969 + 3 ^ 40 * 243922 * 2
def baseEnd_243922 : Nat := 24740588287624669185823

theorem tailTrace_243922 : CollatzResearch.WordTrace tailWord_243922 prefixEnd_243922 24740588287624669185823 := by
  unfold tailWord_243922
  simp only [CollatzResearch.WordTrace]
  refine ⟨2224141555579931851525505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5931044148213151604068013 2224141555579931851525505)
  ·
    refine ⟨1668106166684948888644129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2224141555579931851525505 1668106166684948888644129)
    ·
      refine ⟨1251079625013711666483097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1668106166684948888644129 1251079625013711666483097)
      ·
        refine ⟨938309718760283749862323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1251079625013711666483097 938309718760283749862323)
        ·
          refine ⟨1407464578140425624793485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938309718760283749862323 1407464578140425624793485)
          ·
            refine ⟨527799216802659609297557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1407464578140425624793485 527799216802659609297557)
            ·
              refine ⟨24740588287624669185823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 527799216802659609297557 24740588287624669185823)
              ·
                rfl

theorem cell19_243922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 6].length) (baseStart_243922 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243922 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243922 prefixEnd_243922 := by exact prefixLift 243922
  have htrace : WordTrace (prefixWord ++ tailWord_243922) baseStart_243922 baseEnd_243922 := by
    simpa [prefixWord, tailWord_243922, baseEnd_243922] using wordTrace_append hprefix tailTrace_243922
  have hstable : (prefixWord ++ tailWord_243922).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243922).length < 2 ^ (prefixWord ++ tailWord_243922).sum := by decide
  have hdescent : baseEnd_243922 < baseStart_243922 := by decide
  rcases family_descends (prefixWord ++ tailWord_243922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243958 : List Nat := [5, 1, 1, 1, 1, 1, 6, 3]
def baseStart_243958 : Nat := 118140960795 + 243958 * 2 ^ 59
def prefixEnd_243958 : Nat := 4983230072969 + 3 ^ 40 * 243958 * 2
def baseEnd_243958 : Nat := 74232719116836590757371

theorem tailTrace_243958 : CollatzResearch.WordTrace tailWord_243958 prefixEnd_243958 74232719116836590757371 := by
  unfold tailWord_243958
  simp only [CollatzResearch.WordTrace]
  refine ⟨556117453136831597150783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5931919500126203702941685 556117453136831597150783)
  ·
    refine ⟨834176179705247395726175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 556117453136831597150783 834176179705247395726175)
    ·
      refine ⟨1251264269557871093589263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 834176179705247395726175 1251264269557871093589263)
      ·
        refine ⟨1876896404336806640383895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1251264269557871093589263 1876896404336806640383895)
        ·
          refine ⟨2815344606505209960575843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1876896404336806640383895 2815344606505209960575843)
          ·
            refine ⟨4223016909757814940863765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2815344606505209960575843 4223016909757814940863765)
            ·
              refine ⟨197953917644897575352989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4223016909757814940863765 197953917644897575352989)
              ·
                refine ⟨74232719116836590757371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197953917644897575352989 74232719116836590757371)
                ·
                  rfl

theorem cell19_243958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_243958 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243958 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243958 prefixEnd_243958 := by exact prefixLift 243958
  have htrace : WordTrace (prefixWord ++ tailWord_243958) baseStart_243958 baseEnd_243958 := by
    simpa [prefixWord, tailWord_243958, baseEnd_243958] using wordTrace_append hprefix tailTrace_243958
  have hstable : (prefixWord ++ tailWord_243958).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243958).length < 2 ^ (prefixWord ++ tailWord_243958).sum := by decide
  have hdescent : baseEnd_243958 < baseStart_243958 := by decide
  rcases family_descends (prefixWord ++ tailWord_243958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243975 : List Nat := [1, 1, 4, 5, 2, 1, 5]
def baseStart_243975 : Nat := 118140960795 + 243975 * 2 ^ 59
def prefixEnd_243975 : Nat := 4983230072969 + 3 ^ 40 * 243975 * 2
def baseEnd_243975 : Nat := 24745963986328529459849

theorem tailTrace_243975 : CollatzResearch.WordTrace tailWord_243975 prefixEnd_243975 24745963986328529459849 := by
  unfold tailWord_243975
  simp only [CollatzResearch.WordTrace]
  refine ⟨8898499291127717457781379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5932332860751811638520919 8898499291127717457781379)
  ·
    refine ⟨13347748936691576186672069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8898499291127717457781379 13347748936691576186672069)
    ·
      refine ⟨2502702925629670535001013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13347748936691576186672069 2502702925629670535001013)
      ·
        refine ⟨234628399277781612656345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2502702925629670535001013 234628399277781612656345)
        ·
          refine ⟨175971299458336209492259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234628399277781612656345 175971299458336209492259)
          ·
            refine ⟨263956949187504314238389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175971299458336209492259 263956949187504314238389)
            ·
              refine ⟨24745963986328529459849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263956949187504314238389 24745963986328529459849)
              ·
                rfl

theorem cell19_243975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 5].length) (baseStart_243975 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_243975 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_243975 prefixEnd_243975 := by exact prefixLift 243975
  have htrace : WordTrace (prefixWord ++ tailWord_243975) baseStart_243975 baseEnd_243975 := by
    simpa [prefixWord, tailWord_243975, baseEnd_243975] using wordTrace_append hprefix tailTrace_243975
  have hstable : (prefixWord ++ tailWord_243975).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243975).length < 2 ^ (prefixWord ++ tailWord_243975).sum := by decide
  have hdescent : baseEnd_243975 < baseStart_243975 := by decide
  rcases family_descends (prefixWord ++ tailWord_243975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244019 : List Nat := [1, 1, 1, 2, 5, 1, 1, 7]
def baseStart_244019 : Nat := 118140960795 + 244019 * 2 ^ 59
def prefixEnd_244019 : Nat := 4983230072969 + 3 ^ 40 * 244019 * 2
def baseEnd_244019 : Nat := 74251280491606523401649

theorem tailTrace_244019 : CollatzResearch.WordTrace tailWord_244019 prefixEnd_244019 74251280491606523401649 := by
  unfold tailWord_244019
  simp only [CollatzResearch.WordTrace]
  refine ⟨8900104102968312972383111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5933402735312208648255407 8900104102968312972383111)
  ·
    refine ⟨13350156154452469458574667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8900104102968312972383111 13350156154452469458574667)
    ·
      refine ⟨20025234231678704187862001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13350156154452469458574667 20025234231678704187862001)
      ·
        refine ⟨15018925673759028140896501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20025234231678704187862001 15018925673759028140896501)
        ·
          refine ⟨1408024281914908888209047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15018925673759028140896501 1408024281914908888209047)
          ·
            refine ⟨2112036422872363332313571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408024281914908888209047 2112036422872363332313571)
            ·
              refine ⟨3168054634308544998470357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112036422872363332313571 3168054634308544998470357)
              ·
                refine ⟨74251280491606523401649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3168054634308544998470357 74251280491606523401649)
                ·
                  rfl

theorem cell19_244019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_244019 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244019 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244019 prefixEnd_244019 := by exact prefixLift 244019
  have htrace : WordTrace (prefixWord ++ tailWord_244019) baseStart_244019 baseEnd_244019 := by
    simpa [prefixWord, tailWord_244019, baseEnd_244019] using wordTrace_append hprefix tailTrace_244019
  have hstable : (prefixWord ++ tailWord_244019).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244019).length < 2 ^ (prefixWord ++ tailWord_244019).sum := by decide
  have hdescent : baseEnd_244019 < baseStart_244019 := by decide
  rcases family_descends (prefixWord ++ tailWord_244019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244036 : List Nat := [2, 3, 4, 1, 9]
def baseStart_244036 : Nat := 118140960795 + 244036 * 2 ^ 59
def prefixEnd_244036 : Nat := 4983230072969 + 3 ^ 40 * 244036 * 2
def baseEnd_244036 : Nat := 2750239012361315593475

theorem tailTrace_244036 : CollatzResearch.WordTrace tailWord_244036 prefixEnd_244036 2750239012361315593475 := by
  unfold tailWord_244036
  simp only [CollatzResearch.WordTrace]
  refine ⟨4450362071953362437875981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5933816095937816583834641 4450362071953362437875981)
  ·
    refine ⟨1668885776982510914203493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4450362071953362437875981 1668885776982510914203493)
    ·
      refine ⟨312916083184220796413155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1668885776982510914203493 312916083184220796413155)
      ·
        refine ⟨469374124776331194619733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312916083184220796413155 469374124776331194619733)
        ·
          refine ⟨2750239012361315593475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 469374124776331194619733 2750239012361315593475)
          ·
            rfl

theorem cell19_244036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 9].length) (baseStart_244036 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244036 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244036 prefixEnd_244036 := by exact prefixLift 244036
  have htrace : WordTrace (prefixWord ++ tailWord_244036) baseStart_244036 baseEnd_244036 := by
    simpa [prefixWord, tailWord_244036, baseEnd_244036] using wordTrace_append hprefix tailTrace_244036
  have hstable : (prefixWord ++ tailWord_244036).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244036).length < 2 ^ (prefixWord ++ tailWord_244036).sum := by decide
  have hdescent : baseEnd_244036 < baseStart_244036 := by decide
  rcases family_descends (prefixWord ++ tailWord_244036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244053 : List Nat := [1, 3, 2, 2, 4, 2, 1, 4]
def baseStart_244053 : Nat := 118140960795 + 244053 * 2 ^ 59
def prefixEnd_244053 : Nat := 4983230072969 + 3 ^ 40 * 244053 * 2
def baseEnd_244053 : Nat := 74261626175904518646001

theorem tailTrace_244053 : CollatzResearch.WordTrace tailWord_244053 prefixEnd_244053 74261626175904518646001 := by
  unfold tailWord_244053
  simp only [CollatzResearch.WordTrace]
  refine ⟨8901344184845136779120813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5934229456563424519413875 8901344184845136779120813)
  ·
    refine ⟨3338004069316926292170305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8901344184845136779120813 3338004069316926292170305)
    ·
      refine ⟨2503503051987694719127729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3338004069316926292170305 2503503051987694719127729)
      ·
        refine ⟨1877627288990771039345797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2503503051987694719127729 1877627288990771039345797)
        ·
          refine ⟨352055116685769569877337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1877627288990771039345797 352055116685769569877337)
          ·
            refine ⟨264041337514327177408003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352055116685769569877337 264041337514327177408003)
            ·
              refine ⟨396062006271490766112005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264041337514327177408003 396062006271490766112005)
              ·
                refine ⟨74261626175904518646001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 396062006271490766112005 74261626175904518646001)
                ·
                  rfl

theorem cell19_244053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 4].length) (baseStart_244053 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244053 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244053 prefixEnd_244053 := by exact prefixLift 244053
  have htrace : WordTrace (prefixWord ++ tailWord_244053) baseStart_244053 baseEnd_244053 := by
    simpa [prefixWord, tailWord_244053, baseEnd_244053] using wordTrace_append hprefix tailTrace_244053
  have hstable : (prefixWord ++ tailWord_244053).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244053).length < 2 ^ (prefixWord ++ tailWord_244053).sum := by decide
  have hdescent : baseEnd_244053 < baseStart_244053 := by decide
  rcases family_descends (prefixWord ++ tailWord_244053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244072 : List Nat := [2, 1, 4, 2, 2, 2, 3, 3]
def baseStart_244072 : Nat := 118140960795 + 244072 * 2 ^ 59
def prefixEnd_244072 : Nat := 4983230072969 + 3 ^ 40 * 244072 * 2
def baseEnd_244072 : Nat := 74267407587718104223727

theorem tailTrace_244072 : CollatzResearch.WordTrace tailWord_244072 prefixEnd_244072 74267407587718104223727 := by
  unfold tailWord_244072
  simp only [CollatzResearch.WordTrace]
  refine ⟨4451018585888151512031235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5934691447850868682708313 4451018585888151512031235)
  ·
    refine ⟨6676527878832227268046853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4451018585888151512031235 6676527878832227268046853)
    ·
      refine ⟨1251848977281042612758785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6676527878832227268046853 1251848977281042612758785)
      ·
        refine ⟨938886732960781959569089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1251848977281042612758785 938886732960781959569089)
        ·
          refine ⟨704165049720586469676817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 938886732960781959569089 704165049720586469676817)
          ·
            refine ⟨528123787290439852257613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 704165049720586469676817 528123787290439852257613)
            ·
              refine ⟨198046420233914944596605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 528123787290439852257613 198046420233914944596605)
              ·
                refine ⟨74267407587718104223727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198046420233914944596605 74267407587718104223727)
                ·
                  rfl

theorem cell19_244072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 3].length) (baseStart_244072 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244072 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244072 prefixEnd_244072 := by exact prefixLift 244072
  have htrace : WordTrace (prefixWord ++ tailWord_244072) baseStart_244072 baseEnd_244072 := by
    simpa [prefixWord, tailWord_244072, baseEnd_244072] using wordTrace_append hprefix tailTrace_244072
  have hstable : (prefixWord ++ tailWord_244072).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244072).length < 2 ^ (prefixWord ++ tailWord_244072).sum := by decide
  have hdescent : baseEnd_244072 < baseStart_244072 := by decide
  rcases family_descends (prefixWord ++ tailWord_244072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244129 : List Nat := [1, 2, 3, 5, 1, 1, 1, 5]
def baseStart_244129 : Nat := 118140960795 + 244129 * 2 ^ 59
def prefixEnd_244129 : Nat := 4983230072969 + 3 ^ 40 * 244129 * 2
def baseEnd_244129 : Nat := 74284751823158860956905

theorem tailTrace_244129 : CollatzResearch.WordTrace tailWord_244129 prefixEnd_244129 74284751823158860956905 := by
  unfold tailWord_244129
  simp only [CollatzResearch.WordTrace]
  refine ⟨8904116132569801758887441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5936077421713201172591627 8904116132569801758887441)
  ·
    refine ⟨6678087099427351319165581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8904116132569801758887441 6678087099427351319165581)
    ·
      refine ⟨2504282662285256744687093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6678087099427351319165581 2504282662285256744687093)
      ·
        refine ⟨234776499589242819814415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2504282662285256744687093 234776499589242819814415)
        ·
          refine ⟨352164749383864229721623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234776499589242819814415 352164749383864229721623)
          ·
            refine ⟨528247124075796344582435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352164749383864229721623 528247124075796344582435)
            ·
              refine ⟨792370686113694516873653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528247124075796344582435 792370686113694516873653)
              ·
                refine ⟨74284751823158860956905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 792370686113694516873653 74284751823158860956905)
                ·
                  rfl

theorem cell19_244129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 5].length) (baseStart_244129 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244129 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244129 prefixEnd_244129 := by exact prefixLift 244129
  have htrace : WordTrace (prefixWord ++ tailWord_244129) baseStart_244129 baseEnd_244129 := by
    simpa [prefixWord, tailWord_244129, baseEnd_244129] using wordTrace_append hprefix tailTrace_244129
  have hstable : (prefixWord ++ tailWord_244129).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244129).length < 2 ^ (prefixWord ++ tailWord_244129).sum := by decide
  have hdescent : baseEnd_244129 < baseStart_244129 := by decide
  rcases family_descends (prefixWord ++ tailWord_244129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244131 : List Nat := [1, 1, 1, 4, 1, 4, 4, 3]
def baseStart_244131 : Nat := 118140960795 + 244131 * 2 ^ 59
def prefixEnd_244131 : Nat := 4983230072969 + 3 ^ 40 * 244131 * 2
def baseEnd_244131 : Nat := 74285360392823448912455

theorem tailTrace_244131 : CollatzResearch.WordTrace tailWord_244131 prefixEnd_244131 74285360392823448912455 := by
  unfold tailWord_244131
  simp only [CollatzResearch.WordTrace]
  refine ⟨8904189078562556100460247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5936126052375037400306831 8904189078562556100460247)
  ·
    refine ⟨13356283617843834150690371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8904189078562556100460247 13356283617843834150690371)
    ·
      refine ⟨20034425426765751226035557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13356283617843834150690371 20034425426765751226035557)
      ·
        refine ⟨3756454767518578354881667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20034425426765751226035557 3756454767518578354881667)
        ·
          refine ⟨5634682151277867532322501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3756454767518578354881667 5634682151277867532322501)
          ·
            refine ⟨1056502903364600162310469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5634682151277867532322501 1056502903364600162310469)
            ·
              refine ⟨198094294380862530433213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1056502903364600162310469 198094294380862530433213)
              ·
                refine ⟨74285360392823448912455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198094294380862530433213 74285360392823448912455)
                ·
                  rfl

theorem cell19_244131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 3].length) (baseStart_244131 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244131 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244131 prefixEnd_244131 := by exact prefixLift 244131
  have htrace : WordTrace (prefixWord ++ tailWord_244131) baseStart_244131 baseEnd_244131 := by
    simpa [prefixWord, tailWord_244131, baseEnd_244131] using wordTrace_append hprefix tailTrace_244131
  have hstable : (prefixWord ++ tailWord_244131).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244131).length < 2 ^ (prefixWord ++ tailWord_244131).sum := by decide
  have hdescent : baseEnd_244131 < baseStart_244131 := by decide
  rcases family_descends (prefixWord ++ tailWord_244131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244133 : List Nat := [1, 3, 1, 2, 1, 1, 5, 5]
def baseStart_244133 : Nat := 118140960795 + 244133 * 2 ^ 59
def prefixEnd_244133 : Nat := 4983230072969 + 3 ^ 40 * 244133 * 2
def baseEnd_244133 : Nat := 74285968962488036868005

theorem tailTrace_244133 : CollatzResearch.WordTrace tailWord_244133 prefixEnd_244133 74285968962488036868005 := by
  unfold tailWord_244133
  simp only [CollatzResearch.WordTrace]
  refine ⟨8904262024555310442033053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5936174683036873628022035 8904262024555310442033053)
  ·
    refine ⟨3339098259208241415762395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8904262024555310442033053 3339098259208241415762395)
    ·
      refine ⟨5008647388812362123643593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3339098259208241415762395 5008647388812362123643593)
      ·
        refine ⟨3756485541609271592732695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5008647388812362123643593 3756485541609271592732695)
        ·
          refine ⟨5634728312413907389099043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3756485541609271592732695 5634728312413907389099043)
          ·
            refine ⟨8452092468620861083648565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5634728312413907389099043 8452092468620861083648565)
            ·
              refine ⟨792383668933205726592053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8452092468620861083648565 792383668933205726592053)
              ·
                refine ⟨74285968962488036868005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 792383668933205726592053 74285968962488036868005)
                ·
                  rfl

theorem cell19_244133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_244133 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244133 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244133 prefixEnd_244133 := by exact prefixLift 244133
  have htrace : WordTrace (prefixWord ++ tailWord_244133) baseStart_244133 baseEnd_244133 := by
    simpa [prefixWord, tailWord_244133, baseEnd_244133] using wordTrace_append hprefix tailTrace_244133
  have hstable : (prefixWord ++ tailWord_244133).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244133).length < 2 ^ (prefixWord ++ tailWord_244133).sum := by decide
  have hdescent : baseEnd_244133 < baseStart_244133 := by decide
  rcases family_descends (prefixWord ++ tailWord_244133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244245 : List Nat := [1, 3, 2, 1, 3, 1, 5, 3]
def baseStart_244245 : Nat := 118140960795 + 244245 * 2 ^ 59
def prefixEnd_244245 : Nat := 4983230072969 + 3 ^ 40 * 244245 * 2
def baseEnd_244245 : Nat := 74320048863704962378811

theorem tailTrace_244245 : CollatzResearch.WordTrace tailWord_244245 prefixEnd_244245 74320048863704962378811 := by
  unfold tailWord_244245
  simp only [CollatzResearch.WordTrace]
  refine ⟨8908347000149553570110189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5938898000099702380073459 8908347000149553570110189)
  ·
    refine ⟨3340630125056082588791321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8908347000149553570110189 3340630125056082588791321)
    ·
      refine ⟨2505472593792061941593491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3340630125056082588791321 2505472593792061941593491)
      ·
        refine ⟨3758208890688092912390237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2505472593792061941593491 3758208890688092912390237)
        ·
          refine ⟨1409328334008034842146339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3758208890688092912390237 1409328334008034842146339)
          ·
            refine ⟨2113992501012052263219509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409328334008034842146339 2113992501012052263219509)
            ·
              refine ⟨198186796969879899676829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2113992501012052263219509 198186796969879899676829)
              ·
                refine ⟨74320048863704962378811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198186796969879899676829 74320048863704962378811)
                ·
                  rfl

theorem cell19_244245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 3].length) (baseStart_244245 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244245 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244245 prefixEnd_244245 := by exact prefixLift 244245
  have htrace : WordTrace (prefixWord ++ tailWord_244245) baseStart_244245 baseEnd_244245 := by
    simpa [prefixWord, tailWord_244245, baseEnd_244245] using wordTrace_append hprefix tailTrace_244245
  have hstable : (prefixWord ++ tailWord_244245).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244245).length < 2 ^ (prefixWord ++ tailWord_244245).sum := by decide
  have hdescent : baseEnd_244245 < baseStart_244245 := by decide
  rcases family_descends (prefixWord ++ tailWord_244245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244264 : List Nat := [2, 1, 5, 2, 1, 2, 6]
def baseStart_244264 : Nat := 118140960795 + 244264 * 2 ^ 59
def prefixEnd_244264 : Nat := 4983230072969 + 3 ^ 40 * 244264 * 2
def baseEnd_244264 : Nat := 24775276758506182652179

theorem tailTrace_244264 : CollatzResearch.WordTrace tailWord_244264 prefixEnd_244264 24775276758506182652179 := by
  unfold tailWord_244264
  simp only [CollatzResearch.WordTrace]
  refine ⟨4454519993540359907525923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5939359991387146543367897 4454519993540359907525923)
  ·
    refine ⟨6681779990310539861288885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4454519993540359907525923 6681779990310539861288885)
    ·
      refine ⟨626416874091613111995833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6681779990310539861288885 626416874091613111995833)
      ·
        refine ⟨469812655568709833996875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 626416874091613111995833 469812655568709833996875)
        ·
          refine ⟨704718983353064750995313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469812655568709833996875 704718983353064750995313)
          ·
            refine ⟨528539237514798563246485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 704718983353064750995313 528539237514798563246485)
            ·
              refine ⟨24775276758506182652179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 528539237514798563246485 24775276758506182652179)
              ·
                rfl

theorem cell19_244264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 6].length) (baseStart_244264 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244264 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244264 prefixEnd_244264 := by exact prefixLift 244264
  have htrace : WordTrace (prefixWord ++ tailWord_244264) baseStart_244264 baseEnd_244264 := by
    simpa [prefixWord, tailWord_244264, baseEnd_244264] using wordTrace_append hprefix tailTrace_244264
  have hstable : (prefixWord ++ tailWord_244264).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244264).length < 2 ^ (prefixWord ++ tailWord_244264).sum := by decide
  have hdescent : baseEnd_244264 < baseStart_244264 := by decide
  rcases family_descends (prefixWord ++ tailWord_244264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244302 : List Nat := [4, 1, 1, 1, 1, 2, 6, 3]
def baseStart_244302 : Nat := 118140960795 + 244302 * 2 ^ 59
def prefixEnd_244302 : Nat := 4983230072969 + 3 ^ 40 * 244302 * 2
def baseEnd_244302 : Nat := 74337393099145719111989

theorem tailTrace_244302 : CollatzResearch.WordTrace tailWord_244302 prefixEnd_244302 74337393099145719111989 := by
  unfold tailWord_244302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1113803245117881538116895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5940283973962034869956773 1113803245117881538116895)
  ·
    refine ⟨1670704867676822307175343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1113803245117881538116895 1670704867676822307175343)
    ·
      refine ⟨2506057301515233460763015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1670704867676822307175343 2506057301515233460763015)
      ·
        refine ⟨3759085952272850191144523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2506057301515233460763015 3759085952272850191144523)
        ·
          refine ⟨5638628928409275286716785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3759085952272850191144523 5638628928409275286716785)
          ·
            refine ⟨4228971696306956465037589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5638628928409275286716785 4228971696306956465037589)
            ·
              refine ⟨198233048264388584298637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4228971696306956465037589 198233048264388584298637)
              ·
                refine ⟨74337393099145719111989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198233048264388584298637 74337393099145719111989)
                ·
                  rfl

theorem cell19_244302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_244302 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244302 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244302 prefixEnd_244302 := by exact prefixLift 244302
  have htrace : WordTrace (prefixWord ++ tailWord_244302) baseStart_244302 baseEnd_244302 := by
    simpa [prefixWord, tailWord_244302, baseEnd_244302] using wordTrace_append hprefix tailTrace_244302
  have hstable : (prefixWord ++ tailWord_244302).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244302).length < 2 ^ (prefixWord ++ tailWord_244302).sum := by decide
  have hdescent : baseEnd_244302 < baseStart_244302 := by decide
  rcases family_descends (prefixWord ++ tailWord_244302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244378 : List Nat := [3, 1, 1, 6, 1, 7]
def baseStart_244378 : Nat := 118140960795 + 244378 * 2 ^ 59
def prefixEnd_244378 : Nat := 4983230072969 + 3 ^ 40 * 244378 * 2
def baseEnd_244378 : Nat := 8262279860711117935877

theorem tailTrace_244378 : CollatzResearch.WordTrace tailWord_244378 prefixEnd_244378 8262279860711117935877 := by
  unfold tailWord_244378
  simp only [CollatzResearch.WordTrace]
  refine ⟨2228299477166929321175447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5942131939111811523134525 2228299477166929321175447)
  ·
    refine ⟨3342449215750393981763171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2228299477166929321175447 3342449215750393981763171)
    ·
      refine ⟨5013673823625590972644757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3342449215750393981763171 5013673823625590972644757)
      ·
        refine ⟨235015960482449576842723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5013673823625590972644757 235015960482449576842723)
        ·
          refine ⟨352523940723674365264085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235015960482449576842723 352523940723674365264085)
          ·
            refine ⟨8262279860711117935877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 352523940723674365264085 8262279860711117935877)
            ·
              rfl

theorem cell19_244378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 7].length) (baseStart_244378 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244378 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244378 prefixEnd_244378 := by exact prefixLift 244378
  have htrace : WordTrace (prefixWord ++ tailWord_244378) baseStart_244378 baseEnd_244378 := by
    simpa [prefixWord, tailWord_244378, baseEnd_244378] using wordTrace_append hprefix tailTrace_244378
  have hstable : (prefixWord ++ tailWord_244378).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244378).length < 2 ^ (prefixWord ++ tailWord_244378).sum := by decide
  have hdescent : baseEnd_244378 < baseStart_244378 := by decide
  rcases family_descends (prefixWord ++ tailWord_244378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244380 : List Nat := [2, 2, 3, 2, 2, 8]
def baseStart_244380 : Nat := 118140960795 + 244380 * 2 ^ 59
def prefixEnd_244380 : Nat := 4983230072969 + 3 ^ 40 * 244380 * 2
def baseEnd_244380 : Nat := 8262347479562738819827

theorem tailTrace_244380 : CollatzResearch.WordTrace tailWord_244380 prefixEnd_244380 8262347479562738819827 := by
  unfold tailWord_244380
  simp only [CollatzResearch.WordTrace]
  refine ⟨4456635427330235813137297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5942180569773647750849729 4456635427330235813137297)
  ·
    refine ⟨3342476570497676859852973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4456635427330235813137297 3342476570497676859852973)
    ·
      refine ⟨1253428713936628822444865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3342476570497676859852973 1253428713936628822444865)
      ·
        refine ⟨940071535452471616833649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1253428713936628822444865 940071535452471616833649)
        ·
          refine ⟨705053651589353712625237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 940071535452471616833649 705053651589353712625237)
          ·
            refine ⟨8262347479562738819827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 705053651589353712625237 8262347479562738819827)
            ·
              rfl

theorem cell19_244380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 8].length) (baseStart_244380 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244380 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244380 prefixEnd_244380 := by exact prefixLift 244380
  have htrace : WordTrace (prefixWord ++ tailWord_244380) baseStart_244380 baseEnd_244380 := by
    simpa [prefixWord, tailWord_244380, baseEnd_244380] using wordTrace_append hprefix tailTrace_244380
  have hstable : (prefixWord ++ tailWord_244380).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244380).length < 2 ^ (prefixWord ++ tailWord_244380).sum := by decide
  have hdescent : baseEnd_244380 < baseStart_244380 := by decide
  rcases family_descends (prefixWord ++ tailWord_244380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244397 : List Nat := [1, 5, 2, 1, 1, 2, 3, 4]
def baseStart_244397 : Nat := 118140960795 + 244397 * 2 ^ 59
def prefixEnd_244397 : Nat := 4983230072969 + 3 ^ 40 * 244397 * 2
def baseEnd_244397 : Nat := 74366300158213647000619

theorem tailTrace_244397 : CollatzResearch.WordTrace tailWord_244397 prefixEnd_244397 74366300158213647000619 := by
  unfold tailWord_244397
  simp only [CollatzResearch.WordTrace]
  refine ⟨8913890895598883529643445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5942593930399255686428963 8913890895598883529643445)
  ·
    refine ⟨835677271462395330904073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8913890895598883529643445 835677271462395330904073)
    ·
      refine ⟨626757953596796498178055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 835677271462395330904073 626757953596796498178055)
      ·
        refine ⟨940136930395194747267083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626757953596796498178055 940136930395194747267083)
        ·
          refine ⟨1410205395592792120900625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940136930395194747267083 1410205395592792120900625)
          ·
            refine ⟨1057654046694594090675469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1410205395592792120900625 1057654046694594090675469)
            ·
              refine ⟨396620267510472784003301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1057654046694594090675469 396620267510472784003301)
              ·
                refine ⟨74366300158213647000619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 396620267510472784003301 74366300158213647000619)
                ·
                  rfl

theorem cell19_244397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 4].length) (baseStart_244397 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244397 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244397 prefixEnd_244397 := by exact prefixLift 244397
  have htrace : WordTrace (prefixWord ++ tailWord_244397) baseStart_244397 baseEnd_244397 := by
    simpa [prefixWord, tailWord_244397, baseEnd_244397] using wordTrace_append hprefix tailTrace_244397
  have hstable : (prefixWord ++ tailWord_244397).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244397).length < 2 ^ (prefixWord ++ tailWord_244397).sum := by decide
  have hdescent : baseEnd_244397 < baseStart_244397 := by decide
  rcases family_descends (prefixWord ++ tailWord_244397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244399 : List Nat := [1, 1, 2, 1, 2, 5, 3, 4]
def baseStart_244399 : Nat := 118140960795 + 244399 * 2 ^ 59
def prefixEnd_244399 : Nat := 4983230072969 + 3 ^ 40 * 244399 * 2
def baseEnd_244399 : Nat := 74366908727878234956169

theorem tailTrace_244399 : CollatzResearch.WordTrace tailWord_244399 prefixEnd_244399 74366908727878234956169 := by
  unfold tailWord_244399
  simp only [CollatzResearch.WordTrace]
  refine ⟨8913963841591637871216251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5942642561061091914144167 8913963841591637871216251)
  ·
    refine ⟨13370945762387456806824377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8913963841591637871216251 13370945762387456806824377)
    ·
      refine ⟨10028209321790592605118283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13370945762387456806824377 10028209321790592605118283)
      ·
        refine ⟨15042313982685888907677425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10028209321790592605118283 15042313982685888907677425)
        ·
          refine ⟨11281735487014416680758069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15042313982685888907677425 11281735487014416680758069)
          ·
            refine ⟨1057662701907601563821069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11281735487014416680758069 1057662701907601563821069)
            ·
              refine ⟨396623513215350586432901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1057662701907601563821069 396623513215350586432901)
              ·
                refine ⟨74366908727878234956169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 396623513215350586432901 74366908727878234956169)
                ·
                  rfl

theorem cell19_244399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 4].length) (baseStart_244399 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244399 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244399 prefixEnd_244399 := by exact prefixLift 244399
  have htrace : WordTrace (prefixWord ++ tailWord_244399) baseStart_244399 baseEnd_244399 := by
    simpa [prefixWord, tailWord_244399, baseEnd_244399] using wordTrace_append hprefix tailTrace_244399
  have hstable : (prefixWord ++ tailWord_244399).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244399).length < 2 ^ (prefixWord ++ tailWord_244399).sum := by decide
  have hdescent : baseEnd_244399 < baseStart_244399 := by decide
  rcases family_descends (prefixWord ++ tailWord_244399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244416 : List Nat := [2, 1, 1, 2, 4, 3, 3, 3]
def baseStart_244416 : Nat := 118140960795 + 244416 * 2 ^ 59
def prefixEnd_244416 : Nat := 4983230072969 + 3 ^ 40 * 244416 * 2
def baseEnd_244416 : Nat := 74372081570027232578345

theorem tailTrace_244416 : CollatzResearch.WordTrace tailWord_244416 prefixEnd_244416 74372081570027232578345 := by
  unfold tailWord_244416
  simp only [CollatzResearch.WordTrace]
  refine ⟨4457291941265024887292551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5943055921686699849723401 4457291941265024887292551)
  ·
    refine ⟨6685937911897537330938827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4457291941265024887292551 6685937911897537330938827)
    ·
      refine ⟨10028906867846305996408241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6685937911897537330938827 10028906867846305996408241)
      ·
        refine ⟨7521680150884729497306181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10028906867846305996408241 7521680150884729497306181)
        ·
          refine ⟨1410315028290886780744909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7521680150884729497306181 1410315028290886780744909)
          ·
            refine ⟨528868135609082542779341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1410315028290886780744909 528868135609082542779341)
            ·
              refine ⟨198325550853405953542253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 528868135609082542779341 198325550853405953542253)
              ·
                refine ⟨74372081570027232578345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198325550853405953542253 74372081570027232578345)
                ·
                  rfl

theorem cell19_244416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 3].length) (baseStart_244416 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244416 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244416 prefixEnd_244416 := by exact prefixLift 244416
  have htrace : WordTrace (prefixWord ++ tailWord_244416) baseStart_244416 baseEnd_244416 := by
    simpa [prefixWord, tailWord_244416, baseEnd_244416] using wordTrace_append hprefix tailTrace_244416
  have hstable : (prefixWord ++ tailWord_244416).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244416).length < 2 ^ (prefixWord ++ tailWord_244416).sum := by decide
  have hdescent : baseEnd_244416 < baseStart_244416 := by decide
  rcases family_descends (prefixWord ++ tailWord_244416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244469 : List Nat := [1, 3, 6, 1, 1, 1, 1, 5]
def baseStart_244469 : Nat := 118140960795 + 244469 * 2 ^ 59
def prefixEnd_244469 : Nat := 4983230072969 + 3 ^ 40 * 244469 * 2
def baseEnd_244469 : Nat := 74388208666138813400423

theorem tailTrace_244469 : CollatzResearch.WordTrace tailWord_244469 prefixEnd_244469 74388208666138813400423 := by
  unfold tailWord_244469
  simp only [CollatzResearch.WordTrace]
  refine ⟨8916516951338039826264461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5944344634225359884176307 8916516951338039826264461)
  ·
    refine ⟨3343693856751764934849173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8916516951338039826264461 3343693856751764934849173)
    ·
      refine ⟨156735649535238981321055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3343693856751764934849173 156735649535238981321055)
      ·
        refine ⟨235103474302858471981583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156735649535238981321055 235103474302858471981583)
        ·
          refine ⟨352655211454287707972375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235103474302858471981583 352655211454287707972375)
          ·
            refine ⟨528982817181431561958563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352655211454287707972375 528982817181431561958563)
            ·
              refine ⟨793474225772147342937845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528982817181431561958563 793474225772147342937845)
              ·
                refine ⟨74388208666138813400423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 793474225772147342937845 74388208666138813400423)
                ·
                  rfl

theorem cell19_244469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 5].length) (baseStart_244469 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244469 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244469 prefixEnd_244469 := by exact prefixLift 244469
  have htrace : WordTrace (prefixWord ++ tailWord_244469) baseStart_244469 baseEnd_244469 := by
    simpa [prefixWord, tailWord_244469, baseEnd_244469] using wordTrace_append hprefix tailTrace_244469
  have hstable : (prefixWord ++ tailWord_244469).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244469).length < 2 ^ (prefixWord ++ tailWord_244469).sum := by decide
  have hdescent : baseEnd_244469 < baseStart_244469 := by decide
  rcases family_descends (prefixWord ++ tailWord_244469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244509 : List Nat := [1, 4, 2, 4, 1, 1, 2, 4]
def baseStart_244509 : Nat := 118140960795 + 244509 * 2 ^ 59
def prefixEnd_244509 : Nat := 4983230072969 + 3 ^ 40 * 244509 * 2
def baseEnd_244509 : Nat := 74400380059430572511425

theorem tailTrace_244509 : CollatzResearch.WordTrace tailWord_244509 prefixEnd_244509 74400380059430572511425 := by
  unfold tailWord_244509
  simp only [CollatzResearch.WordTrace]
  refine ⟨8917975871193126657720581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5945317247462084438480387 8917975871193126657720581)
  ·
    refine ⟨1672120475848711248322609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8917975871193126657720581 1672120475848711248322609)
    ·
      refine ⟨1254090356886533436241957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1672120475848711248322609 1254090356886533436241957)
      ·
        refine ⟨235141941916225019295367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1254090356886533436241957 235141941916225019295367)
        ·
          refine ⟨352712912874337528943051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235141941916225019295367 352712912874337528943051)
          ·
            refine ⟨529069369311506293414577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352712912874337528943051 529069369311506293414577)
            ·
              refine ⟨396802026983629720060933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529069369311506293414577 396802026983629720060933)
              ·
                refine ⟨74400380059430572511425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 396802026983629720060933 74400380059430572511425)
                ·
                  rfl

theorem cell19_244509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 4].length) (baseStart_244509 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244509 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244509 prefixEnd_244509 := by exact prefixLift 244509
  have htrace : WordTrace (prefixWord ++ tailWord_244509) baseStart_244509 baseEnd_244509 := by
    simpa [prefixWord, tailWord_244509, baseEnd_244509] using wordTrace_append hprefix tailTrace_244509
  have hstable : (prefixWord ++ tailWord_244509).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244509).length < 2 ^ (prefixWord ++ tailWord_244509).sum := by decide
  have hdescent : baseEnd_244509 < baseStart_244509 := by decide
  rcases family_descends (prefixWord ++ tailWord_244509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244513 : List Nat := [1, 2, 3, 2, 1, 2, 4, 4]
def baseStart_244513 : Nat := 118140960795 + 244513 * 2 ^ 59
def prefixEnd_244513 : Nat := 4983230072969 + 3 ^ 40 * 244513 * 2
def baseEnd_244513 : Nat := 74401597198759748422525

theorem tailTrace_244513 : CollatzResearch.WordTrace tailWord_244513 prefixEnd_244513 74401597198759748422525 := by
  unfold tailWord_244513
  simp only [CollatzResearch.WordTrace]
  refine ⟨8918121763178635340866193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5945414508785756893910795 8918121763178635340866193)
  ·
    refine ⟨6688591322383976505649645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8918121763178635340866193 6688591322383976505649645)
    ·
      refine ⟨2508221745893991189618617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6688591322383976505649645 2508221745893991189618617)
      ·
        refine ⟨1881166309420493392213963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2508221745893991189618617 1881166309420493392213963)
        ·
          refine ⟨2821749464130740088320945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1881166309420493392213963 2821749464130740088320945)
          ·
            refine ⟨2116312098098055066240709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2821749464130740088320945 2116312098098055066240709)
            ·
              refine ⟨396808518393385324920133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2116312098098055066240709 396808518393385324920133)
              ·
                refine ⟨74401597198759748422525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 396808518393385324920133 74401597198759748422525)
                ·
                  rfl

theorem cell19_244513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 4].length) (baseStart_244513 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244513 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244513 prefixEnd_244513 := by exact prefixLift 244513
  have htrace : WordTrace (prefixWord ++ tailWord_244513) baseStart_244513 baseEnd_244513 := by
    simpa [prefixWord, tailWord_244513, baseEnd_244513] using wordTrace_append hprefix tailTrace_244513
  have hstable : (prefixWord ++ tailWord_244513).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244513).length < 2 ^ (prefixWord ++ tailWord_244513).sum := by decide
  have hdescent : baseEnd_244513 < baseStart_244513 := by decide
  rcases family_descends (prefixWord ++ tailWord_244513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244553 : List Nat := [1, 2, 1, 1, 2, 12]
def baseStart_244553 : Nat := 118140960795 + 244553 * 2 ^ 59
def prefixEnd_244553 : Nat := 4983230072969 + 3 ^ 40 * 244553 * 2
def baseEnd_244553 : Nat := 8268196510227945281503

theorem tailTrace_244553 : CollatzResearch.WordTrace tailWord_244553 prefixEnd_244553 8268196510227945281503 := by
  unfold tailWord_244553
  simp only [CollatzResearch.WordTrace]
  refine ⟨8919580683033722172322313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5946387122022481448214875 8919580683033722172322313)
  ·
    refine ⟨6689685512275291629241735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8919580683033722172322313 6689685512275291629241735)
    ·
      refine ⟨10034528268412937443862603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6689685512275291629241735 10034528268412937443862603)
      ·
        refine ⟨15051792402619406165793905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10034528268412937443862603 15051792402619406165793905)
        ·
          refine ⟨11288844301964554624345429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15051792402619406165793905 11288844301964554624345429)
          ·
            refine ⟨8268196510227945281503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 11288844301964554624345429 8268196510227945281503)
            ·
              rfl

theorem cell19_244553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 12].length) (baseStart_244553 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244553 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244553 prefixEnd_244553 := by exact prefixLift 244553
  have htrace : WordTrace (prefixWord ++ tailWord_244553) baseStart_244553 baseEnd_244553 := by
    simpa [prefixWord, tailWord_244553, baseEnd_244553] using wordTrace_append hprefix tailTrace_244553
  have hstable : (prefixWord ++ tailWord_244553).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244553).length < 2 ^ (prefixWord ++ tailWord_244553).sum := by decide
  have hdescent : baseEnd_244553 < baseStart_244553 := by decide
  rcases family_descends (prefixWord ++ tailWord_244553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244570 : List Nat := [3, 1, 1, 2, 1, 4, 3, 4]
def baseStart_244570 : Nat := 118140960795 + 244570 * 2 ^ 59
def prefixEnd_244570 : Nat := 4983230072969 + 3 ^ 40 * 244570 * 2
def baseEnd_244570 : Nat := 74418941434200505155703

theorem tailTrace_244570 : CollatzResearch.WordTrace tailWord_244570 prefixEnd_244570 74418941434200505155703 := by
  unfold tailWord_244570
  simp only [CollatzResearch.WordTrace]
  refine ⟨2230050180993033518922791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5946800482648089383794109 2230050180993033518922791)
  ·
    refine ⟨3345075271489550278384187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2230050180993033518922791 3345075271489550278384187)
    ·
      refine ⟨5017612907234325417576281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3345075271489550278384187 5017612907234325417576281)
      ·
        refine ⟨3763209680425744063182211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5017612907234325417576281 3763209680425744063182211)
        ·
          refine ⟨5644814520638616094773317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3763209680425744063182211 5644814520638616094773317)
          ·
            refine ⟨1058402722619740517769997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5644814520638616094773317 1058402722619740517769997)
            ·
              refine ⟨396901020982402694163749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1058402722619740517769997 396901020982402694163749)
              ·
                refine ⟨74418941434200505155703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 396901020982402694163749 74418941434200505155703)
                ·
                  rfl

theorem cell19_244570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_244570 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244570 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244570 prefixEnd_244570 := by exact prefixLift 244570
  have htrace : WordTrace (prefixWord ++ tailWord_244570) baseStart_244570 baseEnd_244570 := by
    simpa [prefixWord, tailWord_244570, baseEnd_244570] using wordTrace_append hprefix tailTrace_244570
  have hstable : (prefixWord ++ tailWord_244570).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244570).length < 2 ^ (prefixWord ++ tailWord_244570).sum := by decide
  have hdescent : baseEnd_244570 < baseStart_244570 := by decide
  rcases family_descends (prefixWord ++ tailWord_244570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244591 : List Nat := [1, 1, 2, 1, 3, 1, 1, 9]
def baseStart_244591 : Nat := 118140960795 + 244591 * 2 ^ 59
def prefixEnd_244591 : Nat := 4983230072969 + 3 ^ 40 * 244591 * 2
def baseEnd_244591 : Nat := 74425331415678678688979

theorem tailTrace_244591 : CollatzResearch.WordTrace tailWord_244591 prefixEnd_244591 74425331415678678688979 := by
  unfold tailWord_244591
  simp only [CollatzResearch.WordTrace]
  refine ⟨8920966656896054662205627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5947311104597369774803751 8920966656896054662205627)
  ·
    refine ⟨13381449985344081993308441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8920966656896054662205627 13381449985344081993308441)
    ·
      refine ⟨10036087489008061494981331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13381449985344081993308441 10036087489008061494981331)
      ·
        refine ⟨15054131233512092242471997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10036087489008061494981331 15054131233512092242471997)
        ·
          refine ⟨5645299212567034590926999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15054131233512092242471997 5645299212567034590926999)
          ·
            refine ⟨8467948818850551886390499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5645299212567034590926999 8467948818850551886390499)
            ·
              refine ⟨12701923228275827829585749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8467948818850551886390499 12701923228275827829585749)
              ·
                refine ⟨74425331415678678688979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12701923228275827829585749 74425331415678678688979)
                ·
                  rfl

theorem cell19_244591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_244591 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244591 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244591 prefixEnd_244591 := by exact prefixLift 244591
  have htrace : WordTrace (prefixWord ++ tailWord_244591) baseStart_244591 baseEnd_244591 := by
    simpa [prefixWord, tailWord_244591, baseEnd_244591] using wordTrace_append hprefix tailTrace_244591
  have hstable : (prefixWord ++ tailWord_244591).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244591).length < 2 ^ (prefixWord ++ tailWord_244591).sum := by decide
  have hdescent : baseEnd_244591 < baseStart_244591 := by decide
  rcases family_descends (prefixWord ++ tailWord_244591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244642 : List Nat := [3, 3, 1, 2, 2, 3, 2, 3]
def baseStart_244642 : Nat := 118140960795 + 244642 * 2 ^ 59
def prefixEnd_244642 : Nat := 4983230072969 + 3 ^ 40 * 244642 * 2
def baseEnd_244642 : Nat := 74440849942125671555507

theorem tailTrace_244642 : CollatzResearch.WordTrace tailWord_244642 prefixEnd_244642 74440849942125671555507 := by
  unfold tailWord_244642
  simp only [CollatzResearch.WordTrace]
  refine ⟨2230706694927822593078045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5948551186474193581541453 2230706694927822593078045)
  ·
    refine ⟨836515010597933472404267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2230706694927822593078045 836515010597933472404267)
    ·
      refine ⟨1254772515896900208606401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 836515010597933472404267 1254772515896900208606401)
      ·
        refine ⟨941079386922675156454801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1254772515896900208606401 941079386922675156454801)
        ·
          refine ⟨705809540192006367341101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 941079386922675156454801 705809540192006367341101)
          ·
            refine ⟨264678577572002387752913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 705809540192006367341101 264678577572002387752913)
            ·
              refine ⟨198508933179001790814685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264678577572002387752913 198508933179001790814685)
              ·
                refine ⟨74440849942125671555507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198508933179001790814685 74440849942125671555507)
                ·
                  rfl

theorem cell19_244642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_244642 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244642 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244642 prefixEnd_244642 := by exact prefixLift 244642
  have htrace : WordTrace (prefixWord ++ tailWord_244642) baseStart_244642 baseEnd_244642 := by
    simpa [prefixWord, tailWord_244642, baseEnd_244642] using wordTrace_append hprefix tailTrace_244642
  have hstable : (prefixWord ++ tailWord_244642).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244642).length < 2 ^ (prefixWord ++ tailWord_244642).sum := by decide
  have hdescent : baseEnd_244642 < baseStart_244642 := by decide
  rcases family_descends (prefixWord ++ tailWord_244642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244665 : List Nat := [1, 2, 1, 4, 2, 4, 5]
def baseStart_244665 : Nat := 118140960795 + 244665 * 2 ^ 59
def prefixEnd_244665 : Nat := 4983230072969 + 3 ^ 40 * 244665 * 2
def baseEnd_244665 : Nat := 24815949497756144348111

theorem tailTrace_244665 : CollatzResearch.WordTrace tailWord_244665 prefixEnd_244665 24815949497756144348111 := by
  unfold tailWord_244665
  simp only [CollatzResearch.WordTrace]
  refine ⟨8923665658627965300399449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5949110439085310200266299 8923665658627965300399449)
  ·
    refine ⟨6692749243970973975299587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8923665658627965300399449 6692749243970973975299587)
    ·
      refine ⟨10039123865956460962949381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6692749243970973975299587 10039123865956460962949381)
      ·
        refine ⟨1882335724866836430553009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10039123865956460962949381 1882335724866836430553009)
        ·
          refine ⟨1411751793650127322914757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1882335724866836430553009 1411751793650127322914757)
          ·
            refine ⟨264703461309398873046517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1411751793650127322914757 264703461309398873046517)
            ·
              refine ⟨24815949497756144348111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 264703461309398873046517 24815949497756144348111)
              ·
                rfl

theorem cell19_244665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 5].length) (baseStart_244665 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244665 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244665 prefixEnd_244665 := by exact prefixLift 244665
  have htrace : WordTrace (prefixWord ++ tailWord_244665) baseStart_244665 baseEnd_244665 := by
    simpa [prefixWord, tailWord_244665, baseEnd_244665] using wordTrace_append hprefix tailTrace_244665
  have hstable : (prefixWord ++ tailWord_244665).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244665).length < 2 ^ (prefixWord ++ tailWord_244665).sum := by decide
  have hdescent : baseEnd_244665 < baseStart_244665 := by decide
  rcases family_descends (prefixWord ++ tailWord_244665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244684 : List Nat := [2, 2, 1, 4, 1, 1, 4, 4]
def baseStart_244684 : Nat := 118140960795 + 244684 * 2 ^ 59
def prefixEnd_244684 : Nat := 4983230072969 + 3 ^ 40 * 244684 * 2
def baseEnd_244684 : Nat := 74453629905082018622059

theorem tailTrace_244684 : CollatzResearch.WordTrace tailWord_244684 prefixEnd_244684 74453629905082018622059 := by
  unfold tailWord_244684
  simp only [CollatzResearch.WordTrace]
  refine ⟨4462179322779565772670553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5949572430372754363560737 4462179322779565772670553)
  ·
    refine ⟨3346634492084674329502915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4462179322779565772670553 3346634492084674329502915)
    ·
      refine ⟨5019951738127011494254373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3346634492084674329502915 5019951738127011494254373)
      ·
        refine ⟨941240950898814655172695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5019951738127011494254373 941240950898814655172695)
        ·
          refine ⟨1411861426348221982759043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941240950898814655172695 1411861426348221982759043)
          ·
            refine ⟨2117792139522332974138565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411861426348221982759043 2117792139522332974138565)
            ·
              refine ⟨397086026160437432650981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2117792139522332974138565 397086026160437432650981)
              ·
                refine ⟨74453629905082018622059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 397086026160437432650981 74453629905082018622059)
                ·
                  rfl

theorem cell19_244684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_244684 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244684 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244684 prefixEnd_244684 := by exact prefixLift 244684
  have htrace : WordTrace (prefixWord ++ tailWord_244684) baseStart_244684 baseEnd_244684 := by
    simpa [prefixWord, tailWord_244684, baseEnd_244684] using wordTrace_append hprefix tailTrace_244684
  have hstable : (prefixWord ++ tailWord_244684).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244684).length < 2 ^ (prefixWord ++ tailWord_244684).sum := by decide
  have hdescent : baseEnd_244684 < baseStart_244684 := by decide
  rcases family_descends (prefixWord ++ tailWord_244684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244722 : List Nat := [3, 2, 1, 5, 8]
def baseStart_244722 : Nat := 118140960795 + 244722 * 2 ^ 59
def prefixEnd_244722 : Nat := 4983230072969 + 3 ^ 40 * 244722 * 2
def baseEnd_244722 : Nat := 2757970101063303325093

theorem tailTrace_244722 : CollatzResearch.WordTrace tailWord_244722 prefixEnd_244722 2757970101063303325093 := by
  unfold tailWord_244722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2231436154855366008806105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5950496412947642690149613 2231436154855366008806105)
  ·
    refine ⟨1673577116141524506604579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2231436154855366008806105 1673577116141524506604579)
    ·
      refine ⟨2510365674212286759906869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1673577116141524506604579 2510365674212286759906869)
      ·
        refine ⟨235346781957401883741269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2510365674212286759906869 235346781957401883741269)
        ·
          refine ⟨2757970101063303325093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 235346781957401883741269 2757970101063303325093)
          ·
            rfl

theorem cell19_244722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 8].length) (baseStart_244722 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244722 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244722 prefixEnd_244722 := by exact prefixLift 244722
  have htrace : WordTrace (prefixWord ++ tailWord_244722) baseStart_244722 baseEnd_244722 := by
    simpa [prefixWord, tailWord_244722, baseEnd_244722] using wordTrace_append hprefix tailTrace_244722
  have hstable : (prefixWord ++ tailWord_244722).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244722).length < 2 ^ (prefixWord ++ tailWord_244722).sum := by decide
  have hdescent : baseEnd_244722 < baseStart_244722 := by decide
  rcases family_descends (prefixWord ++ tailWord_244722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244800 : List Nat := [2, 1, 1, 2, 2, 3, 2, 6]
def baseStart_244800 : Nat := 118140960795 + 244800 * 2 ^ 59
def prefixEnd_244800 : Nat := 4983230072969 + 3 ^ 40 * 244800 * 2
def baseEnd_244800 : Nat := 74488926945628120043965

theorem tailTrace_244800 : CollatzResearch.WordTrace tailWord_244800 prefixEnd_244800 74488926945628120043965 := by
  unfold tailWord_244800
  simp only [CollatzResearch.WordTrace]
  refine ⟨4464294756569441678281927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5952393008759255571042569 4464294756569441678281927)
  ·
    refine ⟨6696442134854162517422891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4464294756569441678281927 6696442134854162517422891)
    ·
      refine ⟨10044663202281243776134337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6696442134854162517422891 10044663202281243776134337)
      ·
        refine ⟨7533497401710932832100753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10044663202281243776134337 7533497401710932832100753)
        ·
          refine ⟨5650123051283199624075565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7533497401710932832100753 5650123051283199624075565)
          ·
            refine ⟨2118796144231199859028337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5650123051283199624075565 2118796144231199859028337)
            ·
              refine ⟨1589097108173399894271253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2118796144231199859028337 1589097108173399894271253)
              ·
                refine ⟨74488926945628120043965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1589097108173399894271253 74488926945628120043965)
                ·
                  rfl

theorem cell19_244800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_244800 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244800 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244800 prefixEnd_244800 := by exact prefixLift 244800
  have htrace : WordTrace (prefixWord ++ tailWord_244800) baseStart_244800 baseEnd_244800 := by
    simpa [prefixWord, tailWord_244800, baseEnd_244800] using wordTrace_append hprefix tailTrace_244800
  have hstable : (prefixWord ++ tailWord_244800).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244800).length < 2 ^ (prefixWord ++ tailWord_244800).sum := by decide
  have hdescent : baseEnd_244800 < baseStart_244800 := by decide
  rcases family_descends (prefixWord ++ tailWord_244800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244813 : List Nat := [1, 6, 1, 1, 1, 4, 2, 3]
def baseStart_244813 : Nat := 118140960795 + 244813 * 2 ^ 59
def prefixEnd_244813 : Nat := 4983230072969 + 3 ^ 40 * 244813 * 2
def baseEnd_244813 : Nat := 74492882648447941755041

theorem tailTrace_244813 : CollatzResearch.WordTrace tailWord_244813 prefixEnd_244813 74492882648447941755041 := by
  unfold tailWord_244813
  simp only [CollatzResearch.WordTrace]
  refine ⟨8929063662091786576787093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5952709108061191051191395 8929063662091786576787093)
  ·
    refine ⟨418549859160552495786895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8929063662091786576787093 418549859160552495786895)
    ·
      refine ⟨627824788740828743680343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418549859160552495786895 627824788740828743680343)
      ·
        refine ⟨941737183111243115520515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627824788740828743680343 941737183111243115520515)
        ·
          refine ⟨1412605774666864673280773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941737183111243115520515 1412605774666864673280773)
          ·
            refine ⟨264863582750037126240145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1412605774666864673280773 264863582750037126240145)
            ·
              refine ⟨198647687062527844680109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264863582750037126240145 198647687062527844680109)
              ·
                refine ⟨74492882648447941755041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198647687062527844680109 74492882648447941755041)
                ·
                  rfl

theorem cell19_244813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 3].length) (baseStart_244813 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244813 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244813 prefixEnd_244813 := by exact prefixLift 244813
  have htrace : WordTrace (prefixWord ++ tailWord_244813) baseStart_244813 baseEnd_244813 := by
    simpa [prefixWord, tailWord_244813, baseEnd_244813] using wordTrace_append hprefix tailTrace_244813
  have hstable : (prefixWord ++ tailWord_244813).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244813).length < 2 ^ (prefixWord ++ tailWord_244813).sum := by decide
  have hdescent : baseEnd_244813 < baseStart_244813 := by decide
  rcases family_descends (prefixWord ++ tailWord_244813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244817 : List Nat := [1, 2, 2, 1, 3, 1, 6, 3]
def baseStart_244817 : Nat := 118140960795 + 244817 * 2 ^ 59
def prefixEnd_244817 : Nat := 4983230072969 + 3 ^ 40 * 244817 * 2
def baseEnd_244817 : Nat := 74494099787777117666141

theorem tailTrace_244817 : CollatzResearch.WordTrace tailWord_244817 prefixEnd_244817 74494099787777117666141 := by
  unfold tailWord_244817
  simp only [CollatzResearch.WordTrace]
  refine ⟨8929209554077295259932705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5952806369384863506621803 8929209554077295259932705)
  ·
    refine ⟨6696907165557971444949529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8929209554077295259932705 6696907165557971444949529)
    ·
      refine ⟨5022680374168478583712147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6696907165557971444949529 5022680374168478583712147)
      ·
        refine ⟨7534020561252717875568221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5022680374168478583712147 7534020561252717875568221)
        ·
          refine ⟨2825257710469769203338083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7534020561252717875568221 2825257710469769203338083)
          ·
            refine ⟨4237886565704653805007125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2825257710469769203338083 4237886565704653805007125)
            ·
              refine ⟨198650932767405647109709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4237886565704653805007125 198650932767405647109709)
              ·
                refine ⟨74494099787777117666141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198650932767405647109709 74494099787777117666141)
                ·
                  rfl

theorem cell19_244817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 3].length) (baseStart_244817 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244817 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244817 prefixEnd_244817 := by exact prefixLift 244817
  have htrace : WordTrace (prefixWord ++ tailWord_244817) baseStart_244817 baseEnd_244817 := by
    simpa [prefixWord, tailWord_244817, baseEnd_244817] using wordTrace_append hprefix tailTrace_244817
  have hstable : (prefixWord ++ tailWord_244817).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244817).length < 2 ^ (prefixWord ++ tailWord_244817).sum := by decide
  have hdescent : baseEnd_244817 < baseStart_244817 := by decide
  rcases family_descends (prefixWord ++ tailWord_244817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244834 : List Nat := [3, 3, 2, 2, 1, 3, 5]
def baseStart_244834 : Nat := 118140960795 + 244834 * 2 ^ 59
def prefixEnd_244834 : Nat := 4983230072969 + 3 ^ 40 * 244834 * 2
def baseEnd_244834 : Nat := 24833090876642038429439

theorem tailTrace_244834 : CollatzResearch.WordTrace tailWord_244834 prefixEnd_244834 24833090876642038429439 := by
  unfold tailWord_244834
  simp only [CollatzResearch.WordTrace]
  refine ⟨2232457398753926790825389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5953219730010471442201037 2232457398753926790825389)
  ·
    refine ⟨837171524532722546559521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2232457398753926790825389 837171524532722546559521)
    ·
      refine ⟨627878643399541909919641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 837171524532722546559521 627878643399541909919641)
      ·
        refine ⟨470908982549656432439731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 627878643399541909919641 470908982549656432439731)
        ·
          refine ⟨706363473824484648659597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470908982549656432439731 706363473824484648659597)
          ·
            refine ⟨264886302684181743247349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 706363473824484648659597 264886302684181743247349)
            ·
              refine ⟨24833090876642038429439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 264886302684181743247349 24833090876642038429439)
              ·
                rfl

theorem cell19_244834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 5].length) (baseStart_244834 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244834 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244834 prefixEnd_244834 := by exact prefixLift 244834
  have htrace : WordTrace (prefixWord ++ tailWord_244834) baseStart_244834 baseEnd_244834 := by
    simpa [prefixWord, tailWord_244834, baseEnd_244834] using wordTrace_append hprefix tailTrace_244834
  have hstable : (prefixWord ++ tailWord_244834).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244834).length < 2 ^ (prefixWord ++ tailWord_244834).sum := by decide
  have hdescent : baseEnd_244834 < baseStart_244834 := by decide
  rcases family_descends (prefixWord ++ tailWord_244834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244895 : List Nat := [1, 1, 2, 6, 9]
def baseStart_244895 : Nat := 118140960795 + 244895 * 2 ^ 59
def prefixEnd_244895 : Nat := 4983230072969 + 3 ^ 40 * 244895 * 2
def baseEnd_244895 : Nat := 2759919777951705478985

theorem tailTrace_244895 : CollatzResearch.WordTrace tailWord_244895 prefixEnd_244895 2759919777951705478985 := by
  unfold tailWord_244895
  simp only [CollatzResearch.WordTrace]
  refine ⟨8932054447794714581272139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5954702965196476387514759 8932054447794714581272139)
  ·
    refine ⟨13398081671692071871908209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8932054447794714581272139 13398081671692071871908209)
    ·
      refine ⟨10048561253769053903931157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13398081671692071871908209 10048561253769053903931157)
      ·
        refine ⟨471026308770424401746773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10048561253769053903931157 471026308770424401746773)
        ·
          refine ⟨2759919777951705478985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 471026308770424401746773 2759919777951705478985)
          ·
            rfl

theorem cell19_244895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 9].length) (baseStart_244895 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244895 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244895 prefixEnd_244895 := by exact prefixLift 244895
  have htrace : WordTrace (prefixWord ++ tailWord_244895) baseStart_244895 baseEnd_244895 := by
    simpa [prefixWord, tailWord_244895, baseEnd_244895] using wordTrace_append hprefix tailTrace_244895
  have hstable : (prefixWord ++ tailWord_244895).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244895).length < 2 ^ (prefixWord ++ tailWord_244895).sum := by decide
  have hdescent : baseEnd_244895 < baseStart_244895 := by decide
  rcases family_descends (prefixWord ++ tailWord_244895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244948 : List Nat := [2, 4, 1, 4, 1, 1, 6]
def baseStart_244948 : Nat := 118140960795 + 244948 * 2 ^ 59
def prefixEnd_244948 : Nat := 4983230072969 + 3 ^ 40 * 244948 * 2
def baseEnd_244948 : Nat := 24844653700269209584891

theorem tailTrace_244948 : CollatzResearch.WordTrace tailWord_244948 prefixEnd_244948 24844653700269209584891 := by
  unfold tailWord_244948
  simp only [CollatzResearch.WordTrace]
  refine ⟨4466993758301352316475749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5955991677735136421967665 4466993758301352316475749)
  ·
    refine ⟨837561329681503559339203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4466993758301352316475749 837561329681503559339203)
    ·
      refine ⟨1256341994522255339008805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 837561329681503559339203 1256341994522255339008805)
      ·
        refine ⟨235564123972922876064151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1256341994522255339008805 235564123972922876064151)
        ·
          refine ⟨353346185959384314096227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235564123972922876064151 353346185959384314096227)
          ·
            refine ⟨530019278939076471144341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353346185959384314096227 530019278939076471144341)
            ·
              refine ⟨24844653700269209584891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 530019278939076471144341 24844653700269209584891)
              ·
                rfl

theorem cell19_244948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 6].length) (baseStart_244948 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244948 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244948 prefixEnd_244948 := by exact prefixLift 244948
  have htrace : WordTrace (prefixWord ++ tailWord_244948) baseStart_244948 baseEnd_244948 := by
    simpa [prefixWord, tailWord_244948, baseEnd_244948] using wordTrace_append hprefix tailTrace_244948
  have hstable : (prefixWord ++ tailWord_244948).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244948).length < 2 ^ (prefixWord ++ tailWord_244948).sum := by decide
  have hdescent : baseEnd_244948 < baseStart_244948 := by decide
  rcases family_descends (prefixWord ++ tailWord_244948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244980 : List Nat := [2, 6, 1, 2, 1, 2, 2, 3]
def baseStart_244980 : Nat := 118140960795 + 244980 * 2 ^ 59
def prefixEnd_244980 : Nat := 4983230072969 + 3 ^ 40 * 244980 * 2
def baseEnd_244980 : Nat := 74543698215441036043475

theorem tailTrace_244980 : CollatzResearch.WordTrace tailWord_244980 prefixEnd_244980 74543698215441036043475 := by
  unfold tailWord_244980
  simp only [CollatzResearch.WordTrace]
  refine ⟨4467577326243387049058197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5956769768324516065410929 4467577326243387049058197)
  ·
    refine ⟨209417687167658767924603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4467577326243387049058197 209417687167658767924603)
    ·
      refine ⟨314126530751488151886905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209417687167658767924603 314126530751488151886905)
      ·
        refine ⟨235594898063616113915179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314126530751488151886905 235594898063616113915179)
        ·
          refine ⟨353392347095424170872769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235594898063616113915179 353392347095424170872769)
          ·
            refine ⟨265044260321568128154577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353392347095424170872769 265044260321568128154577)
            ·
              refine ⟨198783195241176096115933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265044260321568128154577 198783195241176096115933)
              ·
                refine ⟨74543698215441036043475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198783195241176096115933 74543698215441036043475)
                ·
                  rfl

theorem cell19_244980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 3].length) (baseStart_244980 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244980 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244980 prefixEnd_244980 := by exact prefixLift 244980
  have htrace : WordTrace (prefixWord ++ tailWord_244980) baseStart_244980 baseEnd_244980 := by
    simpa [prefixWord, tailWord_244980, baseEnd_244980] using wordTrace_append hprefix tailTrace_244980
  have hstable : (prefixWord ++ tailWord_244980).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244980).length < 2 ^ (prefixWord ++ tailWord_244980).sum := by decide
  have hdescent : baseEnd_244980 < baseStart_244980 := by decide
  rcases family_descends (prefixWord ++ tailWord_244980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244988 : List Nat := [2, 2, 2, 1, 5, 1, 1, 5]
def baseStart_244988 : Nat := 118140960795 + 244988 * 2 ^ 59
def prefixEnd_244988 : Nat := 4983230072969 + 3 ^ 40 * 244988 * 2
def baseEnd_244988 : Nat := 74546132494099387865675

theorem tailTrace_244988 : CollatzResearch.WordTrace tailWord_244988 prefixEnd_244988 74546132494099387865675 := by
  unfold tailWord_244988
  simp only [CollatzResearch.WordTrace]
  refine ⟨4467723218228895732203809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5956964290971860976271745 4467723218228895732203809)
  ·
    refine ⟨3350792413671671799152857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4467723218228895732203809 3350792413671671799152857)
    ·
      refine ⟨2513094310253753849364643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3350792413671671799152857 2513094310253753849364643)
      ·
        refine ⟨3769641465380630774046965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2513094310253753849364643 3769641465380630774046965)
        ·
          refine ⟨353403887379434135066903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3769641465380630774046965 353403887379434135066903)
          ·
            refine ⟨530105831069151202600355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353403887379434135066903 530105831069151202600355)
            ·
              refine ⟨795158746603726803900533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530105831069151202600355 795158746603726803900533)
              ·
                refine ⟨74546132494099387865675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 795158746603726803900533 74546132494099387865675)
                ·
                  rfl

theorem cell19_244988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_244988 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_244988 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_244988 prefixEnd_244988 := by exact prefixLift 244988
  have htrace : WordTrace (prefixWord ++ tailWord_244988) baseStart_244988 baseEnd_244988 := by
    simpa [prefixWord, tailWord_244988, baseEnd_244988] using wordTrace_append hprefix tailTrace_244988
  have hstable : (prefixWord ++ tailWord_244988).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244988).length < 2 ^ (prefixWord ++ tailWord_244988).sum := by decide
  have hdescent : baseEnd_244988 < baseStart_244988 := by decide
  rcases family_descends (prefixWord ++ tailWord_244988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245022 : List Nat := [4, 3, 2, 1, 2, 1, 2, 4]
def baseStart_245022 : Nat := 118140960795 + 245022 * 2 ^ 59
def prefixEnd_245022 : Nat := 4983230072969 + 3 ^ 40 * 245022 * 2
def baseEnd_245022 : Nat := 74556478178397383110027

theorem tailTrace_245022 : CollatzResearch.WordTrace tailWord_245022 prefixEnd_245022 74556478178397383110027 := by
  unfold tailWord_245022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1117085814791826908893165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5957791012223076847430213 1117085814791826908893165)
  ·
    refine ⟨418907180546935090834937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1117085814791826908893165 418907180546935090834937)
    ·
      refine ⟨314180385410201318126203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418907180546935090834937 314180385410201318126203)
      ·
        refine ⟨471270578115301977189305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314180385410201318126203 471270578115301977189305)
        ·
          refine ⟨353452933586476482891979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471270578115301977189305 353452933586476482891979)
          ·
            refine ⟨530179400379714724337969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353452933586476482891979 530179400379714724337969)
            ·
              refine ⟨397634550284786043253477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530179400379714724337969 397634550284786043253477)
              ·
                refine ⟨74556478178397383110027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 397634550284786043253477 74556478178397383110027)
                ·
                  rfl

theorem cell19_245022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_245022 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_245022 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_245022 prefixEnd_245022 := by exact prefixLift 245022
  have htrace : WordTrace (prefixWord ++ tailWord_245022) baseStart_245022 baseEnd_245022 := by
    simpa [prefixWord, tailWord_245022, baseEnd_245022] using wordTrace_append hprefix tailTrace_245022
  have hstable : (prefixWord ++ tailWord_245022).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245022).length < 2 ^ (prefixWord ++ tailWord_245022).sum := by decide
  have hdescent : baseEnd_245022 < baseStart_245022 := by decide
  rcases family_descends (prefixWord ++ tailWord_245022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245062 : List Nat := [6, 1, 1, 3, 8]
def baseStart_245062 : Nat := 118140960795 + 245062 * 2 ^ 59
def prefixEnd_245062 : Nat := 4983230072969 + 3 ^ 40 * 245062 * 2
def baseEnd_245062 : Nat := 2761801835988486748927

theorem tailTrace_245062 : CollatzResearch.WordTrace tailWord_245062 prefixEnd_245062 2761801835988486748927 := by
  unfold tailWord_245062
  simp only [CollatzResearch.WordTrace]
  refine ⟨279317044943428190706295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5958763625459801401734293 279317044943428190706295)
  ·
    refine ⟨418975567415142286059443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279317044943428190706295 418975567415142286059443)
    ·
      refine ⟨628463351122713429089165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418975567415142286059443 628463351122713429089165)
      ·
        refine ⟨235673756671017535908437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 628463351122713429089165 235673756671017535908437)
        ·
          refine ⟨2761801835988486748927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 235673756671017535908437 2761801835988486748927)
          ·
            rfl

theorem cell19_245062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 8].length) (baseStart_245062 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_245062 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_245062 prefixEnd_245062 := by exact prefixLift 245062
  have htrace : WordTrace (prefixWord ++ tailWord_245062) baseStart_245062 baseEnd_245062 := by
    simpa [prefixWord, tailWord_245062, baseEnd_245062] using wordTrace_append hprefix tailTrace_245062
  have hstable : (prefixWord ++ tailWord_245062).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245062).length < 2 ^ (prefixWord ++ tailWord_245062).sum := by decide
  have hdescent : baseEnd_245062 < baseStart_245062 := by decide
  rcases family_descends (prefixWord ++ tailWord_245062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245121 : List Nat := [1, 2, 4, 3, 2, 1, 6]
def baseStart_245121 : Nat := 118140960795 + 245121 * 2 ^ 59
def prefixEnd_245121 : Nat := 4983230072969 + 3 ^ 40 * 245121 * 2
def baseEnd_245121 : Nat := 24862200792264828969919

theorem tailTrace_245121 : CollatzResearch.WordTrace tailWord_245121 prefixEnd_245121 24862200792264828969919 := by
  unfold tailWord_245121
  simp only [CollatzResearch.WordTrace]
  refine ⟨8940297344975955178999217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5960198229983970119332811 8940297344975955178999217)
  ·
    refine ⟨6705223008731966384249413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8940297344975955178999217 6705223008731966384249413)
    ·
      refine ⟨1257229314137243697046765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6705223008731966384249413 1257229314137243697046765)
      ·
        refine ⟨471460992801466386392537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1257229314137243697046765 471460992801466386392537)
        ·
          refine ⟨353595744601099789794403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471460992801466386392537 353595744601099789794403)
          ·
            refine ⟨530393616901649684691605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353595744601099789794403 530393616901649684691605)
            ·
              refine ⟨24862200792264828969919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 530393616901649684691605 24862200792264828969919)
              ·
                rfl

theorem cell19_245121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 6].length) (baseStart_245121 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_245121 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_245121 prefixEnd_245121 := by exact prefixLift 245121
  have htrace : WordTrace (prefixWord ++ tailWord_245121) baseStart_245121 baseEnd_245121 := by
    simpa [prefixWord, tailWord_245121, baseEnd_245121] using wordTrace_append hprefix tailTrace_245121
  have hstable : (prefixWord ++ tailWord_245121).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245121).length < 2 ^ (prefixWord ++ tailWord_245121).sum := by decide
  have hdescent : baseEnd_245121 < baseStart_245121 := by decide
  rcases family_descends (prefixWord ++ tailWord_245121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245123 : List Nat := [1, 1, 1, 3, 5, 2, 6]
def baseStart_245123 : Nat := 118140960795 + 245123 * 2 ^ 59
def prefixEnd_245123 : Nat := 4983230072969 + 3 ^ 40 * 245123 * 2
def baseEnd_245123 : Nat := 24862403648819691621769

theorem tailTrace_245123 : CollatzResearch.WordTrace tailWord_245123 prefixEnd_245123 24862403648819691621769 := by
  unfold tailWord_245123
  simp only [CollatzResearch.WordTrace]
  refine ⟨8940370290968709520572023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5960246860645806347048015 8940370290968709520572023)
  ·
    refine ⟨13410555436453064280858035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8940370290968709520572023 13410555436453064280858035)
    ·
      refine ⟨20115833154679596421287053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13410555436453064280858035 20115833154679596421287053)
      ·
        refine ⟨7543437433004848657982645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20115833154679596421287053 7543437433004848657982645)
        ·
          refine ⟨707197259344204561685873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7543437433004848657982645 707197259344204561685873)
          ·
            refine ⟨530397944508153421264405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 707197259344204561685873 530397944508153421264405)
            ·
              refine ⟨24862403648819691621769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 530397944508153421264405 24862403648819691621769)
              ·
                rfl

theorem cell19_245123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 6].length) (baseStart_245123 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_245123 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_245123 prefixEnd_245123 := by exact prefixLift 245123
  have htrace : WordTrace (prefixWord ++ tailWord_245123) baseStart_245123 baseEnd_245123 := by
    simpa [prefixWord, tailWord_245123, baseEnd_245123] using wordTrace_append hprefix tailTrace_245123
  have hstable : (prefixWord ++ tailWord_245123).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245123).length < 2 ^ (prefixWord ++ tailWord_245123).sum := by decide
  have hdescent : baseEnd_245123 < baseStart_245123 := by decide
  rcases family_descends (prefixWord ++ tailWord_245123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245252 : List Nat := [2, 3, 2, 3, 2, 2, 1, 4]
def baseStart_245252 : Nat := 118140960795 + 245252 * 2 ^ 59
def prefixEnd_245252 : Nat := 4983230072969 + 3 ^ 40 * 245252 * 2
def baseEnd_245252 : Nat := 74626463689824997998289

theorem tailTrace_245252 : CollatzResearch.WordTrace tailWord_245252 prefixEnd_245252 74626463689824997998289 := by
  unfold tailWord_245252
  simp only [CollatzResearch.WordTrace]
  refine ⟨4472537653750682276009005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5963383538334243034678673 4472537653750682276009005)
  ·
    refine ⟨1677201620156505853503377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4472537653750682276009005 1677201620156505853503377)
    ·
      refine ⟨1257901215117379390127533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1677201620156505853503377 1257901215117379390127533)
      ·
        refine ⟨471712955669017271297825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1257901215117379390127533 471712955669017271297825)
        ·
          refine ⟨353784716751762953473369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471712955669017271297825 353784716751762953473369)
          ·
            refine ⟨265338537563822215105027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353784716751762953473369 265338537563822215105027)
            ·
              refine ⟨398007806345733322657541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265338537563822215105027 398007806345733322657541)
              ·
                refine ⟨74626463689824997998289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 398007806345733322657541 74626463689824997998289)
                ·
                  rfl

theorem cell19_245252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_245252 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_245252 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_245252 prefixEnd_245252 := by exact prefixLift 245252
  have htrace : WordTrace (prefixWord ++ tailWord_245252) baseStart_245252 baseEnd_245252 := by
    simpa [prefixWord, tailWord_245252, baseEnd_245252] using wordTrace_append hprefix tailTrace_245252
  have hstable : (prefixWord ++ tailWord_245252).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245252).length < 2 ^ (prefixWord ++ tailWord_245252).sum := by decide
  have hdescent : baseEnd_245252 < baseStart_245252 := by decide
  rcases family_descends (prefixWord ++ tailWord_245252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245256 : List Nat := [2, 1, 3, 2, 1, 1, 5, 4]
def baseStart_245256 : Nat := 118140960795 + 245256 * 2 ^ 59
def prefixEnd_245256 : Nat := 4983230072969 + 3 ^ 40 * 245256 * 2
def baseEnd_245256 : Nat := 74627680829154173909389

theorem tailTrace_245256 : CollatzResearch.WordTrace tailWord_245256 prefixEnd_245256 74627680829154173909389 := by
  unfold tailWord_245256
  simp only [CollatzResearch.WordTrace]
  refine ⟨4472610599743436617581811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5963480799657915490109081 4472610599743436617581811)
  ·
    refine ⟨6708915899615154926372717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4472610599743436617581811 6708915899615154926372717)
    ·
      refine ⟨2515843462355683097389769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6708915899615154926372717 2515843462355683097389769)
      ·
        refine ⟨1886882596766762323042327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2515843462355683097389769 1886882596766762323042327)
        ·
          refine ⟨2830323895150143484563491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1886882596766762323042327 2830323895150143484563491)
          ·
            refine ⟨4245485842725215226845237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2830323895150143484563491 4245485842725215226845237)
            ·
              refine ⟨398014297755488927516741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4245485842725215226845237 398014297755488927516741)
              ·
                refine ⟨74627680829154173909389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 398014297755488927516741 74627680829154173909389)
                ·
                  rfl

theorem cell19_245256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_245256 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_245256 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_245256 prefixEnd_245256 := by exact prefixLift 245256
  have htrace : WordTrace (prefixWord ++ tailWord_245256) baseStart_245256 baseEnd_245256 := by
    simpa [prefixWord, tailWord_245256, baseEnd_245256] using wordTrace_append hprefix tailTrace_245256
  have hstable : (prefixWord ++ tailWord_245256).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245256).length < 2 ^ (prefixWord ++ tailWord_245256).sum := by decide
  have hdescent : baseEnd_245256 < baseStart_245256 := by decide
  rcases family_descends (prefixWord ++ tailWord_245256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245313 : List Nat := [1, 2, 5, 1, 1, 1, 2, 6]
def baseStart_245313 : Nat := 118140960795 + 245313 * 2 ^ 59
def prefixEnd_245313 : Nat := 4983230072969 + 3 ^ 40 * 245313 * 2
def baseEnd_245313 : Nat := 74645025064594930642567

theorem tailTrace_245313 : CollatzResearch.WordTrace tailWord_245313 prefixEnd_245313 74645025064594930642567 := by
  unfold tailWord_245313
  simp only [CollatzResearch.WordTrace]
  refine ⟨8947300160280371969988593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5964866773520247979992395 8947300160280371969988593)
  ·
    refine ⟨6710475120210278977491445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8947300160280371969988593 6710475120210278977491445)
    ·
      refine ⟨629107042519713654139823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6710475120210278977491445 629107042519713654139823)
      ·
        refine ⟨943660563779570481209735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629107042519713654139823 943660563779570481209735)
        ·
          refine ⟨1415490845669355721814603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 943660563779570481209735 1415490845669355721814603)
          ·
            refine ⟨2123236268504033582721905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1415490845669355721814603 2123236268504033582721905)
            ·
              refine ⟨1592427201378025187041429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2123236268504033582721905 1592427201378025187041429)
              ·
                refine ⟨74645025064594930642567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1592427201378025187041429 74645025064594930642567)
                ·
                  rfl

theorem cell19_245313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 6].length) (baseStart_245313 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_245313 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_245313 prefixEnd_245313 := by exact prefixLift 245313
  have htrace : WordTrace (prefixWord ++ tailWord_245313) baseStart_245313 baseEnd_245313 := by
    simpa [prefixWord, tailWord_245313, baseEnd_245313] using wordTrace_append hprefix tailTrace_245313
  have hstable : (prefixWord ++ tailWord_245313).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245313).length < 2 ^ (prefixWord ++ tailWord_245313).sum := by decide
  have hdescent : baseEnd_245313 < baseStart_245313 := by decide
  rcases family_descends (prefixWord ++ tailWord_245313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245330 : List Nat := [3, 2, 2, 1, 2, 2, 4, 3]
def baseStart_245330 : Nat := 118140960795 + 245330 * 2 ^ 59
def prefixEnd_245330 : Nat := 4983230072969 + 3 ^ 40 * 245330 * 2
def baseEnd_245330 : Nat := 74650197906743928264743

theorem tailTrace_245330 : CollatzResearch.WordTrace tailWord_245330 prefixEnd_245330 74650197906743928264743 := by
  unfold tailWord_245330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2236980050304695968339361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5965280134145855915571629 2236980050304695968339361)
  ·
    refine ⟨1677735037728521976254521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2236980050304695968339361 1677735037728521976254521)
    ·
      refine ⟨1258301278296391482190891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1677735037728521976254521 1258301278296391482190891)
      ·
        refine ⟨1887451917444587223286337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1258301278296391482190891 1887451917444587223286337)
        ·
          refine ⟨1415588938083440417464753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1887451917444587223286337 1415588938083440417464753)
          ·
            refine ⟨1061691703562580313098565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1415588938083440417464753 1061691703562580313098565)
            ·
              refine ⟨199067194417983808705981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1061691703562580313098565 199067194417983808705981)
              ·
                refine ⟨74650197906743928264743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199067194417983808705981 74650197906743928264743)
                ·
                  rfl

theorem cell19_245330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_245330 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_245330 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_245330 prefixEnd_245330 := by exact prefixLift 245330
  have htrace : WordTrace (prefixWord ++ tailWord_245330) baseStart_245330 baseEnd_245330 := by
    simpa [prefixWord, tailWord_245330, baseEnd_245330] using wordTrace_append hprefix tailTrace_245330
  have hstable : (prefixWord ++ tailWord_245330).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245330).length < 2 ^ (prefixWord ++ tailWord_245330).sum := by decide
  have hdescent : baseEnd_245330 < baseStart_245330 := by decide
  rcases family_descends (prefixWord ++ tailWord_245330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245332 : List Nat := [2, 4, 1, 1, 1, 2, 3, 5]
def baseStart_245332 : Nat := 118140960795 + 245332 * 2 ^ 59
def prefixEnd_245332 : Nat := 4983230072969 + 3 ^ 40 * 245332 * 2
def baseEnd_245332 : Nat := 74650806476408516220293

theorem tailTrace_245332 : CollatzResearch.WordTrace tailWord_245332 prefixEnd_245332 74650806476408516220293 := by
  unfold tailWord_245332
  simp only [CollatzResearch.WordTrace]
  refine ⟨4473996573605769107465125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5965328764807692143286833 4473996573605769107465125)
  ·
    refine ⟨838874357551081707649711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4473996573605769107465125 838874357551081707649711)
    ·
      refine ⟨1258311536326622561474567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 838874357551081707649711 1258311536326622561474567)
      ·
        refine ⟨1887467304489933842211851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1258311536326622561474567 1887467304489933842211851)
        ·
          refine ⟨2831200956734900763317777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1887467304489933842211851 2831200956734900763317777)
          ·
            refine ⟨2123400717551175572488333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2831200956734900763317777 2123400717551175572488333)
            ·
              refine ⟨796275269081690839683125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2123400717551175572488333 796275269081690839683125)
              ·
                refine ⟨74650806476408516220293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 796275269081690839683125 74650806476408516220293)
                ·
                  rfl

theorem cell19_245332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_245332 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_245332 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_245332 prefixEnd_245332 := by exact prefixLift 245332
  have htrace : WordTrace (prefixWord ++ tailWord_245332) baseStart_245332 baseEnd_245332 := by
    simpa [prefixWord, tailWord_245332, baseEnd_245332] using wordTrace_append hprefix tailTrace_245332
  have hstable : (prefixWord ++ tailWord_245332).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245332).length < 2 ^ (prefixWord ++ tailWord_245332).sum := by decide
  have hdescent : baseEnd_245332 < baseStart_245332 := by decide
  rcases family_descends (prefixWord ++ tailWord_245332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245353 : List Nat := [1, 2, 1, 1, 1, 4, 9]
def baseStart_245353 : Nat := 118140960795 + 245353 * 2 ^ 59
def prefixEnd_245353 : Nat := 4983230072969 + 3 ^ 40 * 245353 * 2
def baseEnd_245353 : Nat := 24885732152628896584523

theorem tailTrace_245353 : CollatzResearch.WordTrace tailWord_245353 prefixEnd_245353 24885732152628896584523 := by
  unfold tailWord_245353
  simp only [CollatzResearch.WordTrace]
  refine ⟨8948759080135458801444713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5965839386756972534296475 8948759080135458801444713)
  ·
    refine ⟨6711569310101594101083535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8948759080135458801444713 6711569310101594101083535)
    ·
      refine ⟨10067353965152391151625303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6711569310101594101083535 10067353965152391151625303)
      ·
        refine ⟨15101030947728586727437955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10067353965152391151625303 15101030947728586727437955)
        ·
          refine ⟨22651546421592880091156933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15101030947728586727437955 22651546421592880091156933)
          ·
            refine ⟨4247164954048665017091925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22651546421592880091156933 4247164954048665017091925)
            ·
              refine ⟨24885732152628896584523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4247164954048665017091925 24885732152628896584523)
              ·
                rfl

theorem cell19_245353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 9].length) (baseStart_245353 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_245353 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_245353 prefixEnd_245353 := by exact prefixLift 245353
  have htrace : WordTrace (prefixWord ++ tailWord_245353) baseStart_245353 baseEnd_245353 := by
    simpa [prefixWord, tailWord_245353, baseEnd_245353] using wordTrace_append hprefix tailTrace_245353
  have hstable : (prefixWord ++ tailWord_245353).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245353).length < 2 ^ (prefixWord ++ tailWord_245353).sum := by decide
  have hdescent : baseEnd_245353 < baseStart_245353 := by decide
  rcases family_descends (prefixWord ++ tailWord_245353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245444 : List Nat := [2, 3, 3, 1, 1, 1, 5, 3]
def baseStart_245444 : Nat := 118140960795 + 245444 * 2 ^ 59
def prefixEnd_245444 : Nat := 4983230072969 + 3 ^ 40 * 245444 * 2
def baseEnd_245444 : Nat := 74684886377625441731099

theorem tailTrace_245444 : CollatzResearch.WordTrace tailWord_245444 prefixEnd_245444 74684886377625441731099 := by
  unfold tailWord_245444
  simp only [CollatzResearch.WordTrace]
  refine ⟨4476039061402890671503693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5968052081870520895338257 4476039061402890671503693)
  ·
    refine ⟨1678514648026084001813885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4476039061402890671503693 1678514648026084001813885)
    ·
      refine ⟨629442993009781500680207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1678514648026084001813885 629442993009781500680207)
      ·
        refine ⟨944164489514672251020311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629442993009781500680207 944164489514672251020311)
        ·
          refine ⟨1416246734272008376530467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 944164489514672251020311 1416246734272008376530467)
          ·
            refine ⟨2124370101408012564795701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1416246734272008376530467 2124370101408012564795701)
            ·
              refine ⟨199159697007001177949597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2124370101408012564795701 199159697007001177949597)
              ·
                refine ⟨74684886377625441731099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199159697007001177949597 74684886377625441731099)
                ·
                  rfl

theorem cell19_245444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 3].length) (baseStart_245444 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_245444 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_245444 prefixEnd_245444 := by exact prefixLift 245444
  have htrace : WordTrace (prefixWord ++ tailWord_245444) baseStart_245444 baseEnd_245444 := by
    simpa [prefixWord, tailWord_245444, baseEnd_245444] using wordTrace_append hprefix tailTrace_245444
  have hstable : (prefixWord ++ tailWord_245444).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245444).length < 2 ^ (prefixWord ++ tailWord_245444).sum := by decide
  have hdescent : baseEnd_245444 < baseStart_245444 := by decide
  rcases family_descends (prefixWord ++ tailWord_245444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245503 : List Nat := [1, 1, 2, 2, 1, 3, 6, 3]
def baseStart_245503 : Nat := 118140960795 + 245503 * 2 ^ 59
def prefixEnd_245503 : Nat := 4983230072969 + 3 ^ 40 * 245503 * 2
def baseEnd_245503 : Nat := 74702839182730786419827

theorem tailTrace_245503 : CollatzResearch.WordTrace tailWord_245503 prefixEnd_245503 74702839182730786419827 := by
  unfold tailWord_245503
  simp only [CollatzResearch.WordTrace]
  refine ⟨8954230029592034419405163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5969486686394689612936775 8954230029592034419405163)
  ·
    refine ⟨13431345044388051629107745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8954230029592034419405163 13431345044388051629107745)
    ·
      refine ⟨10073508783291038721830809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13431345044388051629107745 10073508783291038721830809)
      ·
        refine ⟨7555131587468279041373107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10073508783291038721830809 7555131587468279041373107)
        ·
          refine ⟨11332697381202418562059661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7555131587468279041373107 11332697381202418562059661)
          ·
            refine ⟨4249761517950906960772373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11332697381202418562059661 4249761517950906960772373)
            ·
              refine ⟨199207571153948763786205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4249761517950906960772373 199207571153948763786205)
              ·
                refine ⟨74702839182730786419827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199207571153948763786205 74702839182730786419827)
                ·
                  rfl

theorem cell19_245503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 3].length) (baseStart_245503 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_245503 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_245503 prefixEnd_245503 := by exact prefixLift 245503
  have htrace : WordTrace (prefixWord ++ tailWord_245503) baseStart_245503 baseEnd_245503 := by
    simpa [prefixWord, tailWord_245503, baseEnd_245503] using wordTrace_append hprefix tailTrace_245503
  have hstable : (prefixWord ++ tailWord_245503).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245503).length < 2 ^ (prefixWord ++ tailWord_245503).sum := by decide
  have hdescent : baseEnd_245503 < baseStart_245503 := by decide
  rcases family_descends (prefixWord ++ tailWord_245503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245541 : List Nat := [1, 3, 1, 2, 3, 3, 2, 4]
def baseStart_245541 : Nat := 118140960795 + 245541 * 2 ^ 59
def prefixEnd_245541 : Nat := 4983230072969 + 3 ^ 40 * 245541 * 2
def baseEnd_245541 : Nat := 74714402006357957575279

theorem tailTrace_245541 : CollatzResearch.WordTrace tailWord_245541 prefixEnd_245541 74714402006357957575279 := by
  unfold tailWord_245541
  simp only [CollatzResearch.WordTrace]
  refine ⟨8955616003454366909288477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5970410668969577939525651 8955616003454366909288477)
  ·
    refine ⟨3358356001295387590983179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8955616003454366909288477 3358356001295387590983179)
    ·
      refine ⟨5037534001943081386474769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3358356001295387590983179 5037534001943081386474769)
      ·
        refine ⟨3778150501457311039856077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5037534001943081386474769 3778150501457311039856077)
        ·
          refine ⟨1416806438046491639946029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3778150501457311039856077 1416806438046491639946029)
          ·
            refine ⟨531302414267434364979761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1416806438046491639946029 531302414267434364979761)
            ·
              refine ⟨398476810700575773734821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531302414267434364979761 398476810700575773734821)
              ·
                refine ⟨74714402006357957575279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 398476810700575773734821 74714402006357957575279)
                ·
                  rfl

theorem cell19_245541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 4].length) (baseStart_245541 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_245541 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_245541 prefixEnd_245541 := by exact prefixLift 245541
  have htrace : WordTrace (prefixWord ++ tailWord_245541) baseStart_245541 baseEnd_245541 := by
    simpa [prefixWord, tailWord_245541, baseEnd_245541] using wordTrace_append hprefix tailTrace_245541
  have hstable : (prefixWord ++ tailWord_245541).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245541).length < 2 ^ (prefixWord ++ tailWord_245541).sum := by decide
  have hdescent : baseEnd_245541 < baseStart_245541 := by decide
  rcases family_descends (prefixWord ++ tailWord_245541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245558 : List Nat := [5, 1, 2, 2, 1, 1, 2, 5]
def baseStart_245558 : Nat := 118140960795 + 245558 * 2 ^ 59
def prefixEnd_245558 : Nat := 4983230072969 + 3 ^ 40 * 245558 * 2
def baseEnd_245558 : Nat := 74719574848506955197455

theorem tailTrace_245558 : CollatzResearch.WordTrace tailWord_245558 prefixEnd_245558 74719574848506955197455 := by
  unfold tailWord_245558
  simp only [CollatzResearch.WordTrace]
  refine ⟨559764752774548675791083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5970824029595185875104885 559764752774548675791083)
  ·
    refine ⟨839647129161823013686625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 559764752774548675791083 839647129161823013686625)
    ·
      refine ⟨629735346871367260264969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 839647129161823013686625 629735346871367260264969)
      ·
        refine ⟨472301510153525445198727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629735346871367260264969 472301510153525445198727)
        ·
          refine ⟨708452265230288167798091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472301510153525445198727 708452265230288167798091)
          ·
            refine ⟨1062678397845432251697137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708452265230288167798091 1062678397845432251697137)
            ·
              refine ⟨797008798384074188772853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1062678397845432251697137 797008798384074188772853)
              ·
                refine ⟨74719574848506955197455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 797008798384074188772853 74719574848506955197455)
                ·
                  rfl

theorem cell19_245558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_245558 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_245558 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_245558 prefixEnd_245558 := by exact prefixLift 245558
  have htrace : WordTrace (prefixWord ++ tailWord_245558) baseStart_245558 baseEnd_245558 := by
    simpa [prefixWord, tailWord_245558, baseEnd_245558] using wordTrace_append hprefix tailTrace_245558
  have hstable : (prefixWord ++ tailWord_245558).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245558).length < 2 ^ (prefixWord ++ tailWord_245558).sum := by decide
  have hdescent : baseEnd_245558 < baseStart_245558 := by decide
  rcases family_descends (prefixWord ++ tailWord_245558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245617 : List Nat := [1, 2, 2, 2, 1, 3, 5, 3]
def baseStart_245617 : Nat := 118140960795 + 245617 * 2 ^ 59
def prefixEnd_245617 : Nat := 4983230072969 + 3 ^ 40 * 245617 * 2
def baseEnd_245617 : Nat := 74737527653612299886183

theorem tailTrace_245617 : CollatzResearch.WordTrace tailWord_245617 prefixEnd_245617 74737527653612299886183 := by
  unfold tailWord_245617
  simp only [CollatzResearch.WordTrace]
  refine ⟨8958387951179031889055105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5972258634119354592703403 8958387951179031889055105)
  ·
    refine ⟨6718790963384273916791329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8958387951179031889055105 6718790963384273916791329)
    ·
      refine ⟨5039093222538205437593497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6718790963384273916791329 5039093222538205437593497)
      ·
        refine ⟨3779319916903654078195123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5039093222538205437593497 3779319916903654078195123)
        ·
          refine ⟨5668979875355481117292685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3779319916903654078195123 5668979875355481117292685)
          ·
            refine ⟨2125867453258305418984757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5668979875355481117292685 2125867453258305418984757)
            ·
              refine ⟨199300073742966133029821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2125867453258305418984757 199300073742966133029821)
              ·
                refine ⟨74737527653612299886183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199300073742966133029821 74737527653612299886183)
                ·
                  rfl

theorem cell19_245617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 3].length) (baseStart_245617 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_245617 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_245617 prefixEnd_245617 := by exact prefixLift 245617
  have htrace : WordTrace (prefixWord ++ tailWord_245617) baseStart_245617 baseEnd_245617 := by
    simpa [prefixWord, tailWord_245617, baseEnd_245617] using wordTrace_append hprefix tailTrace_245617
  have hstable : (prefixWord ++ tailWord_245617).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245617).length < 2 ^ (prefixWord ++ tailWord_245617).sum := by decide
  have hdescent : baseEnd_245617 < baseStart_245617 := by decide
  rcases family_descends (prefixWord ++ tailWord_245617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245693 : List Nat := [1, 4, 1, 2, 3, 3, 5]
def baseStart_245693 : Nat := 118140960795 + 245693 * 2 ^ 59
def prefixEnd_245693 : Nat := 4983230072969 + 3 ^ 40 * 245693 * 2
def baseEnd_245693 : Nat := 24920217766955547399029

theorem tailTrace_245693 : CollatzResearch.WordTrace tailWord_245693 prefixEnd_245693 24920217766955547399029 := by
  unfold tailWord_245693
  simp only [CollatzResearch.WordTrace]
  refine ⟨8961159898903696868821733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5974106599269131245881155 8961159898903696868821733)
  ·
    refine ⟨1680217481044443162904075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8961159898903696868821733 1680217481044443162904075)
    ·
      refine ⟨2520326221566664744356113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1680217481044443162904075 2520326221566664744356113)
      ·
        refine ⟨1890244666174998558267085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2520326221566664744356113 1890244666174998558267085)
        ·
          refine ⟨708841749815624459350157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1890244666174998558267085 708841749815624459350157)
          ·
            refine ⟨265815656180859172256309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 708841749815624459350157 265815656180859172256309)
            ·
              refine ⟨24920217766955547399029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 265815656180859172256309 24920217766955547399029)
              ·
                rfl

theorem cell19_245693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 5].length) (baseStart_245693 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_245693 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_245693 prefixEnd_245693 := by exact prefixLift 245693
  have htrace : WordTrace (prefixWord ++ tailWord_245693) baseStart_245693 baseEnd_245693 := by
    simpa [prefixWord, tailWord_245693, baseEnd_245693] using wordTrace_append hprefix tailTrace_245693
  have hstable : (prefixWord ++ tailWord_245693).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245693).length < 2 ^ (prefixWord ++ tailWord_245693).sum := by decide
  have hdescent : baseEnd_245693 < baseStart_245693 := by decide
  rcases family_descends (prefixWord ++ tailWord_245693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245748 : List Nat := [2, 6, 2, 9]
def baseStart_245748 : Nat := 118140960795 + 245748 * 2 ^ 59
def prefixEnd_245748 : Nat := 4983230072969 + 3 ^ 40 * 245748 * 2
def baseEnd_245748 : Nat := 923177641563491493515

theorem tailTrace_245748 : CollatzResearch.WordTrace tailWord_245748 prefixEnd_245748 923177641563491493515 := by
  unfold tailWord_245748
  simp only [CollatzResearch.WordTrace]
  refine ⟨4481582956852220631036949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5975443942469627508049265 4481582956852220631036949)
  ·
    refine ⟨210074201102447842079857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4481582956852220631036949 210074201102447842079857)
    ·
      refine ⟨157555650826835881559893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210074201102447842079857 157555650826835881559893)
      ·
        refine ⟨923177641563491493515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 157555650826835881559893 923177641563491493515)
        ·
          rfl

theorem cell19_245748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 9].length) (baseStart_245748 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_245748 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_245748 prefixEnd_245748 := by exact prefixLift 245748
  have htrace : WordTrace (prefixWord ++ tailWord_245748) baseStart_245748 baseEnd_245748 := by
    simpa [prefixWord, tailWord_245748, baseEnd_245748] using wordTrace_append hprefix tailTrace_245748
  have hstable : (prefixWord ++ tailWord_245748).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245748).length < 2 ^ (prefixWord ++ tailWord_245748).sum := by decide
  have hdescent : baseEnd_245748 < baseStart_245748 := by decide
  rcases family_descends (prefixWord ++ tailWord_245748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245750 : List Nat := [5, 1, 1, 1, 4, 7]
def baseStart_245750 : Nat := 118140960795 + 245750 * 2 ^ 59
def prefixEnd_245750 : Nat := 4983230072969 + 3 ^ 40 * 245750 * 2
def baseEnd_245750 : Nat := 8308666392923044325585

theorem tailTrace_245750 : CollatzResearch.WordTrace tailWord_245750 prefixEnd_245750 8308666392923044325585 := by
  unfold tailWord_245750
  simp only [CollatzResearch.WordTrace]
  refine ⟨560202428731074725227919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5975492573131463735764469 560202428731074725227919)
  ·
    refine ⟨840303643096612087841879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 560202428731074725227919 840303643096612087841879)
    ·
      refine ⟨1260455464644918131762819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 840303643096612087841879 1260455464644918131762819)
      ·
        refine ⟨1890683196967377197644229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1260455464644918131762819 1890683196967377197644229)
        ·
          refine ⟨354503099431383224558293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1890683196967377197644229 354503099431383224558293)
          ·
            refine ⟨8308666392923044325585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 354503099431383224558293 8308666392923044325585)
            ·
              rfl

theorem cell19_245750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 7].length) (baseStart_245750 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_245750 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_245750 prefixEnd_245750 := by exact prefixLift 245750
  have htrace : WordTrace (prefixWord ++ tailWord_245750) baseStart_245750 baseEnd_245750 := by
    simpa [prefixWord, tailWord_245750, baseEnd_245750] using wordTrace_append hprefix tailTrace_245750
  have hstable : (prefixWord ++ tailWord_245750).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245750).length < 2 ^ (prefixWord ++ tailWord_245750).sum := by decide
  have hdescent : baseEnd_245750 < baseStart_245750 := by decide
  rcases family_descends (prefixWord ++ tailWord_245750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245809 : List Nat := [1, 2, 2, 3, 1, 4, 6]
def baseStart_245809 : Nat := 118140960795 + 245809 * 2 ^ 59
def prefixEnd_245809 : Nat := 4983230072969 + 3 ^ 40 * 245809 * 2
def baseEnd_245809 : Nat := 24931983447137581206331

theorem tailTrace_245809 : CollatzResearch.WordTrace tailWord_245809 prefixEnd_245809 24931983447137581206331 := by
  unfold tailWord_245809
  simp only [CollatzResearch.WordTrace]
  refine ⟨8965390766483448680044481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5976927177655632453362987 8965390766483448680044481)
  ·
    refine ⟨6724043074862586510033361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8965390766483448680044481 6724043074862586510033361)
    ·
      refine ⟨5043032306146939882525021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6724043074862586510033361 5043032306146939882525021)
      ·
        refine ⟨1891137114805102455946883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5043032306146939882525021 1891137114805102455946883)
        ·
          refine ⟨2836705672207653683920325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1891137114805102455946883 2836705672207653683920325)
          ·
            refine ⟨531882313538935065735061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2836705672207653683920325 531882313538935065735061)
            ·
              refine ⟨24931983447137581206331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 531882313538935065735061 24931983447137581206331)
              ·
                rfl

theorem cell19_245809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 6].length) (baseStart_245809 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_245809 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_245809 prefixEnd_245809 := by exact prefixLift 245809
  have htrace : WordTrace (prefixWord ++ tailWord_245809) baseStart_245809 baseEnd_245809 := by
    simpa [prefixWord, tailWord_245809, baseEnd_245809] using wordTrace_append hprefix tailTrace_245809
  have hstable : (prefixWord ++ tailWord_245809).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245809).length < 2 ^ (prefixWord ++ tailWord_245809).sum := by decide
  have hdescent : baseEnd_245809 < baseStart_245809 := by decide
  rcases family_descends (prefixWord ++ tailWord_245809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245845 : List Nat := [1, 3, 2, 2, 1, 3, 4, 3]
def baseStart_245845 : Nat := 118140960795 + 245845 * 2 ^ 59
def prefixEnd_245845 : Nat := 4983230072969 + 3 ^ 40 * 245845 * 2
def baseEnd_245845 : Nat := 74806904595375326818895

theorem tailTrace_245845 : CollatzResearch.WordTrace tailWord_245845 prefixEnd_245845 74806904595375326818895 := by
  unfold tailWord_245845
  simp only [CollatzResearch.WordTrace]
  refine ⟨8966703794353026828354989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5977802529568684552236659 8966703794353026828354989)
  ·
    refine ⟨3362513922882385060633121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8966703794353026828354989 3362513922882385060633121)
    ·
      refine ⟨2521885442161788795474841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3362513922882385060633121 2521885442161788795474841)
      ·
        refine ⟨1891414081621341596606131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2521885442161788795474841 1891414081621341596606131)
        ·
          refine ⟨2837121122432012394909197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1891414081621341596606131 2837121122432012394909197)
          ·
            refine ⟨1063920420912004648090949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2837121122432012394909197 1063920420912004648090949)
            ·
              refine ⟨199485078921000871517053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1063920420912004648090949 199485078921000871517053)
              ·
                refine ⟨74806904595375326818895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199485078921000871517053 74806904595375326818895)
                ·
                  rfl

theorem cell19_245845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 3].length) (baseStart_245845 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_245845 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_245845 prefixEnd_245845 := by exact prefixLift 245845
  have htrace : WordTrace (prefixWord ++ tailWord_245845) baseStart_245845 baseEnd_245845 := by
    simpa [prefixWord, tailWord_245845, baseEnd_245845] using wordTrace_append hprefix tailTrace_245845
  have hstable : (prefixWord ++ tailWord_245845).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245845).length < 2 ^ (prefixWord ++ tailWord_245845).sum := by decide
  have hdescent : baseEnd_245845 < baseStart_245845 := by decide
  rcases family_descends (prefixWord ++ tailWord_245845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245885 : List Nat := [1, 4, 1, 1, 3, 2, 1, 6]
def baseStart_245885 : Nat := 118140960795 + 245885 * 2 ^ 59
def prefixEnd_245885 : Nat := 4983230072969 + 3 ^ 40 * 245885 * 2
def baseEnd_245885 : Nat := 74819075988667085929897

theorem tailTrace_245885 : CollatzResearch.WordTrace tailWord_245885 prefixEnd_245885 74819075988667085929897 := by
  unfold tailWord_245885
  simp only [CollatzResearch.WordTrace]
  refine ⟨8968162714208113659811109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5978775142805409106540739 8968162714208113659811109)
  ·
    refine ⟨1681530508914021311214583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8968162714208113659811109 1681530508914021311214583)
    ·
      refine ⟨2522295763371031966821875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1681530508914021311214583 2522295763371031966821875)
      ·
        refine ⟨3783443645056547950232813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2522295763371031966821875 3783443645056547950232813)
        ·
          refine ⟨1418791366896205481337305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3783443645056547950232813 1418791366896205481337305)
          ·
            refine ⟨1064093525172154111002979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1418791366896205481337305 1064093525172154111002979)
            ·
              refine ⟨1596140287758231166504469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1064093525172154111002979 1596140287758231166504469)
              ·
                refine ⟨74819075988667085929897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1596140287758231166504469 74819075988667085929897)
                ·
                  rfl

theorem cell19_245885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_245885 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_245885 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_245885 prefixEnd_245885 := by exact prefixLift 245885
  have htrace : WordTrace (prefixWord ++ tailWord_245885) baseStart_245885 baseEnd_245885 := by
    simpa [prefixWord, tailWord_245885, baseEnd_245885] using wordTrace_append hprefix tailTrace_245885
  have hstable : (prefixWord ++ tailWord_245885).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245885).length < 2 ^ (prefixWord ++ tailWord_245885).sum := by decide
  have hdescent : baseEnd_245885 < baseStart_245885 := by decide
  rcases family_descends (prefixWord ++ tailWord_245885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245934 : List Nat := [4, 1, 4, 2, 2, 1, 1, 4]
def baseStart_245934 : Nat := 118140960795 + 245934 * 2 ^ 59
def prefixEnd_245934 : Nat := 4983230072969 + 3 ^ 40 * 245934 * 2
def baseEnd_245934 : Nat := 74833985945449490840875

theorem tailTrace_245934 : CollatzResearch.WordTrace tailWord_245934 prefixEnd_245934 74833985945449490840875 := by
  unfold tailWord_245934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1121243736378824378543107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5979966594020396685563237 1121243736378824378543107)
  ·
    refine ⟨1681865604568236567814661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1121243736378824378543107 1681865604568236567814661)
    ·
      refine ⟨315349800856544356465249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1681865604568236567814661 315349800856544356465249)
      ·
        refine ⟨236512350642408267348937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315349800856544356465249 236512350642408267348937)
        ·
          refine ⟨177384262981806200511703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236512350642408267348937 177384262981806200511703)
          ·
            refine ⟨266076394472709300767555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177384262981806200511703 266076394472709300767555)
            ·
              refine ⟨399114591709063951151333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266076394472709300767555 399114591709063951151333)
              ·
                refine ⟨74833985945449490840875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 399114591709063951151333 74833985945449490840875)
                ·
                  rfl

theorem cell19_245934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_245934 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_245934 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_245934 prefixEnd_245934 := by exact prefixLift 245934
  have htrace : WordTrace (prefixWord ++ tailWord_245934) baseStart_245934 baseEnd_245934 := by
    simpa [prefixWord, tailWord_245934, baseEnd_245934] using wordTrace_append hprefix tailTrace_245934
  have hstable : (prefixWord ++ tailWord_245934).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245934).length < 2 ^ (prefixWord ++ tailWord_245934).sum := by decide
  have hdescent : baseEnd_245934 < baseStart_245934 := by decide
  rcases family_descends (prefixWord ++ tailWord_245934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246096 : List Nat := [2, 1, 1, 1, 1, 13]
def baseStart_246096 : Nat := 118140960795 + 246096 * 2 ^ 59
def prefixEnd_246096 : Nat := 4983230072969 + 3 ^ 40 * 246096 * 2
def baseEnd_246096 : Nat := 8320364454253457248937

theorem tailTrace_246096 : CollatzResearch.WordTrace tailWord_246096 prefixEnd_246096 8320364454253457248937 := by
  unfold tailWord_246096
  simp only [CollatzResearch.WordTrace]
  refine ⟨4487929258221848347871071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5983905677629131130494761 4487929258221848347871071)
  ·
    refine ⟨6731893887332772521806607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4487929258221848347871071 6731893887332772521806607)
    ·
      refine ⟨10097840830999158782709911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6731893887332772521806607 10097840830999158782709911)
      ·
        refine ⟨15146761246498738174064867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10097840830999158782709911 15146761246498738174064867)
        ·
          refine ⟨22720141869748107261097301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15146761246498738174064867 22720141869748107261097301)
          ·
            refine ⟨8320364454253457248937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 22720141869748107261097301 8320364454253457248937)
            ·
              rfl

theorem cell19_246096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 13].length) (baseStart_246096 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_246096 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_246096 prefixEnd_246096 := by exact prefixLift 246096
  have htrace : WordTrace (prefixWord ++ tailWord_246096) baseStart_246096 baseEnd_246096 := by
    simpa [prefixWord, tailWord_246096, baseEnd_246096] using wordTrace_append hprefix tailTrace_246096
  have hstable : (prefixWord ++ tailWord_246096).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246096).length < 2 ^ (prefixWord ++ tailWord_246096).sum := by decide
  have hdescent : baseEnd_246096 < baseStart_246096 := by decide
  rcases family_descends (prefixWord ++ tailWord_246096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246130 : List Nat := [3, 2, 1, 2, 1, 4, 3, 3]
def baseStart_246130 : Nat := 118140960795 + 246130 * 2 ^ 59
def prefixEnd_246130 : Nat := 4983230072969 + 3 ^ 40 * 246130 * 2
def baseEnd_246130 : Nat := 74893625772579110484785

theorem tailTrace_246130 : CollatzResearch.WordTrace tailWord_246130 prefixEnd_246130 74893625772579110484785 := by
  unfold tailWord_246130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2244274649580130125619961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5984732398880347001653229 2244274649580130125619961)
  ·
    refine ⟨1683205987185097594214971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2244274649580130125619961 1683205987185097594214971)
    ·
      refine ⟨2524808980777646391322457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1683205987185097594214971 2524808980777646391322457)
      ·
        refine ⟨1893606735583234793491843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2524808980777646391322457 1893606735583234793491843)
        ·
          refine ⟨2840410103374852190237765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1893606735583234793491843 2840410103374852190237765)
          ·
            refine ⟨532576894382784785669581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2840410103374852190237765 532576894382784785669581)
            ·
              refine ⟨199716335393544294626093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 532576894382784785669581 199716335393544294626093)
              ·
                refine ⟨74893625772579110484785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199716335393544294626093 74893625772579110484785)
                ·
                  rfl

theorem cell19_246130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_246130 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_246130 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_246130 prefixEnd_246130 := by exact prefixLift 246130
  have htrace : WordTrace (prefixWord ++ tailWord_246130) baseStart_246130 baseEnd_246130 := by
    simpa [prefixWord, tailWord_246130, baseEnd_246130] using wordTrace_append hprefix tailTrace_246130
  have hstable : (prefixWord ++ tailWord_246130).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246130).length < 2 ^ (prefixWord ++ tailWord_246130).sum := by decide
  have hdescent : baseEnd_246130 < baseStart_246130 := by decide
  rcases family_descends (prefixWord ++ tailWord_246130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246278 : List Nat := [6, 2, 1, 1, 1, 1, 3, 4]
def baseStart_246278 : Nat := 118140960795 + 246278 * 2 ^ 59
def prefixEnd_246278 : Nat := 4983230072969 + 3 ^ 40 * 246278 * 2
def baseEnd_246278 : Nat := 74938659927758619195493

theorem tailTrace_246278 : CollatzResearch.WordTrace tailWord_246278 prefixEnd_246278 74938659927758619195493 := by
  unfold tailWord_246278
  simp only [CollatzResearch.WordTrace]
  refine ⟨280703018805760680589609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5988331067856227852578325 280703018805760680589609)
  ·
    refine ⟨210527264104320510442207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280703018805760680589609 210527264104320510442207)
    ·
      refine ⟨315790896156480765663311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210527264104320510442207 315790896156480765663311)
      ·
        refine ⟨473686344234721148494967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315790896156480765663311 473686344234721148494967)
        ·
          refine ⟨710529516352081722742451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473686344234721148494967 710529516352081722742451)
          ·
            refine ⟨1065794274528122584113677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710529516352081722742451 1065794274528122584113677)
            ·
              refine ⟨399672852948045969042629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1065794274528122584113677 399672852948045969042629)
              ·
                refine ⟨74938659927758619195493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 399672852948045969042629 74938659927758619195493)
                ·
                  rfl

theorem cell19_246278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_246278 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_246278 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_246278 prefixEnd_246278 := by exact prefixLift 246278
  have htrace : WordTrace (prefixWord ++ tailWord_246278) baseStart_246278 baseEnd_246278 := by
    simpa [prefixWord, tailWord_246278, baseEnd_246278] using wordTrace_append hprefix tailTrace_246278
  have hstable : (prefixWord ++ tailWord_246278).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246278).length < 2 ^ (prefixWord ++ tailWord_246278).sum := by decide
  have hdescent : baseEnd_246278 < baseStart_246278 := by decide
  rcases family_descends (prefixWord ++ tailWord_246278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246284 : List Nat := [2, 2, 1, 2, 4, 1, 3, 4]
def baseStart_246284 : Nat := 118140960795 + 246284 * 2 ^ 59
def prefixEnd_246284 : Nat := 4983230072969 + 3 ^ 40 * 246284 * 2
def baseEnd_246284 : Nat := 74940485636752383062143

theorem tailTrace_246284 : CollatzResearch.WordTrace tailWord_246284 prefixEnd_246284 74940485636752383062143 := by
  unfold tailWord_246284
  simp only [CollatzResearch.WordTrace]
  refine ⟨4491357719881302401792953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5988476959841736535723937 4491357719881302401792953)
  ·
    refine ⟨3368518289910976801344715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4491357719881302401792953 3368518289910976801344715)
    ·
      refine ⟨5052777434866465202017073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3368518289910976801344715 5052777434866465202017073)
      ·
        refine ⟨3789583076149848901512805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5052777434866465202017073 3789583076149848901512805)
        ·
          refine ⟨710546826778096669033651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3789583076149848901512805 710546826778096669033651)
          ·
            refine ⟨1065820240167145003550477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710546826778096669033651 1065820240167145003550477)
            ·
              refine ⟨399682590062679376331429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1065820240167145003550477 399682590062679376331429)
              ·
                refine ⟨74940485636752383062143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 399682590062679376331429 74940485636752383062143)
                ·
                  rfl

theorem cell19_246284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_246284 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_246284 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_246284 prefixEnd_246284 := by exact prefixLift 246284
  have htrace : WordTrace (prefixWord ++ tailWord_246284) baseStart_246284 baseEnd_246284 := by
    simpa [prefixWord, tailWord_246284, baseEnd_246284] using wordTrace_append hprefix tailTrace_246284
  have hstable : (prefixWord ++ tailWord_246284).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246284).length < 2 ^ (prefixWord ++ tailWord_246284).sum := by decide
  have hdescent : baseEnd_246284 < baseStart_246284 := by decide
  rcases family_descends (prefixWord ++ tailWord_246284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246301 : List Nat := [1, 4, 2, 2, 1, 3, 3, 3]
def baseStart_246301 : Nat := 118140960795 + 246301 * 2 ^ 59
def prefixEnd_246301 : Nat := 4983230072969 + 3 ^ 40 * 246301 * 2
def baseEnd_246301 : Nat := 74945658478901380684319

theorem tailTrace_246301 : CollatzResearch.WordTrace tailWord_246301 prefixEnd_246301 74945658478901380684319 := by
  unfold tailWord_246301
  simp only [CollatzResearch.WordTrace]
  refine ⟨8983335480701016706954757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5988890320467344471303171 8983335480701016706954757)
  ·
    refine ⟨1684375402631440632554017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8983335480701016706954757 1684375402631440632554017)
    ·
      refine ⟨1263281551973580474415513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1684375402631440632554017 1263281551973580474415513)
      ·
        refine ⟨947461163980185355811635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1263281551973580474415513 947461163980185355811635)
        ·
          refine ⟨1421191745970278033717453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947461163980185355811635 1421191745970278033717453)
          ·
            refine ⟨532946904738854262644045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1421191745970278033717453 532946904738854262644045)
            ·
              refine ⟨199855089277070348491517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 532946904738854262644045 199855089277070348491517)
              ·
                refine ⟨74945658478901380684319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199855089277070348491517 74945658478901380684319)
                ·
                  rfl

theorem cell19_246301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 3].length) (baseStart_246301 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_246301 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_246301 prefixEnd_246301 := by exact prefixLift 246301
  have htrace : WordTrace (prefixWord ++ tailWord_246301) baseStart_246301 baseEnd_246301 := by
    simpa [prefixWord, tailWord_246301, baseEnd_246301] using wordTrace_append hprefix tailTrace_246301
  have hstable : (prefixWord ++ tailWord_246301).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246301).length < 2 ^ (prefixWord ++ tailWord_246301).sum := by decide
  have hdescent : baseEnd_246301 < baseStart_246301 := by decide
  rcases family_descends (prefixWord ++ tailWord_246301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246360 : List Nat := [2, 1, 2, 2, 1, 2, 6, 3]
def baseStart_246360 : Nat := 118140960795 + 246360 * 2 ^ 59
def prefixEnd_246360 : Nat := 4983230072969 + 3 ^ 40 * 246360 * 2
def baseEnd_246360 : Nat := 74963611284006725373047

theorem tailTrace_246360 : CollatzResearch.WordTrace tailWord_246360 prefixEnd_246360 74963611284006725373047 := by
  unfold tailWord_246360
  simp only [CollatzResearch.WordTrace]
  refine ⟨4492743693743634891676267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5990324924991513188901689 4492743693743634891676267)
  ·
    refine ⟨6739115540615452337514401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4492743693743634891676267 6739115540615452337514401)
    ·
      refine ⟨5054336655461589253135801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6739115540615452337514401 5054336655461589253135801)
      ·
        refine ⟨3790752491596191939851851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5054336655461589253135801 3790752491596191939851851)
        ·
          refine ⟨5686128737394287909777777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3790752491596191939851851 5686128737394287909777777)
          ·
            refine ⟨4264596553045715932333333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5686128737394287909777777 4264596553045715932333333)
            ·
              refine ⟨199902963424017934328125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4264596553045715932333333 199902963424017934328125)
              ·
                refine ⟨74963611284006725373047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199902963424017934328125 74963611284006725373047)
                ·
                  rfl

theorem cell19_246360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 3].length) (baseStart_246360 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_246360 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_246360 prefixEnd_246360 := by exact prefixLift 246360
  have htrace : WordTrace (prefixWord ++ tailWord_246360) baseStart_246360 baseEnd_246360 := by
    simpa [prefixWord, tailWord_246360, baseEnd_246360] using wordTrace_append hprefix tailTrace_246360
  have hstable : (prefixWord ++ tailWord_246360).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246360).length < 2 ^ (prefixWord ++ tailWord_246360).sum := by decide
  have hdescent : baseEnd_246360 < baseStart_246360 := by decide
  rcases family_descends (prefixWord ++ tailWord_246360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246400 : List Nat := [2, 1, 1, 2, 1, 5, 1, 6]
def baseStart_246400 : Nat := 118140960795 + 246400 * 2 ^ 59
def prefixEnd_246400 : Nat := 4983230072969 + 3 ^ 40 * 246400 * 2
def baseEnd_246400 : Nat := 74975782677298484484049

theorem tailTrace_246400 : CollatzResearch.WordTrace tailWord_246400 prefixEnd_246400 74975782677298484484049 := by
  unfold tailWord_246400
  simp only [CollatzResearch.WordTrace]
  refine ⟨4493473153671178307404327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5991297538228237743205769 4493473153671178307404327)
  ·
    refine ⟨6740209730506767461106491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4493473153671178307404327 6740209730506767461106491)
    ·
      refine ⟨10110314595760151191659737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6740209730506767461106491 10110314595760151191659737)
      ·
        refine ⟨7582735946820113393744803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10110314595760151191659737 7582735946820113393744803)
        ·
          refine ⟨11374103920230170090617205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7582735946820113393744803 11374103920230170090617205)
          ·
            refine ⟨1066322242521578445995363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11374103920230170090617205 1066322242521578445995363)
            ·
              refine ⟨1599483363782367668993045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066322242521578445995363 1599483363782367668993045)
              ·
                refine ⟨74975782677298484484049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1599483363782367668993045 74975782677298484484049)
                ·
                  rfl

theorem cell19_246400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_246400 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_246400 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_246400 prefixEnd_246400 := by exact prefixLift 246400
  have htrace : WordTrace (prefixWord ++ tailWord_246400) baseStart_246400 baseEnd_246400 := by
    simpa [prefixWord, tailWord_246400, baseEnd_246400] using wordTrace_append hprefix tailTrace_246400
  have hstable : (prefixWord ++ tailWord_246400).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246400).length < 2 ^ (prefixWord ++ tailWord_246400).sum := by decide
  have hdescent : baseEnd_246400 < baseStart_246400 := by decide
  rcases family_descends (prefixWord ++ tailWord_246400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246453 : List Nat := [1, 3, 3, 3, 1, 3, 1, 4]
def baseStart_246453 : Nat := 118140960795 + 246453 * 2 ^ 59
def prefixEnd_246453 : Nat := 4983230072969 + 3 ^ 40 * 246453 * 2
def baseEnd_246453 : Nat := 74991909773410065306127

theorem tailTrace_246453 : CollatzResearch.WordTrace tailWord_246453 prefixEnd_246453 74991909773410065306127 := by
  unfold tailWord_246453
  simp only [CollatzResearch.WordTrace]
  refine ⟨8988879376150346666488013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5992586250766897777658675 8988879376150346666488013)
  ·
    refine ⟨3370829766056379999933005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8988879376150346666488013 3370829766056379999933005)
    ·
      refine ⟨1264061162271142499974877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3370829766056379999933005 1264061162271142499974877)
      ·
        refine ⟨474022935851678437490579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1264061162271142499974877 474022935851678437490579)
        ·
          refine ⟨711034403777517656235869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474022935851678437490579 711034403777517656235869)
          ·
            refine ⟨266637901416569121088451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 711034403777517656235869 266637901416569121088451)
            ·
              refine ⟨399956852124853681632677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266637901416569121088451 399956852124853681632677)
              ·
                refine ⟨74991909773410065306127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 399956852124853681632677 74991909773410065306127)
                ·
                  rfl

theorem cell19_246453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 4].length) (baseStart_246453 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_246453 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_246453 prefixEnd_246453 := by exact prefixLift 246453
  have htrace : WordTrace (prefixWord ++ tailWord_246453) baseStart_246453 baseEnd_246453 := by
    simpa [prefixWord, tailWord_246453, baseEnd_246453] using wordTrace_append hprefix tailTrace_246453
  have hstable : (prefixWord ++ tailWord_246453).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246453).length < 2 ^ (prefixWord ++ tailWord_246453).sum := by decide
  have hdescent : baseEnd_246453 < baseStart_246453 := by decide
  rcases family_descends (prefixWord ++ tailWord_246453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246495 : List Nat := [1, 1, 2, 3, 2, 4, 6]
def baseStart_246495 : Nat := 118140960795 + 246495 * 2 ^ 59
def prefixEnd_246495 : Nat := 4983230072969 + 3 ^ 40 * 246495 * 2
def baseEnd_246495 : Nat := 25001563245455470790893

theorem tailTrace_246495 : CollatzResearch.WordTrace tailWord_246495 prefixEnd_246495 25001563245455470790893 := by
  unfold tailWord_246495
  simp only [CollatzResearch.WordTrace]
  refine ⟨8990411241998187839516939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5993607494665458559677959 8990411241998187839516939)
  ·
    refine ⟨13485616862997281759275409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8990411241998187839516939 13485616862997281759275409)
    ·
      refine ⟨10114212647247961319456557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13485616862997281759275409 10114212647247961319456557)
      ·
        refine ⟨3792829742717985494796209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10114212647247961319456557 3792829742717985494796209)
        ·
          refine ⟨2844622307038489121097157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3792829742717985494796209 2844622307038489121097157)
          ·
            refine ⟨533366682569716710205717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2844622307038489121097157 533366682569716710205717)
            ·
              refine ⟨25001563245455470790893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 533366682569716710205717 25001563245455470790893)
              ·
                rfl

theorem cell19_246495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 6].length) (baseStart_246495 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_246495 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_246495 prefixEnd_246495 := by exact prefixLift 246495
  have htrace : WordTrace (prefixWord ++ tailWord_246495) baseStart_246495 baseEnd_246495 := by
    simpa [prefixWord, tailWord_246495, baseEnd_246495] using wordTrace_append hprefix tailTrace_246495
  have hstable : (prefixWord ++ tailWord_246495).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246495).length < 2 ^ (prefixWord ++ tailWord_246495).sum := by decide
  have hdescent : baseEnd_246495 < baseStart_246495 := by decide
  rcases family_descends (prefixWord ++ tailWord_246495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246546 : List Nat := [3, 2, 4, 1, 3, 1, 5]
def baseStart_246546 : Nat := 118140960795 + 246546 * 2 ^ 59
def prefixEnd_246546 : Nat := 4983230072969 + 3 ^ 40 * 246546 * 2
def baseEnd_246546 : Nat := 25006736087604468413069

theorem tailTrace_246546 : CollatzResearch.WordTrace tailWord_246546 prefixEnd_246546 25006736087604468413069 := by
  unfold tailWord_246546
  simp only [CollatzResearch.WordTrace]
  refine ⟨2248067841203355887405873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5994847576542282366415661 2248067841203355887405873)
  ·
    refine ⟨1686050880902516915554405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2248067841203355887405873 1686050880902516915554405)
    ·
      refine ⟨316134540169221921666451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1686050880902516915554405 316134540169221921666451)
      ·
        refine ⟨474201810253832882499677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316134540169221921666451 474201810253832882499677)
        ·
          refine ⟨177825678845187330937379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474201810253832882499677 177825678845187330937379)
          ·
            refine ⟨266738518267780996406069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177825678845187330937379 266738518267780996406069)
            ·
              refine ⟨25006736087604468413069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 266738518267780996406069 25006736087604468413069)
              ·
                rfl

theorem cell19_246546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 5].length) (baseStart_246546 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_246546 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_246546 prefixEnd_246546 := by exact prefixLift 246546
  have htrace : WordTrace (prefixWord ++ tailWord_246546) baseStart_246546 baseEnd_246546 := by
    simpa [prefixWord, tailWord_246546, baseEnd_246546] using wordTrace_append hprefix tailTrace_246546
  have hstable : (prefixWord ++ tailWord_246546).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246546).length < 2 ^ (prefixWord ++ tailWord_246546).sum := by decide
  have hdescent : baseEnd_246546 < baseStart_246546 := by decide
  rcases family_descends (prefixWord ++ tailWord_246546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246605 : List Nat := [1, 6, 1, 2, 3, 6]
def baseStart_246605 : Nat := 118140960795 + 246605 * 2 ^ 59
def prefixEnd_246605 : Nat := 4983230072969 + 3 ^ 40 * 246605 * 2
def baseEnd_246605 : Nat := 8337573451990972214215

theorem tailTrace_246605 : CollatzResearch.WordTrace tailWord_246605 prefixEnd_246605 8337573451990972214215 := by
  unfold tailWord_246605
  simp only [CollatzResearch.WordTrace]
  refine ⟨8994423271599676626021269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5996282181066451084014179 8994423271599676626021269)
  ·
    refine ⟨421613590856234841844747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8994423271599676626021269 421613590856234841844747)
    ·
      refine ⟨632420386284352262767121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421613590856234841844747 632420386284352262767121)
      ·
        refine ⟨474315289713264197075341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 632420386284352262767121 474315289713264197075341)
        ·
          refine ⟨177868233642474073903253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474315289713264197075341 177868233642474073903253)
          ·
            refine ⟨8337573451990972214215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 177868233642474073903253 8337573451990972214215)
            ·
              rfl

theorem cell19_246605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 6].length) (baseStart_246605 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_246605 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_246605 prefixEnd_246605 := by exact prefixLift 246605
  have htrace : WordTrace (prefixWord ++ tailWord_246605) baseStart_246605 baseEnd_246605 := by
    simpa [prefixWord, tailWord_246605, baseEnd_246605] using wordTrace_append hprefix tailTrace_246605
  have hstable : (prefixWord ++ tailWord_246605).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246605).length < 2 ^ (prefixWord ++ tailWord_246605).sum := by decide
  have hdescent : baseEnd_246605 < baseStart_246605 := by decide
  rcases family_descends (prefixWord ++ tailWord_246605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246609 : List Nat := [1, 2, 2, 1, 6, 7]
def baseStart_246609 : Nat := 118140960795 + 246609 * 2 ^ 59
def prefixEnd_246609 : Nat := 4983230072969 + 3 ^ 40 * 246609 * 2
def baseEnd_246609 : Nat := 8337708689694213982115

theorem tailTrace_246609 : CollatzResearch.WordTrace tailWord_246609 prefixEnd_246609 8337708689694213982115 := by
  unfold tailWord_246609
  simp only [CollatzResearch.WordTrace]
  refine ⟨8994569163585185309166881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5996379442390123539444587 8994569163585185309166881)
  ·
    refine ⟨6745926872688888981875161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8994569163585185309166881 6745926872688888981875161)
    ·
      refine ⟨5059445154516666736406371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6745926872688888981875161 5059445154516666736406371)
      ·
        refine ⟨7589167731775000104609557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5059445154516666736406371 7589167731775000104609557)
        ·
          refine ⟨355742237426953129903573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7589167731775000104609557 355742237426953129903573)
          ·
            refine ⟨8337708689694213982115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 355742237426953129903573 8337708689694213982115)
            ·
              rfl

theorem cell19_246609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 7].length) (baseStart_246609 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_246609 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_246609 prefixEnd_246609 := by exact prefixLift 246609
  have htrace : WordTrace (prefixWord ++ tailWord_246609) baseStart_246609 baseEnd_246609 := by
    simpa [prefixWord, tailWord_246609, baseEnd_246609] using wordTrace_append hprefix tailTrace_246609
  have hstable : (prefixWord ++ tailWord_246609).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246609).length < 2 ^ (prefixWord ++ tailWord_246609).sum := by decide
  have hdescent : baseEnd_246609 < baseStart_246609 := by decide
  rcases family_descends (prefixWord ++ tailWord_246609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246685 : List Nat := [1, 4, 2, 1, 2, 1, 2, 6]
def baseStart_246685 : Nat := 118140960795 + 246685 * 2 ^ 59
def prefixEnd_246685 : Nat := 4983230072969 + 3 ^ 40 * 246685 * 2
def baseEnd_246685 : Nat := 75062503854502268149939

theorem tailTrace_246685 : CollatzResearch.WordTrace tailWord_246685 prefixEnd_246685 75062503854502268149939 := by
  unfold tailWord_246685
  simp only [CollatzResearch.WordTrace]
  refine ⟨8997341111309850288933509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5998227407539900192622339 8997341111309850288933509)
  ·
    refine ⟨1687001458370596929175033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8997341111309850288933509 1687001458370596929175033)
    ·
      refine ⟨1265251093777947696881275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1687001458370596929175033 1265251093777947696881275)
      ·
        refine ⟨1897876640666921545321913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1265251093777947696881275 1897876640666921545321913)
        ·
          refine ⟨1423407480500191158991435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1897876640666921545321913 1423407480500191158991435)
          ·
            refine ⟨2135111220750286738487153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423407480500191158991435 2135111220750286738487153)
            ·
              refine ⟨1601333415562715053865365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2135111220750286738487153 1601333415562715053865365)
              ·
                refine ⟨75062503854502268149939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1601333415562715053865365 75062503854502268149939)
                ·
                  rfl

theorem cell19_246685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_246685 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_246685 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_246685 prefixEnd_246685 := by exact prefixLift 246685
  have htrace : WordTrace (prefixWord ++ tailWord_246685) baseStart_246685 baseEnd_246685 := by
    simpa [prefixWord, tailWord_246685, baseEnd_246685] using wordTrace_append hprefix tailTrace_246685
  have hstable : (prefixWord ++ tailWord_246685).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246685).length < 2 ^ (prefixWord ++ tailWord_246685).sum := by decide
  have hdescent : baseEnd_246685 < baseStart_246685 := by decide
  rcases family_descends (prefixWord ++ tailWord_246685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246740 : List Nat := [2, 4, 1, 2, 1, 3, 2, 4]
def baseStart_246740 : Nat := 118140960795 + 246740 * 2 ^ 59
def prefixEnd_246740 : Nat := 4983230072969 + 3 ^ 40 * 246740 * 2
def baseEnd_246740 : Nat := 75079239520278436927567

theorem tailTrace_246740 : CollatzResearch.WordTrace tailWord_246740 prefixEnd_246740 75079239520278436927567 := by
  unfold tailWord_246740
  simp only [CollatzResearch.WordTrace]
  refine ⟨4499673563055297341092837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5999564750740396454790449 4499673563055297341092837)
  ·
    refine ⟨843688793072868251454907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4499673563055297341092837 843688793072868251454907)
    ·
      refine ⟨1265533189609302377182361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 843688793072868251454907 1265533189609302377182361)
      ·
        refine ⟨949149892206976782886771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1265533189609302377182361 949149892206976782886771)
        ·
          refine ⟨1423724838310465174330157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949149892206976782886771 1423724838310465174330157)
          ·
            refine ⟨533896814366424440373809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1423724838310465174330157 533896814366424440373809)
            ·
              refine ⟨400422610774818330280357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533896814366424440373809 400422610774818330280357)
              ·
                refine ⟨75079239520278436927567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 400422610774818330280357 75079239520278436927567)
                ·
                  rfl

theorem cell19_246740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_246740 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_246740 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_246740 prefixEnd_246740 := by exact prefixLift 246740
  have htrace : WordTrace (prefixWord ++ tailWord_246740) baseStart_246740 baseEnd_246740 := by
    simpa [prefixWord, tailWord_246740, baseEnd_246740] using wordTrace_append hprefix tailTrace_246740
  have hstable : (prefixWord ++ tailWord_246740).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246740).length < 2 ^ (prefixWord ++ tailWord_246740).sum := by decide
  have hdescent : baseEnd_246740 < baseStart_246740 := by decide
  rcases family_descends (prefixWord ++ tailWord_246740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246772 : List Nat := [2, 6, 2, 1, 2, 6]
def baseStart_246772 : Nat := 118140960795 + 246772 * 2 ^ 59
def prefixEnd_246772 : Nat := 4983230072969 + 3 ^ 40 * 246772 * 2
def baseEnd_246772 : Nat := 8343219626101316024041

theorem tailTrace_246772 : CollatzResearch.WordTrace tailWord_246772 prefixEnd_246772 8343219626101316024041 := by
  unfold tailWord_246772
  simp only [CollatzResearch.WordTrace]
  refine ⟨4500257130997332073675285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6000342841329776098233713 4500257130997332073675285)
  ·
    refine ⟨210949553015499940953529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4500257130997332073675285 210949553015499940953529)
    ·
      refine ⟨158212164761624955715147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210949553015499940953529 158212164761624955715147)
      ·
        refine ⟨237318247142437433572721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158212164761624955715147 237318247142437433572721)
        ·
          refine ⟨177988685356828075179541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237318247142437433572721 177988685356828075179541)
          ·
            refine ⟨8343219626101316024041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 177988685356828075179541 8343219626101316024041)
            ·
              rfl

theorem cell19_246772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 6].length) (baseStart_246772 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_246772 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_246772 prefixEnd_246772 := by exact prefixLift 246772
  have htrace : WordTrace (prefixWord ++ tailWord_246772) baseStart_246772 baseEnd_246772 := by
    simpa [prefixWord, tailWord_246772, baseEnd_246772] using wordTrace_append hprefix tailTrace_246772
  have hstable : (prefixWord ++ tailWord_246772).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246772).length < 2 ^ (prefixWord ++ tailWord_246772).sum := by decide
  have hdescent : baseEnd_246772 < baseStart_246772 := by decide
  rcases family_descends (prefixWord ++ tailWord_246772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246894 : List Nat := [4, 1, 2, 2, 1, 2, 7]
def baseStart_246894 : Nat := 118140960795 + 246894 * 2 ^ 59
def prefixEnd_246894 : Nat := 4983230072969 + 3 ^ 40 * 246894 * 2
def baseEnd_246894 : Nat := 25042033128150569834975

theorem tailTrace_246894 : CollatzResearch.WordTrace tailWord_246894 prefixEnd_246894 25042033128150569834975 := by
  unfold tailWord_246894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1125620495944084872911467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6003309311701785988861157 1125620495944084872911467)
  ·
    refine ⟨1688430743916127309367201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1125620495944084872911467 1688430743916127309367201)
    ·
      refine ⟨1266323057937095482025401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1688430743916127309367201 1266323057937095482025401)
      ·
        refine ⟨949742293452821611519051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1266323057937095482025401 949742293452821611519051)
        ·
          refine ⟨1424613440179232417278577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949742293452821611519051 1424613440179232417278577)
          ·
            refine ⟨1068460080134424312958933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1424613440179232417278577 1068460080134424312958933)
            ·
              refine ⟨25042033128150569834975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1068460080134424312958933 25042033128150569834975)
              ·
                rfl

theorem cell19_246894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 7].length) (baseStart_246894 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_246894 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_246894 prefixEnd_246894 := by exact prefixLift 246894
  have htrace : WordTrace (prefixWord ++ tailWord_246894) baseStart_246894 baseEnd_246894 := by
    simpa [prefixWord, tailWord_246894, baseEnd_246894] using wordTrace_append hprefix tailTrace_246894
  have hstable : (prefixWord ++ tailWord_246894).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246894).length < 2 ^ (prefixWord ++ tailWord_246894).sum := by decide
  have hdescent : baseEnd_246894 < baseStart_246894 := by decide
  rcases family_descends (prefixWord ++ tailWord_246894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246913 : List Nat := [1, 2, 4, 2, 2, 1, 1, 6]
def baseStart_246913 : Nat := 118140960795 + 246913 * 2 ^ 59
def prefixEnd_246913 : Nat := 4983230072969 + 3 ^ 40 * 246913 * 2
def baseEnd_246913 : Nat := 75131880796265295082651

theorem tailTrace_246913 : CollatzResearch.WordTrace tailWord_246913 prefixEnd_246913 75131880796265295082651 := by
  unfold tailWord_246913
  simp only [CollatzResearch.WordTrace]
  refine ⟨9005656954483845228233393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6003771302989230152155595 9005656954483845228233393)
  ·
    refine ⟨6754242715862883921175045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9005656954483845228233393 6754242715862883921175045)
    ·
      refine ⟨1266420509224290735220321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6754242715862883921175045 1266420509224290735220321)
      ·
        refine ⟨949815381918218051415241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1266420509224290735220321 949815381918218051415241)
        ·
          refine ⟨712361536438663538561431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 949815381918218051415241 712361536438663538561431)
          ·
            refine ⟨1068542304657995307842147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712361536438663538561431 1068542304657995307842147)
            ·
              refine ⟨1602813456986992961763221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068542304657995307842147 1602813456986992961763221)
              ·
                refine ⟨75131880796265295082651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1602813456986992961763221 75131880796265295082651)
                ·
                  rfl

theorem cell19_246913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 6].length) (baseStart_246913 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_246913 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_246913 prefixEnd_246913 := by exact prefixLift 246913
  have htrace : WordTrace (prefixWord ++ tailWord_246913) baseStart_246913 baseEnd_246913 := by
    simpa [prefixWord, tailWord_246913, baseEnd_246913] using wordTrace_append hprefix tailTrace_246913
  have hstable : (prefixWord ++ tailWord_246913).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246913).length < 2 ^ (prefixWord ++ tailWord_246913).sum := by decide
  have hdescent : baseEnd_246913 < baseStart_246913 := by decide
  rcases family_descends (prefixWord ++ tailWord_246913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246951 : List Nat := [1, 1, 6, 2, 1, 8]
def baseStart_246951 : Nat := 118140960795 + 246951 * 2 ^ 59
def prefixEnd_246951 : Nat := 4983230072969 + 3 ^ 40 * 246951 * 2
def baseEnd_246951 : Nat := 8349271513321385137567

theorem tailTrace_246951 : CollatzResearch.WordTrace tailWord_246951 prefixEnd_246951 8349271513321385137567 := by
  unfold tailWord_246951
  simp only [CollatzResearch.WordTrace]
  refine ⟨9007042928346177718116707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6004695285564118478744471 9007042928346177718116707)
  ·
    refine ⟨13510564392519266577175061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9007042928346177718116707 13510564392519266577175061)
    ·
      refine ⟨633307705899340620805081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13510564392519266577175061 633307705899340620805081)
      ·
        refine ⟨474980779424505465603811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633307705899340620805081 474980779424505465603811)
        ·
          refine ⟨712471169136758198405717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474980779424505465603811 712471169136758198405717)
          ·
            refine ⟨8349271513321385137567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 712471169136758198405717 8349271513321385137567)
            ·
              rfl

theorem cell19_246951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 8].length) (baseStart_246951 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_246951 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_246951 prefixEnd_246951 := by exact prefixLift 246951
  have htrace : WordTrace (prefixWord ++ tailWord_246951) baseStart_246951 baseEnd_246951 := by
    simpa [prefixWord, tailWord_246951, baseEnd_246951] using wordTrace_append hprefix tailTrace_246951
  have hstable : (prefixWord ++ tailWord_246951).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246951).length < 2 ^ (prefixWord ++ tailWord_246951).sum := by decide
  have hdescent : baseEnd_246951 < baseStart_246951 := by decide
  rcases family_descends (prefixWord ++ tailWord_246951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247044 : List Nat := [2, 3, 2, 2, 2, 1, 4, 3]
def baseStart_247044 : Nat := 118140960795 + 247044 * 2 ^ 59
def prefixEnd_247044 : Nat := 4983230072969 + 3 ^ 40 * 247044 * 2
def baseEnd_247044 : Nat := 75171742109295806171183

theorem tailTrace_247044 : CollatzResearch.WordTrace tailWord_247044 prefixEnd_247044 75171742109295806171183 := by
  unfold tailWord_247044
  simp only [CollatzResearch.WordTrace]
  refine ⟨4505217458504627300626093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6006956611339503067501457 4505217458504627300626093)
  ·
    refine ⟨1689456546939235237734785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4505217458504627300626093 1689456546939235237734785)
    ·
      refine ⟨1267092410204426428301089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1689456546939235237734785 1267092410204426428301089)
      ·
        refine ⟨950319307653319821225817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1267092410204426428301089 950319307653319821225817)
        ·
          refine ⟨712739480739989865919363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 950319307653319821225817 712739480739989865919363)
          ·
            refine ⟨1069109221109984798879045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712739480739989865919363 1069109221109984798879045)
            ·
              refine ⟨200457978958122149789821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1069109221109984798879045 200457978958122149789821)
              ·
                refine ⟨75171742109295806171183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200457978958122149789821 75171742109295806171183)
                ·
                  rfl

theorem cell19_247044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 3].length) (baseStart_247044 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247044 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247044 prefixEnd_247044 := by exact prefixLift 247044
  have htrace : WordTrace (prefixWord ++ tailWord_247044) baseStart_247044 baseEnd_247044 := by
    simpa [prefixWord, tailWord_247044, baseEnd_247044] using wordTrace_append hprefix tailTrace_247044
  have hstable : (prefixWord ++ tailWord_247044).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247044).length < 2 ^ (prefixWord ++ tailWord_247044).sum := by decide
  have hdescent : baseEnd_247044 < baseStart_247044 := by decide
  rcases family_descends (prefixWord ++ tailWord_247044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247082 : List Nat := [3, 1, 4, 2, 1, 2, 2, 4]
def baseStart_247082 : Nat := 118140960795 + 247082 * 2 ^ 59
def prefixEnd_247082 : Nat := 4983230072969 + 3 ^ 40 * 247082 * 2
def baseEnd_247082 : Nat := 75183304932922977326635

theorem tailTrace_247082 : CollatzResearch.WordTrace tailWord_247082 prefixEnd_247082 75183304932922977326635 := by
  unfold tailWord_247082
  simp only [CollatzResearch.WordTrace]
  refine ⟨2252955222717896772783875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6007880593914391394090333 2252955222717896772783875)
  ·
    refine ⟨3379432834076845159175813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2252955222717896772783875 3379432834076845159175813)
    ·
      refine ⟨633643656389408467345465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3379432834076845159175813 633643656389408467345465)
      ·
        refine ⟨475232742292056350509099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633643656389408467345465 475232742292056350509099)
        ·
          refine ⟨712849113438084525763649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475232742292056350509099 712849113438084525763649)
          ·
            refine ⟨534636835078563394322737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 712849113438084525763649 534636835078563394322737)
            ·
              refine ⟨400977626308922545742053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 534636835078563394322737 400977626308922545742053)
              ·
                refine ⟨75183304932922977326635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 400977626308922545742053 75183304932922977326635)
                ·
                  rfl

theorem cell19_247082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_247082 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247082 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247082 prefixEnd_247082 := by exact prefixLift 247082
  have htrace : WordTrace (prefixWord ++ tailWord_247082) baseStart_247082 baseEnd_247082 := by
    simpa [prefixWord, tailWord_247082, baseEnd_247082] using wordTrace_append hprefix tailTrace_247082
  have hstable : (prefixWord ++ tailWord_247082).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247082).length < 2 ^ (prefixWord ++ tailWord_247082).sum := by decide
  have hdescent : baseEnd_247082 < baseStart_247082 := by decide
  rcases family_descends (prefixWord ++ tailWord_247082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247133 : List Nat := [1, 4, 5, 1, 2, 1, 1, 4]
def baseStart_247133 : Nat := 118140960795 + 247133 * 2 ^ 59
def prefixEnd_247133 : Nat := 4983230072969 + 3 ^ 40 * 247133 * 2
def baseEnd_247133 : Nat := 75198823459369970193163

theorem tailTrace_247133 : CollatzResearch.WordTrace tailWord_247133 prefixEnd_247133 75198823459369970193163 := by
  unfold tailWord_247133
  simp only [CollatzResearch.WordTrace]
  refine ⟨9013681013686822801242053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6009120675791215200828035 9013681013686822801242053)
  ·
    refine ⟨1690065190066279275232885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9013681013686822801242053 1690065190066279275232885)
    ·
      refine ⟨158443611568713682053083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1690065190066279275232885 158443611568713682053083)
      ·
        refine ⟨237665417353070523079625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158443611568713682053083 237665417353070523079625)
        ·
          refine ⟨178249063014802892309719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237665417353070523079625 178249063014802892309719)
          ·
            refine ⟨267373594522204338464579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178249063014802892309719 267373594522204338464579)
            ·
              refine ⟨401060391783306507696869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267373594522204338464579 401060391783306507696869)
              ·
                refine ⟨75198823459369970193163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 401060391783306507696869 75198823459369970193163)
                ·
                  rfl

theorem cell19_247133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 4].length) (baseStart_247133 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247133 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247133 prefixEnd_247133 := by exact prefixLift 247133
  have htrace : WordTrace (prefixWord ++ tailWord_247133) baseStart_247133 baseEnd_247133 := by
    simpa [prefixWord, tailWord_247133, baseEnd_247133] using wordTrace_append hprefix tailTrace_247133
  have hstable : (prefixWord ++ tailWord_247133).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247133).length < 2 ^ (prefixWord ++ tailWord_247133).sum := by decide
  have hdescent : baseEnd_247133 < baseStart_247133 := by decide
  rcases family_descends (prefixWord ++ tailWord_247133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247200 : List Nat := [2, 1, 1, 4, 1, 2, 2, 6]
def baseStart_247200 : Nat := 118140960795 + 247200 * 2 ^ 59
def prefixEnd_247200 : Nat := 4983230072969 + 3 ^ 40 * 247200 * 2
def baseEnd_247200 : Nat := 75219210543133666704091

theorem tailTrace_247200 : CollatzResearch.WordTrace tailWord_247200 prefixEnd_247200 75219210543133666704091 := by
  unfold tailWord_247200
  simp only [CollatzResearch.WordTrace]
  refine ⟨4508062352222046621965527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6010749802962728829287369 4508062352222046621965527)
  ·
    refine ⟨6762093528333069932948291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4508062352222046621965527 6762093528333069932948291)
    ·
      refine ⟨10143140292499604899422437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6762093528333069932948291 10143140292499604899422437)
      ·
        refine ⟨1901838804843675918641707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10143140292499604899422437 1901838804843675918641707)
        ·
          refine ⟨2852758207265513877962561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1901838804843675918641707 2852758207265513877962561)
          ·
            refine ⟨2139568655449135408471921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2852758207265513877962561 2139568655449135408471921)
            ·
              refine ⟨1604676491586851556353941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2139568655449135408471921 1604676491586851556353941)
              ·
                refine ⟨75219210543133666704091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1604676491586851556353941 75219210543133666704091)
                ·
                  rfl

theorem cell19_247200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_247200 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247200 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247200 prefixEnd_247200 := by exact prefixLift 247200
  have htrace : WordTrace (prefixWord ++ tailWord_247200) baseStart_247200 baseEnd_247200 := by
    simpa [prefixWord, tailWord_247200, baseEnd_247200] using wordTrace_append hprefix tailTrace_247200
  have hstable : (prefixWord ++ tailWord_247200).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247200).length < 2 ^ (prefixWord ++ tailWord_247200).sum := by decide
  have hdescent : baseEnd_247200 < baseStart_247200 := by decide
  rcases family_descends (prefixWord ++ tailWord_247200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247213 : List Nat := [1, 5, 2, 2, 1, 3, 2, 3]
def baseStart_247213 : Nat := 118140960795 + 247213 * 2 ^ 59
def prefixEnd_247213 : Nat := 4983230072969 + 3 ^ 40 * 247213 * 2
def baseEnd_247213 : Nat := 75223166245953488415167

theorem tailTrace_247213 : CollatzResearch.WordTrace tailWord_247213 prefixEnd_247213 75223166245953488415167 := by
  unfold tailWord_247213
  simp only [CollatzResearch.WordTrace]
  refine ⟨9016598853396996464154293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6011065902264664309436195 9016598853396996464154293)
  ·
    refine ⟨845306142505968418514465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9016598853396996464154293 845306142505968418514465)
    ·
      refine ⟨633979606879476313885849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 845306142505968418514465 633979606879476313885849)
      ·
        refine ⟨475484705159607235414387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633979606879476313885849 475484705159607235414387)
        ·
          refine ⟨713227057739410853121581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475484705159607235414387 713227057739410853121581)
          ·
            refine ⟨267460146652279069920593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 713227057739410853121581 267460146652279069920593)
            ·
              refine ⟨200595109989209302440445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267460146652279069920593 200595109989209302440445)
              ·
                refine ⟨75223166245953488415167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200595109989209302440445 75223166245953488415167)
                ·
                  rfl

theorem cell19_247213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 3].length) (baseStart_247213 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247213 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247213 prefixEnd_247213 := by exact prefixLift 247213
  have htrace : WordTrace (prefixWord ++ tailWord_247213) baseStart_247213 baseEnd_247213 := by
    simpa [prefixWord, tailWord_247213, baseEnd_247213] using wordTrace_append hprefix tailTrace_247213
  have hstable : (prefixWord ++ tailWord_247213).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247213).length < 2 ^ (prefixWord ++ tailWord_247213).sum := by decide
  have hdescent : baseEnd_247213 < baseStart_247213 := by decide
  rcases family_descends (prefixWord ++ tailWord_247213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247236 : List Nat := [2, 3, 3, 2, 1, 1, 7]
def baseStart_247236 : Nat := 118140960795 + 247236 * 2 ^ 59
def prefixEnd_247236 : Nat := 4983230072969 + 3 ^ 40 * 247236 * 2
def baseEnd_247236 : Nat := 25076721599032083301331

theorem tailTrace_247236 : CollatzResearch.WordTrace tailWord_247236 prefixEnd_247236 25076721599032083301331 := by
  unfold tailWord_247236
  simp only [CollatzResearch.WordTrace]
  refine ⟨4508718866156835696120781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6011625154875780928161041 4508718866156835696120781)
  ·
    refine ⟨1690769574808813386045293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4508718866156835696120781 1690769574808813386045293)
    ·
      refine ⟨634038590553305019766985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1690769574808813386045293 634038590553305019766985)
      ·
        refine ⟨475528942914978764825239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634038590553305019766985 475528942914978764825239)
        ·
          refine ⟨713293414372468147237859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475528942914978764825239 713293414372468147237859)
          ·
            refine ⟨1069940121558702220856789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713293414372468147237859 1069940121558702220856789)
            ·
              refine ⟨25076721599032083301331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1069940121558702220856789 25076721599032083301331)
              ·
                rfl

theorem cell19_247236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 7].length) (baseStart_247236 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247236 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247236 prefixEnd_247236 := by exact prefixLift 247236
  have htrace : WordTrace (prefixWord ++ tailWord_247236) baseStart_247236 baseEnd_247236 := by
    simpa [prefixWord, tailWord_247236, baseEnd_247236] using wordTrace_append hprefix tailTrace_247236
  have hstable : (prefixWord ++ tailWord_247236).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247236).length < 2 ^ (prefixWord ++ tailWord_247236).sum := by decide
  have hdescent : baseEnd_247236 < baseStart_247236 := by decide
  rcases family_descends (prefixWord ++ tailWord_247236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247257 : List Nat := [1, 2, 1, 2, 4, 2, 1, 6]
def baseStart_247257 : Nat := 118140960795 + 247257 * 2 ^ 59
def prefixEnd_247257 : Nat := 4983230072969 + 3 ^ 40 * 247257 * 2
def baseEnd_247257 : Nat := 75236554778574423437269

theorem tailTrace_247257 : CollatzResearch.WordTrace tailWord_247257 prefixEnd_247257 75236554778574423437269 := by
  unfold tailWord_247257
  simp only [CollatzResearch.WordTrace]
  refine ⟨9018203665237591978756025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6012135776825061319170683 9018203665237591978756025)
  ·
    refine ⟨6763652748928193984067019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9018203665237591978756025 6763652748928193984067019)
    ·
      refine ⟨10145479123392290976100529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6763652748928193984067019 10145479123392290976100529)
      ·
        refine ⟨7609109342544218232075397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10145479123392290976100529 7609109342544218232075397)
        ·
          refine ⟨1426708001727040918514137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7609109342544218232075397 1426708001727040918514137)
          ·
            refine ⟨1070031001295280688885603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1426708001727040918514137 1070031001295280688885603)
            ·
              refine ⟨1605046501942921033328405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070031001295280688885603 1605046501942921033328405)
              ·
                refine ⟨75236554778574423437269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1605046501942921033328405 75236554778574423437269)
                ·
                  rfl

theorem cell19_247257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_247257 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247257 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247257 prefixEnd_247257 := by exact prefixLift 247257
  have htrace : WordTrace (prefixWord ++ tailWord_247257) baseStart_247257 baseEnd_247257 := by
    simpa [prefixWord, tailWord_247257, baseEnd_247257] using wordTrace_append hprefix tailTrace_247257
  have hstable : (prefixWord ++ tailWord_247257).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247257).length < 2 ^ (prefixWord ++ tailWord_247257).sum := by decide
  have hdescent : baseEnd_247257 < baseStart_247257 := by decide
  rcases family_descends (prefixWord ++ tailWord_247257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247310 : List Nat := [4, 1, 1, 2, 4, 2, 1, 4]
def baseStart_247310 : Nat := 118140960795 + 247310 * 2 ^ 59
def prefixEnd_247310 : Nat := 4983230072969 + 3 ^ 40 * 247310 * 2
def baseEnd_247310 : Nat := 75252681874686004259347

theorem tailTrace_247310 : CollatzResearch.WordTrace tailWord_247310 prefixEnd_247310 75252681874686004259347 := by
  unfold tailWord_247310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1127517091755697753804423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6013424489363721353623589 1127517091755697753804423)
  ·
    refine ⟨1691275637633546630706635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1127517091755697753804423 1691275637633546630706635)
    ·
      refine ⟨2536913456450319946059953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1691275637633546630706635 2536913456450319946059953)
      ·
        refine ⟨1902685092337739959544965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2536913456450319946059953 1902685092337739959544965)
        ·
          refine ⟨356753454813326242414681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1902685092337739959544965 356753454813326242414681)
          ·
            refine ⟨267565091109994681811011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356753454813326242414681 267565091109994681811011)
            ·
              refine ⟨401347636664992022716517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267565091109994681811011 401347636664992022716517)
              ·
                refine ⟨75252681874686004259347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 401347636664992022716517 75252681874686004259347)
                ·
                  rfl

theorem cell19_247310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_247310 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247310 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247310 prefixEnd_247310 := by exact prefixLift 247310
  have htrace : WordTrace (prefixWord ++ tailWord_247310) baseStart_247310 baseEnd_247310 := by
    simpa [prefixWord, tailWord_247310, baseEnd_247310] using wordTrace_append hprefix tailTrace_247310
  have hstable : (prefixWord ++ tailWord_247310).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247310).length < 2 ^ (prefixWord ++ tailWord_247310).sum := by decide
  have hdescent : baseEnd_247310 < baseStart_247310 := by decide
  rcases family_descends (prefixWord ++ tailWord_247310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247352 : List Nat := [2, 1, 2, 1, 4, 3, 6]
def baseStart_247352 : Nat := 118140960795 + 247352 * 2 ^ 59
def prefixEnd_247352 : Nat := 4983230072969 + 3 ^ 40 * 247352 * 2
def baseEnd_247352 : Nat := 25088487279214117108633

theorem tailTrace_247352 : CollatzResearch.WordTrace tailWord_247352 prefixEnd_247352 25088487279214117108633 := by
  unfold tailWord_247352
  simp only [CollatzResearch.WordTrace]
  refine ⟨4510834299946711601732155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6014445733262282135642873 4510834299946711601732155)
  ·
    refine ⟨6766251449920067402598233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4510834299946711601732155 6766251449920067402598233)
    ·
      refine ⟨5074688587440050551948675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6766251449920067402598233 5074688587440050551948675)
      ·
        refine ⟨7612032881160075827923013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5074688587440050551948675 7612032881160075827923013)
        ·
          refine ⟨1427256165217514217735565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7612032881160075827923013 1427256165217514217735565)
          ·
            refine ⟨535221061956567831650837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1427256165217514217735565 535221061956567831650837)
            ·
              refine ⟨25088487279214117108633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 535221061956567831650837 25088487279214117108633)
              ·
                rfl

theorem cell19_247352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 6].length) (baseStart_247352 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247352 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247352 prefixEnd_247352 := by exact prefixLift 247352
  have htrace : WordTrace (prefixWord ++ tailWord_247352) baseStart_247352 baseEnd_247352 := by
    simpa [prefixWord, tailWord_247352, baseEnd_247352] using wordTrace_append hprefix tailTrace_247352
  have hstable : (prefixWord ++ tailWord_247352).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247352).length < 2 ^ (prefixWord ++ tailWord_247352).sum := by decide
  have hdescent : baseEnd_247352 < baseStart_247352 := by decide
  rcases family_descends (prefixWord ++ tailWord_247352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247388 : List Nat := [2, 2, 4, 1, 2, 2, 1, 5]
def baseStart_247388 : Nat := 118140960795 + 247388 * 2 ^ 59
def prefixEnd_247388 : Nat := 4983230072969 + 3 ^ 40 * 247388 * 2
def baseEnd_247388 : Nat := 75276416091604934525801

theorem tailTrace_247388 : CollatzResearch.WordTrace tailWord_247388 prefixEnd_247388 75276416091604934525801 := by
  unfold tailWord_247388
  simp only [CollatzResearch.WordTrace]
  refine ⟨4511490813881500675887409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6015321085175334234516545 4511490813881500675887409)
  ·
    refine ⟨3383618110411125506915557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4511490813881500675887409 3383618110411125506915557)
    ·
      refine ⟨634428395702086032546667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3383618110411125506915557 634428395702086032546667)
      ·
        refine ⟨951642593553129048820001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634428395702086032546667 951642593553129048820001)
        ·
          refine ⟨713731945164846786615001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 951642593553129048820001 713731945164846786615001)
          ·
            refine ⟨535298958873635089961251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 713731945164846786615001 535298958873635089961251)
            ·
              refine ⟨802948438310452634941877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535298958873635089961251 802948438310452634941877)
              ·
                refine ⟨75276416091604934525801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 802948438310452634941877 75276416091604934525801)
                ·
                  rfl

theorem cell19_247388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_247388 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247388 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247388 prefixEnd_247388 := by exact prefixLift 247388
  have htrace : WordTrace (prefixWord ++ tailWord_247388) baseStart_247388 baseEnd_247388 := by
    simpa [prefixWord, tailWord_247388, baseEnd_247388] using wordTrace_append hprefix tailTrace_247388
  have hstable : (prefixWord ++ tailWord_247388).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247388).length < 2 ^ (prefixWord ++ tailWord_247388).sum := by decide
  have hdescent : baseEnd_247388 < baseStart_247388 := by decide
  rcases family_descends (prefixWord ++ tailWord_247388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247405 : List Nat := [1, 5, 1, 1, 5, 1, 5]
def baseStart_247405 : Nat := 118140960795 + 247405 * 2 ^ 59
def prefixEnd_247405 : Nat := 4983230072969 + 3 ^ 40 * 247405 * 2
def baseEnd_247405 : Nat := 25093862977917977382659

theorem tailTrace_247405 : CollatzResearch.WordTrace tailWord_247405 prefixEnd_247405 25093862977917977382659 := by
  unfold tailWord_247405
  simp only [CollatzResearch.WordTrace]
  refine ⟨9023601668701413255143669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6015734445800942170095779 9023601668701413255143669)
  ·
    refine ⟨845962656440757492669719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9023601668701413255143669 845962656440757492669719)
    ·
      refine ⟨1268943984661136239004579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 845962656440757492669719 1268943984661136239004579)
      ·
        refine ⟨1903415976991704358506869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1268943984661136239004579 1903415976991704358506869)
        ·
          refine ⟨178445247842972283610019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1903415976991704358506869 178445247842972283610019)
          ·
            refine ⟨267667871764458425415029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178445247842972283610019 267667871764458425415029)
            ·
              refine ⟨25093862977917977382659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 267667871764458425415029 25093862977917977382659)
              ·
                rfl

theorem cell19_247405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 5].length) (baseStart_247405 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247405 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247405 prefixEnd_247405 := by exact prefixLift 247405
  have htrace : WordTrace (prefixWord ++ tailWord_247405) baseStart_247405 baseEnd_247405 := by
    simpa [prefixWord, tailWord_247405, baseEnd_247405] using wordTrace_append hprefix tailTrace_247405
  have hstable : (prefixWord ++ tailWord_247405).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247405).length < 2 ^ (prefixWord ++ tailWord_247405).sum := by decide
  have hdescent : baseEnd_247405 < baseStart_247405 := by decide
  rcases family_descends (prefixWord ++ tailWord_247405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247447 : List Nat := [1, 1, 3, 3, 2, 2, 2, 5]
def baseStart_247447 : Nat := 118140960795 + 247447 * 2 ^ 59
def prefixEnd_247447 : Nat := 4983230072969 + 3 ^ 40 * 247447 * 2
def baseEnd_247447 : Nat := 75294368896710279214529

theorem tailTrace_247447 : CollatzResearch.WordTrace tailWord_247447 prefixEnd_247447 75294368896710279214529 := by
  unfold tailWord_247447
  simp only [CollatzResearch.WordTrace]
  refine ⟨9025133534549254428172595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6016755689699502952115063 9025133534549254428172595)
  ·
    refine ⟨13537700301823881642258893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9025133534549254428172595 13537700301823881642258893)
    ·
      refine ⟨5076637613183955615847085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13537700301823881642258893 5076637613183955615847085)
      ·
        refine ⟨1903739104943983355942657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5076637613183955615847085 1903739104943983355942657)
        ·
          refine ⟨1427804328707987516956993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1903739104943983355942657 1427804328707987516956993)
          ·
            refine ⟨1070853246530990637717745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1427804328707987516956993 1070853246530990637717745)
            ·
              refine ⟨803139934898242978288309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1070853246530990637717745 803139934898242978288309)
              ·
                refine ⟨75294368896710279214529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 803139934898242978288309 75294368896710279214529)
                ·
                  rfl

theorem cell19_247447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_247447 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247447 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247447 prefixEnd_247447 := by exact prefixLift 247447
  have htrace : WordTrace (prefixWord ++ tailWord_247447) baseStart_247447 baseEnd_247447 := by
    simpa [prefixWord, tailWord_247447, baseEnd_247447] using wordTrace_append hprefix tailTrace_247447
  have hstable : (prefixWord ++ tailWord_247447).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247447).length < 2 ^ (prefixWord ++ tailWord_247447).sum := by decide
  have hdescent : baseEnd_247447 < baseStart_247447 := by decide
  rcases family_descends (prefixWord ++ tailWord_247447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247466 : List Nat := [3, 1, 5, 10]
def baseStart_247466 : Nat := 118140960795 + 247466 * 2 ^ 59
def prefixEnd_247466 : Nat := 4983230072969 + 3 ^ 40 * 247466 * 2
def baseEnd_247466 : Nat := 929631485290418083855

theorem tailTrace_247466 : CollatzResearch.WordTrace tailWord_247466 prefixEnd_247466 929631485290418083855 := by
  unfold tailWord_247466
  simp only [CollatzResearch.WordTrace]
  refine ⟨2256456630370105168278563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6017217680986947115409501 2256456630370105168278563)
  ·
    refine ⟨3384684945555157752417845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2256456630370105168278563 3384684945555157752417845)
    ·
      refine ⟨317314213645796039289173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3384684945555157752417845 317314213645796039289173)
      ·
        refine ⟨929631485290418083855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 317314213645796039289173 929631485290418083855)
        ·
          rfl

theorem cell19_247466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 10].length) (baseStart_247466 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247466 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247466 prefixEnd_247466 := by exact prefixLift 247466
  have htrace : WordTrace (prefixWord ++ tailWord_247466) baseStart_247466 baseEnd_247466 := by
    simpa [prefixWord, tailWord_247466, baseEnd_247466] using wordTrace_append hprefix tailTrace_247466
  have hstable : (prefixWord ++ tailWord_247466).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247466).length < 2 ^ (prefixWord ++ tailWord_247466).sum := by decide
  have hdescent : baseEnd_247466 < baseStart_247466 := by decide
  rcases family_descends (prefixWord ++ tailWord_247466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247500 : List Nat := [2, 2, 1, 5, 2, 1, 3, 3]
def baseStart_247500 : Nat := 118140960795 + 247500 * 2 ^ 59
def prefixEnd_247500 : Nat := 4983230072969 + 3 ^ 40 * 247500 * 2
def baseEnd_247500 : Nat := 75310495992821860036607

theorem tailTrace_247500 : CollatzResearch.WordTrace tailWord_247500 prefixEnd_247500 75310495992821860036607 := by
  unfold tailWord_247500
  simp only [CollatzResearch.WordTrace]
  refine ⟨4513533301678622239925977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6018044402238162986567969 4513533301678622239925977)
  ·
    refine ⟨3385149976258966679944483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4513533301678622239925977 3385149976258966679944483)
    ·
      refine ⟨5077724964388450019916725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3385149976258966679944483 5077724964388450019916725)
      ·
        refine ⟨476036715411417189367193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5077724964388450019916725 476036715411417189367193)
        ·
          refine ⟨357027536558562892025395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476036715411417189367193 357027536558562892025395)
          ·
            refine ⟨535541304837844338038093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357027536558562892025395 535541304837844338038093)
            ·
              refine ⟨200827989314191626764285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 535541304837844338038093 200827989314191626764285)
              ·
                refine ⟨75310495992821860036607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200827989314191626764285 75310495992821860036607)
                ·
                  rfl

theorem cell19_247500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 3].length) (baseStart_247500 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247500 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247500 prefixEnd_247500 := by exact prefixLift 247500
  have htrace : WordTrace (prefixWord ++ tailWord_247500) baseStart_247500 baseEnd_247500 := by
    simpa [prefixWord, tailWord_247500, baseEnd_247500] using wordTrace_append hprefix tailTrace_247500
  have hstable : (prefixWord ++ tailWord_247500).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247500).length < 2 ^ (prefixWord ++ tailWord_247500).sum := by decide
  have hdescent : baseEnd_247500 < baseStart_247500 := by decide
  rcases family_descends (prefixWord ++ tailWord_247500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247502 : List Nat := [4, 1, 1, 1, 3, 1, 5, 3]
def baseStart_247502 : Nat := 118140960795 + 247502 * 2 ^ 59
def prefixEnd_247502 : Nat := 4983230072969 + 3 ^ 40 * 247502 * 2
def baseEnd_247502 : Nat := 75311104562486447992157

theorem tailTrace_247502 : CollatzResearch.WordTrace tailWord_247502 prefixEnd_247502 75311104562486447992157 := by
  unfold tailWord_247502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1128392443668749852678095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6018093032899999214283173 1128392443668749852678095)
  ·
    refine ⟨1692588665503124779017143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1128392443668749852678095 1692588665503124779017143)
    ·
      refine ⟨2538882998254687168525715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1692588665503124779017143 2538882998254687168525715)
      ·
        refine ⟨3808324497382030752788573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2538882998254687168525715 3808324497382030752788573)
        ·
          refine ⟨1428121686518261532295715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3808324497382030752788573 1428121686518261532295715)
          ·
            refine ⟨2142182529777392298443573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1428121686518261532295715 2142182529777392298443573)
            ·
              refine ⟨200829612166630527979085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2142182529777392298443573 200829612166630527979085)
              ·
                refine ⟨75311104562486447992157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200829612166630527979085 75311104562486447992157)
                ·
                  rfl

theorem cell19_247502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_247502 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247502 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247502 prefixEnd_247502 := by exact prefixLift 247502
  have htrace : WordTrace (prefixWord ++ tailWord_247502) baseStart_247502 baseEnd_247502 := by
    simpa [prefixWord, tailWord_247502, baseEnd_247502] using wordTrace_append hprefix tailTrace_247502
  have hstable : (prefixWord ++ tailWord_247502).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247502).length < 2 ^ (prefixWord ++ tailWord_247502).sum := by decide
  have hdescent : baseEnd_247502 < baseStart_247502 := by decide
  rcases family_descends (prefixWord ++ tailWord_247502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247559 : List Nat := [1, 1, 4, 4, 2, 1, 1, 5]
def baseStart_247559 : Nat := 118140960795 + 247559 * 2 ^ 59
def prefixEnd_247559 : Nat := 4983230072969 + 3 ^ 40 * 247559 * 2
def baseEnd_247559 : Nat := 75328448797927204725335

theorem tailTrace_247559 : CollatzResearch.WordTrace tailWord_247559 prefixEnd_247559 75328448797927204725335 := by
  unfold tailWord_247559
  simp only [CollatzResearch.WordTrace]
  refine ⟨9029218510143497556249731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6019479006762331704166487 9029218510143497556249731)
  ·
    refine ⟨13543827765215246334374597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9029218510143497556249731 13543827765215246334374597)
    ·
      refine ⟨2539467705977858687695237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13543827765215246334374597 2539467705977858687695237)
      ·
        refine ⟨476150194870848503942857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2539467705977858687695237 476150194870848503942857)
        ·
          refine ⟨357112646153136377957143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476150194870848503942857 357112646153136377957143)
          ·
            refine ⟨535668969229704566935715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357112646153136377957143 535668969229704566935715)
            ·
              refine ⟨803503453844556850403573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535668969229704566935715 803503453844556850403573)
              ·
                refine ⟨75328448797927204725335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 803503453844556850403573 75328448797927204725335)
                ·
                  rfl

theorem cell19_247559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 5].length) (baseStart_247559 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247559 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247559 prefixEnd_247559 := by exact prefixLift 247559
  have htrace : WordTrace (prefixWord ++ tailWord_247559) baseStart_247559 baseEnd_247559 := by
    simpa [prefixWord, tailWord_247559, baseEnd_247559] using wordTrace_append hprefix tailTrace_247559
  have hstable : (prefixWord ++ tailWord_247559).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247559).length < 2 ^ (prefixWord ++ tailWord_247559).sum := by decide
  have hdescent : baseEnd_247559 < baseStart_247559 := by decide
  rcases family_descends (prefixWord ++ tailWord_247559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247572 : List Nat := [2, 4, 4, 1, 2, 1, 5]
def baseStart_247572 : Nat := 118140960795 + 247572 * 2 ^ 59
def prefixEnd_247572 : Nat := 4983230072969 + 3 ^ 40 * 247572 * 2
def baseEnd_247572 : Nat := 25110801500249008812137

theorem tailTrace_247572 : CollatzResearch.WordTrace tailWord_247572 prefixEnd_247572 25110801500249008812137 := by
  unfold tailWord_247572
  simp only [CollatzResearch.WordTrace]
  refine ⟨4514846329548200388236485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6019795106064267184315313 4514846329548200388236485)
  ·
    refine ⟨846533686790287572794341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4514846329548200388236485 846533686790287572794341)
    ·
      refine ⟨158725066273178919898939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 846533686790287572794341 158725066273178919898939)
      ·
        refine ⟨238087599409768379848409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158725066273178919898939 238087599409768379848409)
        ·
          refine ⟨178565699557326284886307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238087599409768379848409 178565699557326284886307)
          ·
            refine ⟨267848549335989427329461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178565699557326284886307 267848549335989427329461)
            ·
              refine ⟨25110801500249008812137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 267848549335989427329461 25110801500249008812137)
              ·
                rfl

theorem cell19_247572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 5].length) (baseStart_247572 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247572 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247572 prefixEnd_247572 := by exact prefixLift 247572
  have htrace : WordTrace (prefixWord ++ tailWord_247572) baseStart_247572 baseEnd_247572 := by
    simpa [prefixWord, tailWord_247572, baseEnd_247572] using wordTrace_append hprefix tailTrace_247572
  have hstable : (prefixWord ++ tailWord_247572).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247572).length < 2 ^ (prefixWord ++ tailWord_247572).sum := by decide
  have hdescent : baseEnd_247572 < baseStart_247572 := by decide
  rcases family_descends (prefixWord ++ tailWord_247572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247639 : List Nat := [1, 1, 3, 2, 12]
def baseStart_247639 : Nat := 118140960795 + 247639 * 2 ^ 59
def prefixEnd_247639 : Nat := 4983230072969 + 3 ^ 40 * 247639 * 2
def baseEnd_247639 : Nat := 2790844132759656405457

theorem tailTrace_247639 : CollatzResearch.WordTrace tailWord_247639 prefixEnd_247639 2790844132759656405457 := by
  unfold tailWord_247639
  simp only [CollatzResearch.WordTrace]
  refine ⟨9032136349853671219161971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6021424233235780812774647 9032136349853671219161971)
  ·
    refine ⟨13548204524780506828742957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9032136349853671219161971 13548204524780506828742957)
    ·
      refine ⟨5080576696792690060778609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13548204524780506828742957 5080576696792690060778609)
      ·
        refine ⟨3810432522594517545583957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5080576696792690060778609 3810432522594517545583957)
        ·
          refine ⟨2790844132759656405457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3810432522594517545583957 2790844132759656405457)
          ·
            rfl

theorem cell19_247639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 12].length) (baseStart_247639 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247639 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247639 prefixEnd_247639 := by exact prefixLift 247639
  have htrace : WordTrace (prefixWord ++ tailWord_247639) baseStart_247639 baseEnd_247639 := by
    simpa [prefixWord, tailWord_247639, baseEnd_247639] using wordTrace_append hprefix tailTrace_247639
  have hstable : (prefixWord ++ tailWord_247639).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247639).length < 2 ^ (prefixWord ++ tailWord_247639).sum := by decide
  have hdescent : baseEnd_247639 < baseStart_247639 := by decide
  rcases family_descends (prefixWord ++ tailWord_247639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247652 : List Nat := [2, 3, 1, 1, 6, 1, 1, 4]
def baseStart_247652 : Nat := 118140960795 + 247652 * 2 ^ 59
def prefixEnd_247652 : Nat := 4983230072969 + 3 ^ 40 * 247652 * 2
def baseEnd_247652 : Nat := 75356747287330544658415

theorem tailTrace_247652 : CollatzResearch.WordTrace tailWord_247652 prefixEnd_247652 75356747287330544658415 := by
  unfold tailWord_247652
  simp only [CollatzResearch.WordTrace]
  refine ⟨4516305249403287219692605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6021740332537716292923473 4516305249403287219692605)
  ·
    refine ⟨1693614468526232707384727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4516305249403287219692605 1693614468526232707384727)
    ·
      refine ⟨2540421702789349061077091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1693614468526232707384727 2540421702789349061077091)
      ·
        refine ⟨3810632554184023591615637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2540421702789349061077091 3810632554184023591615637)
        ·
          refine ⟨178623400977376105856983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3810632554184023591615637 178623400977376105856983)
          ·
            refine ⟨267935101466064158785475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178623400977376105856983 267935101466064158785475)
            ·
              refine ⟨401902652199096238178213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267935101466064158785475 401902652199096238178213)
              ·
                refine ⟨75356747287330544658415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 401902652199096238178213 75356747287330544658415)
                ·
                  rfl

theorem cell19_247652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 4].length) (baseStart_247652 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247652 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247652 prefixEnd_247652 := by exact prefixLift 247652
  have htrace : WordTrace (prefixWord ++ tailWord_247652) baseStart_247652 baseEnd_247652 := by
    simpa [prefixWord, tailWord_247652, baseEnd_247652] using wordTrace_append hprefix tailTrace_247652
  have hstable : (prefixWord ++ tailWord_247652).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247652).length < 2 ^ (prefixWord ++ tailWord_247652).sum := by decide
  have hdescent : baseEnd_247652 < baseStart_247652 := by decide
  rcases family_descends (prefixWord ++ tailWord_247652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247715 : List Nat := [1, 1, 1, 4, 1, 2, 1, 8]
def baseStart_247715 : Nat := 118140960795 + 247715 * 2 ^ 59
def prefixEnd_247715 : Nat := 4983230072969 + 3 ^ 40 * 247715 * 2
def baseEnd_247715 : Nat := 75375917231765065258243

theorem tailTrace_247715 : CollatzResearch.WordTrace tailWord_247715 prefixEnd_247715 75375917231765065258243 := by
  unfold tailWord_247715
  simp only [CollatzResearch.WordTrace]
  refine ⟨9034908297578336198928599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6023272198385557465952399 9034908297578336198928599)
  ·
    refine ⟨13552362446367504298392899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9034908297578336198928599 13552362446367504298392899)
    ·
      refine ⟨20328543669551256447589349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13552362446367504298392899 20328543669551256447589349)
      ·
        refine ⟨3811601938040860583923003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20328543669551256447589349 3811601938040860583923003)
        ·
          refine ⟨5717402907061290875884505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3811601938040860583923003 5717402907061290875884505)
          ·
            refine ⟨4288052180295968156913379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5717402907061290875884505 4288052180295968156913379)
            ·
              refine ⟨6432078270443952235370069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4288052180295968156913379 6432078270443952235370069)
              ·
                refine ⟨75375917231765065258243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6432078270443952235370069 75375917231765065258243)
                ·
                  rfl

theorem cell19_247715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_247715 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247715 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247715 prefixEnd_247715 := by exact prefixLift 247715
  have htrace : WordTrace (prefixWord ++ tailWord_247715) baseStart_247715 baseEnd_247715 := by
    simpa [prefixWord, tailWord_247715, baseEnd_247715] using wordTrace_append hprefix tailTrace_247715
  have hstable : (prefixWord ++ tailWord_247715).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247715).length < 2 ^ (prefixWord ++ tailWord_247715).sum := by decide
  have hdescent : baseEnd_247715 < baseStart_247715 := by decide
  rcases family_descends (prefixWord ++ tailWord_247715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247726 : List Nat := [4, 1, 5, 1, 1, 1, 1, 5]
def baseStart_247726 : Nat := 118140960795 + 247726 * 2 ^ 59
def prefixEnd_247726 : Nat := 4983230072969 + 3 ^ 40 * 247726 * 2
def baseEnd_247726 : Nat := 75379264364920299013769

theorem tailTrace_247726 : CollatzResearch.WordTrace tailWord_247726 prefixEnd_247726 75379264364920299013769 := by
  unfold tailWord_247726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1129413687567310634697379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6023539667025656718386021 1129413687567310634697379)
  ·
    refine ⟨1694120531350965952046069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1129413687567310634697379 1694120531350965952046069)
    ·
      refine ⟨158823799814153058004319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1694120531350965952046069 158823799814153058004319)
      ·
        refine ⟨238235699721229587006479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158823799814153058004319 238235699721229587006479)
        ·
          refine ⟨357353549581844380509719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238235699721229587006479 357353549581844380509719)
          ·
            refine ⟨536030324372766570764579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357353549581844380509719 536030324372766570764579)
            ·
              refine ⟨804045486559149856146869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536030324372766570764579 804045486559149856146869)
              ·
                refine ⟨75379264364920299013769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 804045486559149856146869 75379264364920299013769)
                ·
                  rfl

theorem cell19_247726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_247726 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247726 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247726 prefixEnd_247726 := by exact prefixLift 247726
  have htrace : WordTrace (prefixWord ++ tailWord_247726) baseStart_247726 baseEnd_247726 := by
    simpa [prefixWord, tailWord_247726, baseEnd_247726] using wordTrace_append hprefix tailTrace_247726
  have hstable : (prefixWord ++ tailWord_247726).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247726).length < 2 ^ (prefixWord ++ tailWord_247726).sum := by decide
  have hdescent : baseEnd_247726 < baseStart_247726 := by decide
  rcases family_descends (prefixWord ++ tailWord_247726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247766 : List Nat := [5, 2, 1, 1, 3, 1, 2, 4]
def baseStart_247766 : Nat := 118140960795 + 247766 * 2 ^ 59
def prefixEnd_247766 : Nat := 4983230072969 + 3 ^ 40 * 247766 * 2
def baseEnd_247766 : Nat := 75391435758212058124771

theorem tailTrace_247766 : CollatzResearch.WordTrace tailWord_247766 prefixEnd_247766 75391435758212058124771 := by
  unfold tailWord_247766
  simp only [CollatzResearch.WordTrace]
  refine ⟨564798026274598244314697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6024512280262381272690101 564798026274598244314697)
  ·
    refine ⟨423598519705948683236023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 564798026274598244314697 423598519705948683236023)
    ·
      refine ⟨635397779558923024854035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423598519705948683236023 635397779558923024854035)
      ·
        refine ⟨953096669338384537281053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635397779558923024854035 953096669338384537281053)
        ·
          refine ⟨357411251001894201480395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 953096669338384537281053 357411251001894201480395)
          ·
            refine ⟨536116876502841302220593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357411251001894201480395 536116876502841302220593)
            ·
              refine ⟨402087657377130976665445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536116876502841302220593 402087657377130976665445)
              ·
                refine ⟨75391435758212058124771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 402087657377130976665445 75391435758212058124771)
                ·
                  rfl

theorem cell19_247766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_247766 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247766 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247766 prefixEnd_247766 := by exact prefixLift 247766
  have htrace : WordTrace (prefixWord ++ tailWord_247766) baseStart_247766 baseEnd_247766 := by
    simpa [prefixWord, tailWord_247766, baseEnd_247766] using wordTrace_append hprefix tailTrace_247766
  have hstable : (prefixWord ++ tailWord_247766).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247766).length < 2 ^ (prefixWord ++ tailWord_247766).sum := by decide
  have hdescent : baseEnd_247766 < baseStart_247766 := by decide
  rcases family_descends (prefixWord ++ tailWord_247766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247791 : List Nat := [1, 1, 2, 1, 4, 2, 1, 7]
def baseStart_247791 : Nat := 118140960795 + 247791 * 2 ^ 59
def prefixEnd_247791 : Nat := 4983230072969 + 3 ^ 40 * 247791 * 2
def baseEnd_247791 : Nat := 75399042879019407569147

theorem tailTrace_247791 : CollatzResearch.WordTrace tailWord_247791 prefixEnd_247791 75399042879019407569147 := by
  unfold tailWord_247791
  simp only [CollatzResearch.WordTrace]
  refine ⟨9037680245303001178695227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6025120163535334119130151 9037680245303001178695227)
  ·
    refine ⟨13556520367954501768042841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9037680245303001178695227 13556520367954501768042841)
    ·
      refine ⟨10167390275965876326032131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13556520367954501768042841 10167390275965876326032131)
      ·
        refine ⟨15251085413948814489048197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10167390275965876326032131 15251085413948814489048197)
        ·
          refine ⟨2859578515115402716696537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15251085413948814489048197 2859578515115402716696537)
          ·
            refine ⟨2144683886336552037522403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2859578515115402716696537 2144683886336552037522403)
            ·
              refine ⟨3217025829504828056283605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2144683886336552037522403 3217025829504828056283605)
              ·
                refine ⟨75399042879019407569147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3217025829504828056283605 75399042879019407569147)
                ·
                  rfl

theorem cell19_247791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_247791 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247791 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247791 prefixEnd_247791 := by exact prefixLift 247791
  have htrace : WordTrace (prefixWord ++ tailWord_247791) baseStart_247791 baseEnd_247791 := by
    simpa [prefixWord, tailWord_247791, baseEnd_247791] using wordTrace_append hprefix tailTrace_247791
  have hstable : (prefixWord ++ tailWord_247791).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247791).length < 2 ^ (prefixWord ++ tailWord_247791).sum := by decide
  have hdescent : baseEnd_247791 < baseStart_247791 := by decide
  rcases family_descends (prefixWord ++ tailWord_247791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247865 : List Nat := [1, 2, 1, 5, 3, 1, 6]
def baseStart_247865 : Nat := 118140960795 + 247865 * 2 ^ 59
def prefixEnd_247865 : Nat := 4983230072969 + 3 ^ 40 * 247865 * 2
def baseEnd_247865 : Nat := 25140519985536387308167

theorem tailTrace_247865 : CollatzResearch.WordTrace tailWord_247865 prefixEnd_247865 25140519985536387308167 := by
  unfold tailWord_247865
  simp only [CollatzResearch.WordTrace]
  refine ⟨9040379247034911816889049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6026919498023274544592699 9040379247034911816889049)
  ·
    refine ⟨6780284435276183862666787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9040379247034911816889049 6780284435276183862666787)
    ·
      refine ⟨10170426652914275794000181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6780284435276183862666787 10170426652914275794000181)
      ·
        refine ⟨953477498710713355687517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10170426652914275794000181 953477498710713355687517)
        ·
          refine ⟨357554062016517508382819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 953477498710713355687517 357554062016517508382819)
          ·
            refine ⟨536331093024776262574229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357554062016517508382819 536331093024776262574229)
            ·
              refine ⟨25140519985536387308167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 536331093024776262574229 25140519985536387308167)
              ·
                rfl

theorem cell19_247865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 6].length) (baseStart_247865 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247865 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247865 prefixEnd_247865 := by exact prefixLift 247865
  have htrace : WordTrace (prefixWord ++ tailWord_247865) baseStart_247865 baseEnd_247865 := by
    simpa [prefixWord, tailWord_247865, baseEnd_247865] using wordTrace_append hprefix tailTrace_247865
  have hstable : (prefixWord ++ tailWord_247865).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247865).length < 2 ^ (prefixWord ++ tailWord_247865).sum := by decide
  have hdescent : baseEnd_247865 < baseStart_247865 := by decide
  rcases family_descends (prefixWord ++ tailWord_247865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247901 : List Nat := [1, 4, 4, 1, 1, 2, 1, 5]
def baseStart_247901 : Nat := 118140960795 + 247901 * 2 ^ 59
def prefixEnd_247901 : Nat := 4983230072969 + 3 ^ 40 * 247901 * 2
def baseEnd_247901 : Nat := 75432514210571745124403

theorem tailTrace_247901 : CollatzResearch.WordTrace tailWord_247901 prefixEnd_247901 75432514210571745124403 := by
  unfold tailWord_247901
  simp only [CollatzResearch.WordTrace]
  refine ⟨9041692274904489965199557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6027794849936326643466371 9041692274904489965199557)
  ·
    refine ⟨1695317301544591868474917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9041692274904489965199557 1695317301544591868474917)
    ·
      refine ⟨317871994039610975339047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1695317301544591868474917 317871994039610975339047)
      ·
        refine ⟨476807991059416463008571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317871994039610975339047 476807991059416463008571)
        ·
          refine ⟨715211986589124694512857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476807991059416463008571 715211986589124694512857)
          ·
            refine ⟨536408989941843520884643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 715211986589124694512857 536408989941843520884643)
            ·
              refine ⟨804613484912765281326965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536408989941843520884643 804613484912765281326965)
              ·
                refine ⟨75432514210571745124403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 804613484912765281326965 75432514210571745124403)
                ·
                  rfl

theorem cell19_247901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 5].length) (baseStart_247901 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247901 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247901 prefixEnd_247901 := by exact prefixLift 247901
  have htrace : WordTrace (prefixWord ++ tailWord_247901) baseStart_247901 baseEnd_247901 := by
    simpa [prefixWord, tailWord_247901, baseEnd_247901] using wordTrace_append hprefix tailTrace_247901
  have hstable : (prefixWord ++ tailWord_247901).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247901).length < 2 ^ (prefixWord ++ tailWord_247901).sum := by decide
  have hdescent : baseEnd_247901 < baseStart_247901 := by decide
  rcases family_descends (prefixWord ++ tailWord_247901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247922 : List Nat := [3, 2, 1, 2, 2, 4, 5]
def baseStart_247922 : Nat := 118140960795 + 247922 * 2 ^ 59
def prefixEnd_247922 : Nat := 4983230072969 + 3 ^ 40 * 247922 * 2
def baseEnd_247922 : Nat := 25146301397349972885893

theorem tailTrace_247922 : CollatzResearch.WordTrace tailWord_247922 prefixEnd_247922 25146301397349972885893 := by
  unfold tailWord_247922
  simp only [CollatzResearch.WordTrace]
  refine ⟨2260614551957102637928505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6028305471885607034476013 2260614551957102637928505)
  ·
    refine ⟨1695460913967826978446379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2260614551957102637928505 1695460913967826978446379)
    ·
      refine ⟨2543191370951740467669569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1695460913967826978446379 2543191370951740467669569)
      ·
        refine ⟨1907393528213805350752177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2543191370951740467669569 1907393528213805350752177)
        ·
          refine ⟨1430545146160354013064133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1907393528213805350752177 1430545146160354013064133)
          ·
            refine ⟨268227214905066377449525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1430545146160354013064133 268227214905066377449525)
            ·
              refine ⟨25146301397349972885893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 268227214905066377449525 25146301397349972885893)
              ·
                rfl

theorem cell19_247922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 5].length) (baseStart_247922 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247922 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247922 prefixEnd_247922 := by exact prefixLift 247922
  have htrace : WordTrace (prefixWord ++ tailWord_247922) baseStart_247922 baseEnd_247922 := by
    simpa [prefixWord, tailWord_247922, baseEnd_247922] using wordTrace_append hprefix tailTrace_247922
  have hstable : (prefixWord ++ tailWord_247922).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247922).length < 2 ^ (prefixWord ++ tailWord_247922).sum := by decide
  have hdescent : baseEnd_247922 < baseStart_247922 := by decide
  rcases family_descends (prefixWord ++ tailWord_247922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247941 : List Nat := [1, 3, 1, 1, 5, 2, 2, 4]
def baseStart_247941 : Nat := 118140960795 + 247941 * 2 ^ 59
def prefixEnd_247941 : Nat := 4983230072969 + 3 ^ 40 * 247941 * 2
def baseEnd_247941 : Nat := 75444685603863504235405

theorem tailTrace_247941 : CollatzResearch.WordTrace tailWord_247941 prefixEnd_247941 75444685603863504235405 := by
  unfold tailWord_247941
  simp only [CollatzResearch.WordTrace]
  refine ⟨9043151194759576796655677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6028767463173051197770451 9043151194759576796655677)
  ·
    refine ⟨3391181698034841298745879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9043151194759576796655677 3391181698034841298745879)
    ·
      refine ⟨5086772547052261948118819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3391181698034841298745879 5086772547052261948118819)
      ·
        refine ⟨7630158820578392922178229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5086772547052261948118819 7630158820578392922178229)
        ·
          refine ⟨715327389429224336454209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7630158820578392922178229 715327389429224336454209)
          ·
            refine ⟨536495542071918252340657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 715327389429224336454209 536495542071918252340657)
            ·
              refine ⟨402371656553938689255493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536495542071918252340657 402371656553938689255493)
              ·
                refine ⟨75444685603863504235405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 402371656553938689255493 75444685603863504235405)
                ·
                  rfl

theorem cell19_247941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 4].length) (baseStart_247941 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247941 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247941 prefixEnd_247941 := by exact prefixLift 247941
  have htrace : WordTrace (prefixWord ++ tailWord_247941) baseStart_247941 baseEnd_247941 := by
    simpa [prefixWord, tailWord_247941, baseEnd_247941] using wordTrace_append hprefix tailTrace_247941
  have hstable : (prefixWord ++ tailWord_247941).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247941).length < 2 ^ (prefixWord ++ tailWord_247941).sum := by decide
  have hdescent : baseEnd_247941 < baseStart_247941 := by decide
  rcases family_descends (prefixWord ++ tailWord_247941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247943 : List Nat := [1, 1, 4, 2, 1, 1, 3, 6]
def baseStart_247943 : Nat := 118140960795 + 247943 * 2 ^ 59
def prefixEnd_247943 : Nat := 4983230072969 + 3 ^ 40 * 247943 * 2
def baseEnd_247943 : Nat := 75445294173528092190955

theorem tailTrace_247943 : CollatzResearch.WordTrace tailWord_247943 prefixEnd_247943 75445294173528092190955 := by
  unfold tailWord_247943
  simp only [CollatzResearch.WordTrace]
  refine ⟨9043224140752331138228483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6028816093834887425485655 9043224140752331138228483)
  ·
    refine ⟨13564836211128496707342725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9043224140752331138228483 13564836211128496707342725)
    ·
      refine ⟨2543406789586593132626761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13564836211128496707342725 2543406789586593132626761)
      ·
        refine ⟨1907555092189944849470071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2543406789586593132626761 1907555092189944849470071)
        ·
          refine ⟨2861332638284917274205107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1907555092189944849470071 2861332638284917274205107)
          ·
            refine ⟨4291998957427375911307661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2861332638284917274205107 4291998957427375911307661)
            ·
              refine ⟨1609499609035265966740373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4291998957427375911307661 1609499609035265966740373)
              ·
                refine ⟨75445294173528092190955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1609499609035265966740373 75445294173528092190955)
                ·
                  rfl

theorem cell19_247943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_247943 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247943 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247943 prefixEnd_247943 := by exact prefixLift 247943
  have htrace : WordTrace (prefixWord ++ tailWord_247943) baseStart_247943 baseEnd_247943 := by
    simpa [prefixWord, tailWord_247943, baseEnd_247943] using wordTrace_append hprefix tailTrace_247943
  have hstable : (prefixWord ++ tailWord_247943).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247943).length < 2 ^ (prefixWord ++ tailWord_247943).sum := by decide
  have hdescent : baseEnd_247943 < baseStart_247943 := by decide
  rcases family_descends (prefixWord ++ tailWord_247943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247996 : List Nat := [2, 2, 2, 3, 3, 2, 1, 4]
def baseStart_247996 : Nat := 118140960795 + 247996 * 2 ^ 59
def prefixEnd_247996 : Nat := 4983230072969 + 3 ^ 40 * 247996 * 2
def baseEnd_247996 : Nat := 75461421269639673013033

theorem tailTrace_247996 : CollatzResearch.WordTrace tailWord_247996 prefixEnd_247996 75461421269639673013033 := by
  unfold tailWord_247996
  simp only [CollatzResearch.WordTrace]
  refine ⟨4522578604780160594953921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6030104806373547459938561 4522578604780160594953921)
  ·
    refine ⟨3391933953585120446215441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4522578604780160594953921 3391933953585120446215441)
    ·
      refine ⟨2543950465188840334661581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3391933953585120446215441 2543950465188840334661581)
      ·
        refine ⟨953981424445815125498093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2543950465188840334661581 953981424445815125498093)
        ·
          refine ⟨357743034167180672061785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 953981424445815125498093 357743034167180672061785)
          ·
            refine ⟨268307275625385504046339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357743034167180672061785 268307275625385504046339)
            ·
              refine ⟨402460913438078256069509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268307275625385504046339 402460913438078256069509)
              ·
                refine ⟨75461421269639673013033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 402460913438078256069509 75461421269639673013033)
                ·
                  rfl

theorem cell19_247996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_247996 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_247996 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_247996 prefixEnd_247996 := by exact prefixLift 247996
  have htrace : WordTrace (prefixWord ++ tailWord_247996) baseStart_247996 baseEnd_247996 := by
    simpa [prefixWord, tailWord_247996, baseEnd_247996] using wordTrace_append hprefix tailTrace_247996
  have hstable : (prefixWord ++ tailWord_247996).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247996).length < 2 ^ (prefixWord ++ tailWord_247996).sum := by decide
  have hdescent : baseEnd_247996 < baseStart_247996 := by decide
  rcases family_descends (prefixWord ++ tailWord_247996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248072 : List Nat := [2, 1, 3, 2, 3, 3, 2, 3]
def baseStart_248072 : Nat := 118140960795 + 248072 * 2 ^ 59
def prefixEnd_248072 : Nat := 4983230072969 + 3 ^ 40 * 248072 * 2
def baseEnd_248072 : Nat := 75484546916894015323937

theorem tailTrace_248072 : CollatzResearch.WordTrace tailWord_248072 prefixEnd_248072 75484546916894015323937 := by
  unfold tailWord_248072
  simp only [CollatzResearch.WordTrace]
  refine ⟨4523964578642493084837235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6031952771523324113116313 4523964578642493084837235)
  ·
    refine ⟨6785946867963739627255853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4523964578642493084837235 6785946867963739627255853)
    ·
      refine ⟨2544730075486402360220945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6785946867963739627255853 2544730075486402360220945)
      ·
        refine ⟨1908547556614801770165709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2544730075486402360220945 1908547556614801770165709)
        ·
          refine ⟨715705333730550663812141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1908547556614801770165709 715705333730550663812141)
          ·
            refine ⟨268389500148956498929553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 715705333730550663812141 268389500148956498929553)
            ·
              refine ⟨201292125111717374197165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268389500148956498929553 201292125111717374197165)
              ·
                refine ⟨75484546916894015323937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201292125111717374197165 75484546916894015323937)
                ·
                  rfl

theorem cell19_248072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 3].length) (baseStart_248072 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248072 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248072 prefixEnd_248072 := by exact prefixLift 248072
  have htrace : WordTrace (prefixWord ++ tailWord_248072) baseStart_248072 baseEnd_248072 := by
    simpa [prefixWord, tailWord_248072, baseEnd_248072] using wordTrace_append hprefix tailTrace_248072
  have hstable : (prefixWord ++ tailWord_248072).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248072).length < 2 ^ (prefixWord ++ tailWord_248072).sum := by decide
  have hdescent : baseEnd_248072 < baseStart_248072 := by decide
  rcases family_descends (prefixWord ++ tailWord_248072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248074 : List Nat := [3, 1, 2, 2, 1, 1, 6, 3]
def baseStart_248074 : Nat := 118140960795 + 248074 * 2 ^ 59
def prefixEnd_248074 : Nat := 4983230072969 + 3 ^ 40 * 248074 * 2
def baseEnd_248074 : Nat := 75485155486558603279487

theorem tailTrace_248074 : CollatzResearch.WordTrace tailWord_248074 prefixEnd_248074 75485155486558603279487 := by
  unfold tailWord_248074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2262000525819435127811819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6032001402185160340831517 2262000525819435127811819)
  ·
    refine ⟨3393000788729152691717729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2262000525819435127811819 3393000788729152691717729)
    ·
      refine ⟨2544750591546864518788297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3393000788729152691717729 2544750591546864518788297)
      ·
        refine ⟨1908562943660148389091223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2544750591546864518788297 1908562943660148389091223)
        ·
          refine ⟨2862844415490222583636835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1908562943660148389091223 2862844415490222583636835)
          ·
            refine ⟨4294266623235333875455253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862844415490222583636835 4294266623235333875455253)
            ·
              refine ⟨201293747964156275411965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4294266623235333875455253 201293747964156275411965)
              ·
                refine ⟨75485155486558603279487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201293747964156275411965 75485155486558603279487)
                ·
                  rfl

theorem cell19_248074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_248074 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248074 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248074 prefixEnd_248074 := by exact prefixLift 248074
  have htrace : WordTrace (prefixWord ++ tailWord_248074) baseStart_248074 baseEnd_248074 := by
    simpa [prefixWord, tailWord_248074, baseEnd_248074] using wordTrace_append hprefix tailTrace_248074
  have hstable : (prefixWord ++ tailWord_248074).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248074).length < 2 ^ (prefixWord ++ tailWord_248074).sum := by decide
  have hdescent : baseEnd_248074 < baseStart_248074 := by decide
  rcases family_descends (prefixWord ++ tailWord_248074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248076 : List Nat := [2, 2, 1, 2, 2, 2, 3, 5]
def baseStart_248076 : Nat := 118140960795 + 248076 * 2 ^ 59
def prefixEnd_248076 : Nat := 4983230072969 + 3 ^ 40 * 248076 * 2
def baseEnd_248076 : Nat := 75485764056223191235037

theorem tailTrace_248076 : CollatzResearch.WordTrace tailWord_248076 prefixEnd_248076 75485764056223191235037 := by
  unfold tailWord_248076
  simp only [CollatzResearch.WordTrace]
  refine ⟨4524037524635247426410041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6032050032846996568546721 4524037524635247426410041)
  ·
    refine ⟨3393028143476435569807531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4524037524635247426410041 3393028143476435569807531)
    ·
      refine ⟨5089542215214653354711297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3393028143476435569807531 5089542215214653354711297)
      ·
        refine ⟨3817156661410990016033473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5089542215214653354711297 3817156661410990016033473)
        ·
          refine ⟨2862867496058242512025105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3817156661410990016033473 2862867496058242512025105)
          ·
            refine ⟨2147150622043681884018829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2862867496058242512025105 2147150622043681884018829)
            ·
              refine ⟨805181483266380706507061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2147150622043681884018829 805181483266380706507061)
              ·
                refine ⟨75485764056223191235037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 805181483266380706507061 75485764056223191235037)
                ·
                  rfl

theorem cell19_248076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_248076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248076 prefixEnd_248076 := by exact prefixLift 248076
  have htrace : WordTrace (prefixWord ++ tailWord_248076) baseStart_248076 baseEnd_248076 := by
    simpa [prefixWord, tailWord_248076, baseEnd_248076] using wordTrace_append hprefix tailTrace_248076
  have hstable : (prefixWord ++ tailWord_248076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248076).length < 2 ^ (prefixWord ++ tailWord_248076).sum := by decide
  have hdescent : baseEnd_248076 < baseStart_248076 := by decide
  rcases family_descends (prefixWord ++ tailWord_248076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248095 : List Nat := [1, 1, 2, 4, 3, 1, 7]
def baseStart_248095 : Nat := 118140960795 + 248095 * 2 ^ 59
def prefixEnd_248095 : Nat := 4983230072969 + 3 ^ 40 * 248095 * 2
def baseEnd_248095 : Nat := 25163848489345592270921

theorem tailTrace_248095 : CollatzResearch.WordTrace tailWord_248095 prefixEnd_248095 25163848489345592270921 := by
  unfold tailWord_248095
  simp only [CollatzResearch.WordTrace]
  refine ⟨9048768036201661097761739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6032512024134440731841159 9048768036201661097761739)
  ·
    refine ⟨13573152054302491646642609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9048768036201661097761739 13573152054302491646642609)
    ·
      refine ⟨10179864040726868734981957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13573152054302491646642609 10179864040726868734981957)
      ·
        refine ⟨1908724507636287887809117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10179864040726868734981957 1908724507636287887809117)
        ·
          refine ⟨715771690363607957928419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1908724507636287887809117 715771690363607957928419)
          ·
            refine ⟨1073657535545411936892629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715771690363607957928419 1073657535545411936892629)
            ·
              refine ⟨25163848489345592270921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1073657535545411936892629 25163848489345592270921)
              ·
                rfl

theorem cell19_248095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 7].length) (baseStart_248095 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248095 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248095 prefixEnd_248095 := by exact prefixLift 248095
  have htrace : WordTrace (prefixWord ++ tailWord_248095) baseStart_248095 baseEnd_248095 := by
    simpa [prefixWord, tailWord_248095, baseEnd_248095] using wordTrace_append hprefix tailTrace_248095
  have hstable : (prefixWord ++ tailWord_248095).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248095).length < 2 ^ (prefixWord ++ tailWord_248095).sum := by decide
  have hdescent : baseEnd_248095 < baseStart_248095 := by decide
  rcases family_descends (prefixWord ++ tailWord_248095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248245 : List Nat := [1, 3, 3, 2, 3, 1, 1, 5]
def baseStart_248245 : Nat := 118140960795 + 248245 * 2 ^ 59
def prefixEnd_248245 : Nat := 4983230072969 + 3 ^ 40 * 248245 * 2
def baseEnd_248245 : Nat := 75537188192880873479021

theorem tailTrace_248245 : CollatzResearch.WordTrace tailWord_248245 prefixEnd_248245 75537188192880873479021 := by
  unfold tailWord_248245
  simp only [CollatzResearch.WordTrace]
  refine ⟨9054238985658236715722189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6036159323772157810481459 9054238985658236715722189)
  ·
    refine ⟨3395339619621838768395821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9054238985658236715722189 3395339619621838768395821)
    ·
      refine ⟨1273252357358189538148433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3395339619621838768395821 1273252357358189538148433)
      ·
        refine ⟨954939268018642153611325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1273252357358189538148433 954939268018642153611325)
        ·
          refine ⟨358102225506990807604247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 954939268018642153611325 358102225506990807604247)
          ·
            refine ⟨537153338260486211406371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358102225506990807604247 537153338260486211406371)
            ·
              refine ⟨805730007390729317109557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537153338260486211406371 805730007390729317109557)
              ·
                refine ⟨75537188192880873479021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 805730007390729317109557 75537188192880873479021)
                ·
                  rfl

theorem cell19_248245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 5].length) (baseStart_248245 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248245 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248245 prefixEnd_248245 := by exact prefixLift 248245
  have htrace : WordTrace (prefixWord ++ tailWord_248245) baseStart_248245 baseEnd_248245 := by
    simpa [prefixWord, tailWord_248245, baseEnd_248245] using wordTrace_append hprefix tailTrace_248245
  have hstable : (prefixWord ++ tailWord_248245).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248245).length < 2 ^ (prefixWord ++ tailWord_248245).sum := by decide
  have hdescent : baseEnd_248245 < baseStart_248245 := by decide
  rcases family_descends (prefixWord ++ tailWord_248245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248247 : List Nat := [1, 1, 3, 1, 3, 4, 1, 5]
def baseStart_248247 : Nat := 118140960795 + 248247 * 2 ^ 59
def prefixEnd_248247 : Nat := 4983230072969 + 3 ^ 40 * 248247 * 2
def baseEnd_248247 : Nat := 75537796762545461434571

theorem tailTrace_248247 : CollatzResearch.WordTrace tailWord_248247 prefixEnd_248247 75537796762545461434571 := by
  unfold tailWord_248247
  simp only [CollatzResearch.WordTrace]
  refine ⟨9054311931650991057294995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6036207954433994038196663 9054311931650991057294995)
  ·
    refine ⟨13581467897476486585942493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9054311931650991057294995 13581467897476486585942493)
    ·
      refine ⟨5093050461553682469728435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13581467897476486585942493 5093050461553682469728435)
      ·
        refine ⟨7639575692330523704592653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5093050461553682469728435 7639575692330523704592653)
        ·
          refine ⟨2864840884623946389222245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7639575692330523704592653 2864840884623946389222245)
          ·
            refine ⟨537157665866989947979171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2864840884623946389222245 537157665866989947979171)
            ·
              refine ⟨805736498800484921968757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537157665866989947979171 805736498800484921968757)
              ·
                refine ⟨75537796762545461434571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 805736498800484921968757 75537796762545461434571)
                ·
                  rfl

theorem cell19_248247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 5].length) (baseStart_248247 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248247 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248247 prefixEnd_248247 := by exact prefixLift 248247
  have htrace : WordTrace (prefixWord ++ tailWord_248247) baseStart_248247 baseEnd_248247 := by
    simpa [prefixWord, tailWord_248247, baseEnd_248247] using wordTrace_append hprefix tailTrace_248247
  have hstable : (prefixWord ++ tailWord_248247).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248247).length < 2 ^ (prefixWord ++ tailWord_248247).sum := by decide
  have hdescent : baseEnd_248247 < baseStart_248247 := by decide
  rcases family_descends (prefixWord ++ tailWord_248247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248363 : List Nat := [1, 1, 1, 1, 2, 1, 3, 9]
def baseStart_248363 : Nat := 118140960795 + 248363 * 2 ^ 59
def prefixEnd_248363 : Nat := 4983230072969 + 3 ^ 40 * 248363 * 2
def baseEnd_248363 : Nat := 75573093803091562856477

theorem tailTrace_248363 : CollatzResearch.WordTrace tailWord_248363 prefixEnd_248363 75573093803091562856477 := by
  unfold tailWord_248363
  simp only [CollatzResearch.WordTrace]
  refine ⟨9058542799230742868517743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6039028532820495245678495 9058542799230742868517743)
  ·
    refine ⟨13587814198846114302776615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9058542799230742868517743 13587814198846114302776615)
    ·
      refine ⟨20381721298269171454164923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13587814198846114302776615 20381721298269171454164923)
      ·
        refine ⟨30572581947403757181247385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20381721298269171454164923 30572581947403757181247385)
        ·
          refine ⟨22929436460552817885935539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30572581947403757181247385 22929436460552817885935539)
          ·
            refine ⟨34394154690829226828903309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22929436460552817885935539 34394154690829226828903309)
            ·
              refine ⟨12897808009060960060838741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34394154690829226828903309 12897808009060960060838741)
              ·
                refine ⟨75573093803091562856477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12897808009060960060838741 75573093803091562856477)
                ·
                  rfl

theorem cell19_248363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_248363 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248363 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248363 prefixEnd_248363 := by exact prefixLift 248363
  have htrace : WordTrace (prefixWord ++ tailWord_248363) baseStart_248363 baseEnd_248363 := by
    simpa [prefixWord, tailWord_248363, baseEnd_248363] using wordTrace_append hprefix tailTrace_248363
  have hstable : (prefixWord ++ tailWord_248363).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248363).length < 2 ^ (prefixWord ++ tailWord_248363).sum := by decide
  have hdescent : baseEnd_248363 < baseStart_248363 := by decide
  rcases family_descends (prefixWord ++ tailWord_248363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248380 : List Nat := [2, 2, 2, 2, 3, 2, 6]
def baseStart_248380 : Nat := 118140960795 + 248380 * 2 ^ 59
def prefixEnd_248380 : Nat := 4983230072969 + 3 ^ 40 * 248380 * 2
def baseEnd_248380 : Nat := 25192755548413520159551

theorem tailTrace_248380 : CollatzResearch.WordTrace tailWord_248380 prefixEnd_248380 25192755548413520159551 := by
  unfold tailWord_248380
  simp only [CollatzResearch.WordTrace]
  refine ⟨4529581420084577385943297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6039441893446103181257729 4529581420084577385943297)
  ·
    refine ⟨3397186065063433039457473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4529581420084577385943297 3397186065063433039457473)
    ·
      refine ⟨2547889548797574779593105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3397186065063433039457473 2547889548797574779593105)
      ·
        refine ⟨1910917161598181084694829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2547889548797574779593105 1910917161598181084694829)
        ·
          refine ⟨716593935599317906760561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1910917161598181084694829 716593935599317906760561)
          ·
            refine ⟨537445451699488430070421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 716593935599317906760561 537445451699488430070421)
            ·
              refine ⟨25192755548413520159551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 537445451699488430070421 25192755548413520159551)
              ·
                rfl

theorem cell19_248380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 6].length) (baseStart_248380 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248380 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248380 prefixEnd_248380 := by exact prefixLift 248380
  have htrace : WordTrace (prefixWord ++ tailWord_248380) baseStart_248380 baseEnd_248380 := by
    simpa [prefixWord, tailWord_248380, baseEnd_248380] using wordTrace_append hprefix tailTrace_248380
  have hstable : (prefixWord ++ tailWord_248380).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248380).length < 2 ^ (prefixWord ++ tailWord_248380).sum := by decide
  have hdescent : baseEnd_248380 < baseStart_248380 := by decide
  rcases family_descends (prefixWord ++ tailWord_248380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248412 : List Nat := [2, 2, 4, 1, 4, 1, 2, 3]
def baseStart_248412 : Nat := 118140960795 + 248412 * 2 ^ 59
def prefixEnd_248412 : Nat := 4983230072969 + 3 ^ 40 * 248412 * 2
def baseEnd_248412 : Nat := 75588003759873967767455

theorem tailTrace_248412 : CollatzResearch.WordTrace tailWord_248412 prefixEnd_248412 75588003759873967767455 := by
  unfold tailWord_248412
  simp only [CollatzResearch.WordTrace]
  refine ⟨4530164988026612118525745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6040219984035482824700993 4530164988026612118525745)
  ·
    refine ⟨3397623741019959088894309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4530164988026612118525745 3397623741019959088894309)
    ·
      refine ⟨637054451441242329167683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3397623741019959088894309 637054451441242329167683)
      ·
        refine ⟨955581677161863493751525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637054451441242329167683 955581677161863493751525)
        ·
          refine ⟨179171564467849405078411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 955581677161863493751525 179171564467849405078411)
          ·
            refine ⟨268757346701774107617617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179171564467849405078411 268757346701774107617617)
            ·
              refine ⟨201568010026330580713213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268757346701774107617617 201568010026330580713213)
              ·
                refine ⟨75588003759873967767455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201568010026330580713213 75588003759873967767455)
                ·
                  rfl

theorem cell19_248412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 3].length) (baseStart_248412 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248412 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248412 prefixEnd_248412 := by exact prefixLift 248412
  have htrace : WordTrace (prefixWord ++ tailWord_248412) baseStart_248412 baseEnd_248412 := by
    simpa [prefixWord, tailWord_248412, baseEnd_248412] using wordTrace_append hprefix tailTrace_248412
  have hstable : (prefixWord ++ tailWord_248412).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248412).length < 2 ^ (prefixWord ++ tailWord_248412).sum := by decide
  have hdescent : baseEnd_248412 < baseStart_248412 := by decide
  rcases family_descends (prefixWord ++ tailWord_248412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248439 : List Nat := [1, 1, 3, 1, 1, 3, 9]
def baseStart_248439 : Nat := 118140960795 + 248439 * 2 ^ 59
def prefixEnd_248439 : Nat := 4983230072969 + 3 ^ 40 * 248439 * 2
def baseEnd_248439 : Nat := 25198739816781968389127

theorem tailTrace_248439 : CollatzResearch.WordTrace tailWord_248439 prefixEnd_248439 25198739816781968389127 := by
  unfold tailWord_248439
  simp only [CollatzResearch.WordTrace]
  refine ⟨9061314746955407848284371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6040876497970271898856247 9061314746955407848284371)
  ·
    refine ⟨13591972120433111772426557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9061314746955407848284371 13591972120433111772426557)
    ·
      refine ⟨5096989545162416914659959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13591972120433111772426557 5096989545162416914659959)
      ·
        refine ⟨7645484317743625371989939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5096989545162416914659959 7645484317743625371989939)
        ·
          refine ⟨11468226476615438057984909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7645484317743625371989939 11468226476615438057984909)
          ·
            refine ⟨4300584928730789271744341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11468226476615438057984909 4300584928730789271744341)
            ·
              refine ⟨25198739816781968389127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4300584928730789271744341 25198739816781968389127)
              ·
                rfl

theorem cell19_248439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 9].length) (baseStart_248439 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248439 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248439 prefixEnd_248439 := by exact prefixLift 248439
  have htrace : WordTrace (prefixWord ++ tailWord_248439) baseStart_248439 baseEnd_248439 := by
    simpa [prefixWord, tailWord_248439, baseEnd_248439] using wordTrace_append hprefix tailTrace_248439
  have hstable : (prefixWord ++ tailWord_248439).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248439).length < 2 ^ (prefixWord ++ tailWord_248439).sum := by decide
  have hdescent : baseEnd_248439 < baseStart_248439 := by decide
  rcases family_descends (prefixWord ++ tailWord_248439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248490 : List Nat := [3, 1, 5, 2, 2, 6]
def baseStart_248490 : Nat := 118140960795 + 248490 * 2 ^ 59
def prefixEnd_248490 : Nat := 4983230072969 + 3 ^ 40 * 248490 * 2
def baseEnd_248490 : Nat := 8401304219643655337101

theorem tailTrace_248490 : CollatzResearch.WordTrace tailWord_248490 prefixEnd_248490 8401304219643655337101 := by
  unfold tailWord_248490
  simp only [CollatzResearch.WordTrace]
  refine ⟨2265793717442660889597731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6042116579847095705593949 2265793717442660889597731)
  ·
    refine ⟨3398690576163991334396597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2265793717442660889597731 3398690576163991334396597)
    ·
      refine ⟨318627241515374187599681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3398690576163991334396597 318627241515374187599681)
      ·
        refine ⟨238970431136530640699761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318627241515374187599681 238970431136530640699761)
        ·
          refine ⟨179227823352397980524821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238970431136530640699761 179227823352397980524821)
          ·
            refine ⟨8401304219643655337101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 179227823352397980524821 8401304219643655337101)
            ·
              rfl

theorem cell19_248490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 6].length) (baseStart_248490 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248490 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248490 prefixEnd_248490 := by exact prefixLift 248490
  have htrace : WordTrace (prefixWord ++ tailWord_248490) baseStart_248490 baseEnd_248490 := by
    simpa [prefixWord, tailWord_248490, baseEnd_248490] using wordTrace_append hprefix tailTrace_248490
  have hstable : (prefixWord ++ tailWord_248490).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248490).length < 2 ^ (prefixWord ++ tailWord_248490).sum := by decide
  have hdescent : baseEnd_248490 < baseStart_248490 := by decide
  rcases family_descends (prefixWord ++ tailWord_248490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248591 : List Nat := [1, 1, 2, 1, 1, 1, 7, 5]
def baseStart_248591 : Nat := 118140960795 + 248591 * 2 ^ 59
def prefixEnd_248591 : Nat := 4983230072969 + 3 ^ 40 * 248591 * 2
def baseEnd_248591 : Nat := 75642470744854589789189

theorem tailTrace_248591 : CollatzResearch.WordTrace tailWord_248591 prefixEnd_248591 75642470744854589789189 := by
  unfold tailWord_248591
  simp only [CollatzResearch.WordTrace]
  refine ⟨9066858642404737807817627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6044572428269825205211751 9066858642404737807817627)
  ·
    refine ⟨13600287963607106711726441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9066858642404737807817627 13600287963607106711726441)
    ·
      refine ⟨10200215972705330033794831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13600287963607106711726441 10200215972705330033794831)
      ·
        refine ⟨15300323959057995050692247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10200215972705330033794831 15300323959057995050692247)
        ·
          refine ⟨22950485938586992576038371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15300323959057995050692247 22950485938586992576038371)
          ·
            refine ⟨34425728907880488864057557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22950485938586992576038371 34425728907880488864057557)
            ·
              refine ⟨806853021278448957751349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 34425728907880488864057557 806853021278448957751349)
              ·
                refine ⟨75642470744854589789189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 806853021278448957751349 75642470744854589789189)
                ·
                  rfl

theorem cell19_248591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_248591 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248591 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248591 prefixEnd_248591 := by exact prefixLift 248591
  have htrace : WordTrace (prefixWord ++ tailWord_248591) baseStart_248591 baseEnd_248591 := by
    simpa [prefixWord, tailWord_248591, baseEnd_248591] using wordTrace_append hprefix tailTrace_248591
  have hstable : (prefixWord ++ tailWord_248591).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248591).length < 2 ^ (prefixWord ++ tailWord_248591).sum := by decide
  have hdescent : baseEnd_248591 < baseStart_248591 := by decide
  rcases family_descends (prefixWord ++ tailWord_248591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248608 : List Nat := [2, 1, 1, 5, 1, 4, 5]
def baseStart_248608 : Nat := 118140960795 + 248608 * 2 ^ 59
def prefixEnd_248608 : Nat := 4983230072969 + 3 ^ 40 * 248608 * 2
def baseEnd_248608 : Nat := 25215881195667862470455

theorem tailTrace_248608 : CollatzResearch.WordTrace tailWord_248608 prefixEnd_248608 25215881195667862470455 := by
  unfold tailWord_248608
  simp only [CollatzResearch.WordTrace]
  refine ⟨4533739341671574855593239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6044985788895433140790985 4533739341671574855593239)
  ·
    refine ⟨6800609012507362283389859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4533739341671574855593239 6800609012507362283389859)
    ·
      refine ⟨10200913518761043425084789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6800609012507362283389859 10200913518761043425084789)
      ·
        refine ⟨956335642383847821101699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10200913518761043425084789 956335642383847821101699)
        ·
          refine ⟨1434503463575771731652549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 956335642383847821101699 1434503463575771731652549)
          ·
            refine ⟨268969399420457199684853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1434503463575771731652549 268969399420457199684853)
            ·
              refine ⟨25215881195667862470455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 268969399420457199684853 25215881195667862470455)
              ·
                rfl

theorem cell19_248608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 5].length) (baseStart_248608 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248608 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248608 prefixEnd_248608 := by exact prefixLift 248608
  have htrace : WordTrace (prefixWord ++ tailWord_248608) baseStart_248608 baseEnd_248608 := by
    simpa [prefixWord, tailWord_248608, baseEnd_248608] using wordTrace_append hprefix tailTrace_248608
  have hstable : (prefixWord ++ tailWord_248608).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248608).length < 2 ^ (prefixWord ++ tailWord_248608).sum := by decide
  have hdescent : baseEnd_248608 < baseStart_248608 := by decide
  rcases family_descends (prefixWord ++ tailWord_248608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248627 : List Nat := [1, 1, 1, 2, 6, 2, 2, 4]
def baseStart_248627 : Nat := 118140960795 + 248627 * 2 ^ 59
def prefixEnd_248627 : Nat := 4983230072969 + 3 ^ 40 * 248627 * 2
def baseEnd_248627 : Nat := 75653424998817172989091

theorem tailTrace_248627 : CollatzResearch.WordTrace tailWord_248627 prefixEnd_248627 75653424998817172989091 := by
  unfold tailWord_248627
  simp only [CollatzResearch.WordTrace]
  refine ⟨9068171670274315956128135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6045447780182877304085423 9068171670274315956128135)
  ·
    refine ⟨13602257505411473934192203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9068171670274315956128135 13602257505411473934192203)
    ·
      refine ⟨20403386258117210901288305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13602257505411473934192203 20403386258117210901288305)
      ·
        refine ⟨15302539693587908175966229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20403386258117210901288305 15302539693587908175966229)
        ·
          refine ⟨717306548136933195748417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15302539693587908175966229 717306548136933195748417)
          ·
            refine ⟨537979911102699896811313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717306548136933195748417 537979911102699896811313)
            ·
              refine ⟨403484933327024922608485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537979911102699896811313 403484933327024922608485)
              ·
                refine ⟨75653424998817172989091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 403484933327024922608485 75653424998817172989091)
                ·
                  rfl

theorem cell19_248627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 4].length) (baseStart_248627 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248627 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248627 prefixEnd_248627 := by exact prefixLift 248627
  have htrace : WordTrace (prefixWord ++ tailWord_248627) baseStart_248627 baseEnd_248627 := by
    simpa [prefixWord, tailWord_248627, baseEnd_248627] using wordTrace_append hprefix tailTrace_248627
  have hstable : (prefixWord ++ tailWord_248627).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248627).length < 2 ^ (prefixWord ++ tailWord_248627).sum := by decide
  have hdescent : baseEnd_248627 < baseStart_248627 := by decide
  rcases family_descends (prefixWord ++ tailWord_248627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248648 : List Nat := [2, 1, 3, 1, 1, 3, 1, 7]
def baseStart_248648 : Nat := 118140960795 + 248648 * 2 ^ 59
def prefixEnd_248648 : Nat := 4983230072969 + 3 ^ 40 * 248648 * 2
def baseEnd_248648 : Nat := 75659814980295346522367

theorem tailTrace_248648 : CollatzResearch.WordTrace tailWord_248648 prefixEnd_248648 75659814980295346522367 := by
  unfold tailWord_248648
  simp only [CollatzResearch.WordTrace]
  refine ⟨4534468801599118271321299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6045958402132157695095065 4534468801599118271321299)
  ·
    refine ⟨6801703202398677406981949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4534468801599118271321299 6801703202398677406981949)
    ·
      refine ⟨2550638700899504027618231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6801703202398677406981949 2550638700899504027618231)
      ·
        refine ⟨3825958051349256041427347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2550638700899504027618231 3825958051349256041427347)
        ·
          refine ⟨5738937077023884062141021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3825958051349256041427347 5738937077023884062141021)
          ·
            refine ⟨2152101403883956523302883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5738937077023884062141021 2152101403883956523302883)
            ·
              refine ⟨3228152105825934784954325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2152101403883956523302883 3228152105825934784954325)
              ·
                refine ⟨75659814980295346522367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3228152105825934784954325 75659814980295346522367)
                ·
                  rfl

theorem cell19_248648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_248648 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248648 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248648 prefixEnd_248648 := by exact prefixLift 248648
  have htrace : WordTrace (prefixWord ++ tailWord_248648) baseStart_248648 baseEnd_248648 := by
    simpa [prefixWord, tailWord_248648, baseEnd_248648] using wordTrace_append hprefix tailTrace_248648
  have hstable : (prefixWord ++ tailWord_248648).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248648).length < 2 ^ (prefixWord ++ tailWord_248648).sum := by decide
  have hdescent : baseEnd_248648 < baseStart_248648 := by decide
  rcases family_descends (prefixWord ++ tailWord_248648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248756 : List Nat := [2, 5, 2, 1, 1, 1, 4, 3]
def baseStart_248756 : Nat := 118140960795 + 248756 * 2 ^ 59
def prefixEnd_248756 : Nat := 4983230072969 + 3 ^ 40 * 248756 * 2
def baseEnd_248756 : Nat := 75692677742183096122073

theorem tailTrace_248756 : CollatzResearch.WordTrace tailWord_248756 prefixEnd_248756 75692677742183096122073 := by
  unfold tailWord_248756
  simp only [CollatzResearch.WordTrace]
  refine ⟨4536438343403485493787061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6048584457871313991716081 4536438343403485493787061)
  ·
    refine ⟨425291094694076765042537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4536438343403485493787061 425291094694076765042537)
    ·
      refine ⟨318968321020557573781903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425291094694076765042537 318968321020557573781903)
      ·
        refine ⟨478452481530836360672855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318968321020557573781903 478452481530836360672855)
        ·
          refine ⟨717678722296254541009283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478452481530836360672855 717678722296254541009283)
          ·
            refine ⟨1076518083444381811513925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717678722296254541009283 1076518083444381811513925)
            ·
              refine ⟨201847140645821589658861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1076518083444381811513925 201847140645821589658861)
              ·
                refine ⟨75692677742183096122073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201847140645821589658861 75692677742183096122073)
                ·
                  rfl

theorem cell19_248756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 3].length) (baseStart_248756 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248756 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248756 prefixEnd_248756 := by exact prefixLift 248756
  have htrace : WordTrace (prefixWord ++ tailWord_248756) baseStart_248756 baseEnd_248756 := by
    simpa [prefixWord, tailWord_248756, baseEnd_248756] using wordTrace_append hprefix tailTrace_248756
  have hstable : (prefixWord ++ tailWord_248756).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248756).length < 2 ^ (prefixWord ++ tailWord_248756).sum := by decide
  have hdescent : baseEnd_248756 < baseStart_248756 := by decide
  rcases family_descends (prefixWord ++ tailWord_248756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248760 : List Nat := [2, 1, 2, 1, 2, 4, 4, 3]
def baseStart_248760 : Nat := 118140960795 + 248760 * 2 ^ 59
def prefixEnd_248760 : Nat := 4983230072969 + 3 ^ 40 * 248760 * 2
def baseEnd_248760 : Nat := 75693894881512272033173

theorem tailTrace_248760 : CollatzResearch.WordTrace tailWord_248760 prefixEnd_248760 75693894881512272033173 := by
  unfold tailWord_248760
  simp only [CollatzResearch.WordTrace]
  refine ⟨4536511289396239835359867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6048681719194986447146489 4536511289396239835359867)
  ·
    refine ⟨6804766934094359753039801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4536511289396239835359867 6804766934094359753039801)
    ·
      refine ⟨5103575200570769814779851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6804766934094359753039801 5103575200570769814779851)
      ·
        refine ⟨7655362800856154722169777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5103575200570769814779851 7655362800856154722169777)
        ·
          refine ⟨5741522100642116041627333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7655362800856154722169777 5741522100642116041627333)
          ·
            refine ⟨1076535393870396757805125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5741522100642116041627333 1076535393870396757805125)
            ·
              refine ⟨201850386350699392088461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1076535393870396757805125 201850386350699392088461)
              ·
                refine ⟨75693894881512272033173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201850386350699392088461 75693894881512272033173)
                ·
                  rfl

theorem cell19_248760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 3].length) (baseStart_248760 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248760 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248760 prefixEnd_248760 := by exact prefixLift 248760
  have htrace : WordTrace (prefixWord ++ tailWord_248760) baseStart_248760 baseEnd_248760 := by
    simpa [prefixWord, tailWord_248760, baseEnd_248760] using wordTrace_append hprefix tailTrace_248760
  have hstable : (prefixWord ++ tailWord_248760).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248760).length < 2 ^ (prefixWord ++ tailWord_248760).sum := by decide
  have hdescent : baseEnd_248760 < baseStart_248760 := by decide
  rcases family_descends (prefixWord ++ tailWord_248760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248762 : List Nat := [3, 1, 1, 1, 2, 1, 5, 5]
def baseStart_248762 : Nat := 118140960795 + 248762 * 2 ^ 59
def prefixEnd_248762 : Nat := 4983230072969 + 3 ^ 40 * 248762 * 2
def baseEnd_248762 : Nat := 75694503451176859988723

theorem tailTrace_248762 : CollatzResearch.WordTrace tailWord_248762 prefixEnd_248762 75694503451176859988723 := by
  unfold tailWord_248762
  simp only [CollatzResearch.WordTrace]
  refine ⟨2268273881196308503073135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6048730349856822674861693 2268273881196308503073135)
  ·
    refine ⟨3402410821794462754609703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2268273881196308503073135 3402410821794462754609703)
    ·
      refine ⟨5103616232691694131914555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3402410821794462754609703 5103616232691694131914555)
      ·
        refine ⟨7655424349037541197871833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5103616232691694131914555 7655424349037541197871833)
        ·
          refine ⟨5741568261778155898403875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7655424349037541197871833 5741568261778155898403875)
          ·
            refine ⟨8612352392667233847605813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5741568261778155898403875 8612352392667233847605813)
            ·
              refine ⟨807408036812553173213045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8612352392667233847605813 807408036812553173213045)
              ·
                refine ⟨75694503451176859988723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 807408036812553173213045 75694503451176859988723)
                ·
                  rfl

theorem cell19_248762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_248762 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248762 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248762 prefixEnd_248762 := by exact prefixLift 248762
  have htrace : WordTrace (prefixWord ++ tailWord_248762) baseStart_248762 baseEnd_248762 := by
    simpa [prefixWord, tailWord_248762, baseEnd_248762] using wordTrace_append hprefix tailTrace_248762
  have hstable : (prefixWord ++ tailWord_248762).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248762).length < 2 ^ (prefixWord ++ tailWord_248762).sum := by decide
  have hdescent : baseEnd_248762 < baseStart_248762 := by decide
  rcases family_descends (prefixWord ++ tailWord_248762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248834 : List Nat := [3, 4, 1, 3, 1, 7]
def baseStart_248834 : Nat := 118140960795 + 248834 * 2 ^ 59
def prefixEnd_248834 : Nat := 4983230072969 + 3 ^ 40 * 248834 * 2
def baseEnd_248834 : Nat := 8412934662122447376503

theorem tailTrace_248834 : CollatzResearch.WordTrace tailWord_248834 prefixEnd_248834 8412934662122447376503 := by
  unfold tailWord_248834
  simp only [CollatzResearch.WordTrace]
  refine ⟨2268930395131097577228389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6050481053682926872609037 2268930395131097577228389)
  ·
    refine ⟨425424449087080795730323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2268930395131097577228389 425424449087080795730323)
    ·
      refine ⟨638136673630621193595485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425424449087080795730323 638136673630621193595485)
      ·
        refine ⟨239301252611482947598307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 638136673630621193595485 239301252611482947598307)
        ·
          refine ⟨358951878917224421397461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239301252611482947598307 358951878917224421397461)
          ·
            refine ⟨8412934662122447376503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 358951878917224421397461 8412934662122447376503)
            ·
              rfl

theorem cell19_248834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 7].length) (baseStart_248834 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248834 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248834 prefixEnd_248834 := by exact prefixLift 248834
  have htrace : WordTrace (prefixWord ++ tailWord_248834) baseStart_248834 baseEnd_248834 := by
    simpa [prefixWord, tailWord_248834, baseEnd_248834] using wordTrace_append hprefix tailTrace_248834
  have hstable : (prefixWord ++ tailWord_248834).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248834).length < 2 ^ (prefixWord ++ tailWord_248834).sum := by decide
  have hdescent : baseEnd_248834 < baseStart_248834 := by decide
  rcases family_descends (prefixWord ++ tailWord_248834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248855 : List Nat := [1, 1, 3, 5, 1, 1, 3, 4]
def baseStart_248855 : Nat := 118140960795 + 248855 * 2 ^ 59
def prefixEnd_248855 : Nat := 4983230072969 + 3 ^ 40 * 248855 * 2
def baseEnd_248855 : Nat := 75722801940580199921803

theorem tailTrace_248855 : CollatzResearch.WordTrace tailWord_248855 prefixEnd_248855 75722801940580199921803 := by
  unfold tailWord_248855
  simp only [CollatzResearch.WordTrace]
  refine ⟨9076487513448310895428019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6050991675632207263618679 9076487513448310895428019)
  ·
    refine ⟨13614731270172466343142029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9076487513448310895428019 13614731270172466343142029)
    ·
      refine ⟨5105524226314674878678261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13614731270172466343142029 5105524226314674878678261)
      ·
        refine ⟨478642896217000769876087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5105524226314674878678261 478642896217000769876087)
        ·
          refine ⟨717964344325501154814131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478642896217000769876087 717964344325501154814131)
          ·
            refine ⟨1076946516488251732221197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717964344325501154814131 1076946516488251732221197)
            ·
              refine ⟨403854943683094399582949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1076946516488251732221197 403854943683094399582949)
              ·
                refine ⟨75722801940580199921803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 403854943683094399582949 75722801940580199921803)
                ·
                  rfl

theorem cell19_248855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 4].length) (baseStart_248855 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248855 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248855 prefixEnd_248855 := by exact prefixLift 248855
  have htrace : WordTrace (prefixWord ++ tailWord_248855) baseStart_248855 baseEnd_248855 := by
    simpa [prefixWord, tailWord_248855, baseEnd_248855] using wordTrace_append hprefix tailTrace_248855
  have hstable : (prefixWord ++ tailWord_248855).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248855).length < 2 ^ (prefixWord ++ tailWord_248855).sum := by decide
  have hdescent : baseEnd_248855 < baseStart_248855 := by decide
  rcases family_descends (prefixWord ++ tailWord_248855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248857 : List Nat := [1, 2, 1, 2, 1, 1, 7, 4]
def baseStart_248857 : Nat := 118140960795 + 248857 * 2 ^ 59
def prefixEnd_248857 : Nat := 4983230072969 + 3 ^ 40 * 248857 * 2
def baseEnd_248857 : Nat := 75723410510244787877353

theorem tailTrace_248857 : CollatzResearch.WordTrace tailWord_248857 prefixEnd_248857 75723410510244787877353 := by
  unfold tailWord_248857
  simp only [CollatzResearch.WordTrace]
  refine ⟨9076560459441065237000825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6051040306294043491333883 9076560459441065237000825)
  ·
    refine ⟨6807420344580798927750619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9076560459441065237000825 6807420344580798927750619)
    ·
      refine ⟨10211130516871198391625929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6807420344580798927750619 10211130516871198391625929)
      ·
        refine ⟨7658347887653398793719447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10211130516871198391625929 7658347887653398793719447)
        ·
          refine ⟨11487521831480098190579171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7658347887653398793719447 11487521831480098190579171)
          ·
            refine ⟨17231282747220147285868757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11487521831480098190579171 17231282747220147285868757)
            ·
              refine ⟨403858189387972202012549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 17231282747220147285868757 403858189387972202012549)
              ·
                refine ⟨75723410510244787877353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 403858189387972202012549 75723410510244787877353)
                ·
                  rfl

theorem cell19_248857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 4].length) (baseStart_248857 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248857 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248857 prefixEnd_248857 := by exact prefixLift 248857
  have htrace : WordTrace (prefixWord ++ tailWord_248857) baseStart_248857 baseEnd_248857 := by
    simpa [prefixWord, tailWord_248857, baseEnd_248857] using wordTrace_append hprefix tailTrace_248857
  have hstable : (prefixWord ++ tailWord_248857).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248857).length < 2 ^ (prefixWord ++ tailWord_248857).sum := by decide
  have hdescent : baseEnd_248857 < baseStart_248857 := by decide
  rcases family_descends (prefixWord ++ tailWord_248857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248925 : List Nat := [1, 4, 4, 1, 3, 1, 2, 3]
def baseStart_248925 : Nat := 118140960795 + 248925 * 2 ^ 59
def prefixEnd_248925 : Nat := 4983230072969 + 3 ^ 40 * 248925 * 2
def baseEnd_248925 : Nat := 75744101878840778366057

theorem tailTrace_248925 : CollatzResearch.WordTrace tailWord_248925 prefixEnd_248925 75744101878840778366057 := by
  unfold tailWord_248925
  simp only [CollatzResearch.WordTrace]
  refine ⟨9079040623194712850476229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6052693748796475233650819 9079040623194712850476229)
  ·
    refine ⟨1702320116849008659464293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9079040623194712850476229 1702320116849008659464293)
    ·
      refine ⟨319185021909189123649555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1702320116849008659464293 319185021909189123649555)
      ·
        refine ⟨478777532863783685474333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319185021909189123649555 478777532863783685474333)
        ·
          refine ⟨179541574823918882052875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478777532863783685474333 179541574823918882052875)
          ·
            refine ⟨269312362235878323079313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179541574823918882052875 269312362235878323079313)
            ·
              refine ⟨201984271676908742309485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269312362235878323079313 201984271676908742309485)
              ·
                refine ⟨75744101878840778366057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 201984271676908742309485 75744101878840778366057)
                ·
                  rfl

theorem cell19_248925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 3].length) (baseStart_248925 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248925 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248925 prefixEnd_248925 := by exact prefixLift 248925
  have htrace : WordTrace (prefixWord ++ tailWord_248925) baseStart_248925 baseEnd_248925 := by
    simpa [prefixWord, tailWord_248925, baseEnd_248925] using wordTrace_append hprefix tailTrace_248925
  have hstable : (prefixWord ++ tailWord_248925).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248925).length < 2 ^ (prefixWord ++ tailWord_248925).sum := by decide
  have hdescent : baseEnd_248925 < baseStart_248925 := by decide
  rcases family_descends (prefixWord ++ tailWord_248925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248933 : List Nat := [1, 3, 1, 3, 2, 1, 3, 5]
def baseStart_248933 : Nat := 118140960795 + 248933 * 2 ^ 59
def prefixEnd_248933 : Nat := 4983230072969 + 3 ^ 40 * 248933 * 2
def baseEnd_248933 : Nat := 75746536157499130188257

theorem tailTrace_248933 : CollatzResearch.WordTrace tailWord_248933 prefixEnd_248933 75746536157499130188257 := by
  unfold tailWord_248933
  simp only [CollatzResearch.WordTrace]
  refine ⟨9079332407165730216767453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6052888271443820144511635 9079332407165730216767453)
  ·
    refine ⟨3404749652687148831287795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9079332407165730216767453 3404749652687148831287795)
    ·
      refine ⟨5107124479030723246931693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3404749652687148831287795 5107124479030723246931693)
      ·
        refine ⟨1915171679636521217599385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5107124479030723246931693 1915171679636521217599385)
        ·
          refine ⟨1436378759727390913199539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1915171679636521217599385 1436378759727390913199539)
          ·
            refine ⟨2154568139591086369799309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1436378759727390913199539 2154568139591086369799309)
            ·
              refine ⟨807963052346657388674741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2154568139591086369799309 807963052346657388674741)
              ·
                refine ⟨75746536157499130188257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 807963052346657388674741 75746536157499130188257)
                ·
                  rfl

theorem cell19_248933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_248933 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_248933 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_248933 prefixEnd_248933 := by exact prefixLift 248933
  have htrace : WordTrace (prefixWord ++ tailWord_248933) baseStart_248933 baseEnd_248933 := by
    simpa [prefixWord, tailWord_248933, baseEnd_248933] using wordTrace_append hprefix tailTrace_248933
  have hstable : (prefixWord ++ tailWord_248933).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248933).length < 2 ^ (prefixWord ++ tailWord_248933).sum := by decide
  have hdescent : baseEnd_248933 < baseStart_248933 := by decide
  rcases family_descends (prefixWord ++ tailWord_248933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249009 : List Nat := [1, 2, 2, 5, 1, 8]
def baseStart_249009 : Nat := 118140960795 + 249009 * 2 ^ 59
def prefixEnd_249009 : Nat := 4983230072969 + 3 ^ 40 * 249009 * 2
def baseEnd_249009 : Nat := 8418851311639274722129

theorem tailTrace_249009 : CollatzResearch.WordTrace tailWord_249009 prefixEnd_249009 8418851311639274722129 := by
  unfold tailWord_249009
  simp only [CollatzResearch.WordTrace]
  refine ⟨9082104354890395196534081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6054736236593596797689387 9082104354890395196534081)
  ·
    refine ⟨6811578266167796397400561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9082104354890395196534081 6811578266167796397400561)
    ·
      refine ⟨5108683699625847298050421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6811578266167796397400561 5108683699625847298050421)
      ·
        refine ⟨478939096839923184192227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5108683699625847298050421 478939096839923184192227)
        ·
          refine ⟨718408645259884776288341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478939096839923184192227 718408645259884776288341)
          ·
            refine ⟨8418851311639274722129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 718408645259884776288341 8418851311639274722129)
            ·
              rfl

theorem cell19_249009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 8].length) (baseStart_249009 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_249009 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_249009 prefixEnd_249009 := by exact prefixLift 249009
  have htrace : WordTrace (prefixWord ++ tailWord_249009) baseStart_249009 baseEnd_249009 := by
    simpa [prefixWord, tailWord_249009, baseEnd_249009] using wordTrace_append hprefix tailTrace_249009
  have hstable : (prefixWord ++ tailWord_249009).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249009).length < 2 ^ (prefixWord ++ tailWord_249009).sum := by decide
  have hdescent : baseEnd_249009 < baseStart_249009 := by decide
  rcases family_descends (prefixWord ++ tailWord_249009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249024 : List Nat := [2, 1, 1, 2, 7, 1, 1, 4]
def baseStart_249024 : Nat := 118140960795 + 249024 * 2 ^ 59
def prefixEnd_249024 : Nat := 4983230072969 + 3 ^ 40 * 249024 * 2
def baseEnd_249024 : Nat := 75774226077237882165787

theorem tailTrace_249024 : CollatzResearch.WordTrace tailWord_249024 prefixEnd_249024 75774226077237882165787 := by
  unfold tailWord_249024
  simp only [CollatzResearch.WordTrace]
  refine ⟨4541325724918026379165063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6055100966557368505553417 4541325724918026379165063)
  ·
    refine ⟨6811988587377039568747595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4541325724918026379165063 6811988587377039568747595)
    ·
      refine ⟨10217982881065559353121393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6811988587377039568747595 10217982881065559353121393)
      ·
        refine ⟨7663487160799169514841045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10217982881065559353121393 7663487160799169514841045)
        ·
          refine ⟨179612980331230535504087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 7663487160799169514841045 179612980331230535504087)
          ·
            refine ⟨269419470496845803256131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179612980331230535504087 269419470496845803256131)
            ·
              refine ⟨404129205745268704884197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269419470496845803256131 404129205745268704884197)
              ·
                refine ⟨75774226077237882165787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 404129205745268704884197 75774226077237882165787)
                ·
                  rfl

theorem cell19_249024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 4].length) (baseStart_249024 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_249024 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_249024 prefixEnd_249024 := by exact prefixLift 249024
  have htrace : WordTrace (prefixWord ++ tailWord_249024) baseStart_249024 baseEnd_249024 := by
    simpa [prefixWord, tailWord_249024, baseEnd_249024] using wordTrace_append hprefix tailTrace_249024
  have hstable : (prefixWord ++ tailWord_249024).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249024).length < 2 ^ (prefixWord ++ tailWord_249024).sum := by decide
  have hdescent : baseEnd_249024 < baseStart_249024 := by decide
  rcases family_descends (prefixWord ++ tailWord_249024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249066 : List Nat := [3, 1, 3, 1, 1, 4, 6]
def baseStart_249066 : Nat := 118140960795 + 249066 * 2 ^ 59
def prefixEnd_249066 : Nat := 4983230072969 + 3 ^ 40 * 249066 * 2
def baseEnd_249066 : Nat := 25262335346731409744113

theorem tailTrace_249066 : CollatzResearch.WordTrace tailWord_249066 prefixEnd_249066 25262335346731409744113 := by
  unfold tailWord_249066
  simp only [CollatzResearch.WordTrace]
  refine ⟨2271045828920973482839763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6056122210455929287572701 2271045828920973482839763)
  ·
    refine ⟨3406568743381460224259645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2271045828920973482839763 3406568743381460224259645)
    ·
      refine ⟨1277463278768047584097367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3406568743381460224259645 1277463278768047584097367)
      ·
        refine ⟨1916194918152071376146051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1277463278768047584097367 1916194918152071376146051)
        ·
          refine ⟨2874292377228107064219077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1916194918152071376146051 2874292377228107064219077)
          ·
            refine ⟨538929820730270074541077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2874292377228107064219077 538929820730270074541077)
            ·
              refine ⟨25262335346731409744113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 538929820730270074541077 25262335346731409744113)
              ·
                rfl

theorem cell19_249066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 6].length) (baseStart_249066 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_249066 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_249066 prefixEnd_249066 := by exact prefixLift 249066
  have htrace : WordTrace (prefixWord ++ tailWord_249066) baseStart_249066 baseEnd_249066 := by
    simpa [prefixWord, tailWord_249066, baseEnd_249066] using wordTrace_append hprefix tailTrace_249066
  have hstable : (prefixWord ++ tailWord_249066).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249066).length < 2 ^ (prefixWord ++ tailWord_249066).sum := by decide
  have hdescent : baseEnd_249066 < baseStart_249066 := by decide
  rcases family_descends (prefixWord ++ tailWord_249066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249102 : List Nat := [4, 1, 1, 2, 1, 3, 4, 3]
def baseStart_249102 : Nat := 118140960795 + 249102 * 2 ^ 59
def prefixEnd_249102 : Nat := 4983230072969 + 3 ^ 40 * 249102 * 2
def baseEnd_249102 : Nat := 75797960294156812432241

theorem tailTrace_249102 : CollatzResearch.WordTrace tailWord_249102 prefixEnd_249102 75797960294156812432241 := by
  unfold tailWord_249102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1135687042944184009958695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6056997562368981386446373 1135687042944184009958695)
  ·
    refine ⟨1703530564416276014938043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1135687042944184009958695 1703530564416276014938043)
    ·
      refine ⟨2555295846624414022407065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1703530564416276014938043 2555295846624414022407065)
      ·
        refine ⟨1916471884968310516805299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2555295846624414022407065 1916471884968310516805299)
        ·
          refine ⟨2874707827452465775207949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1916471884968310516805299 2874707827452465775207949)
          ·
            refine ⟨1078015435294674665702981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2874707827452465775207949 1078015435294674665702981)
            ·
              refine ⟨202127894117751499819309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1078015435294674665702981 202127894117751499819309)
              ·
                refine ⟨75797960294156812432241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202127894117751499819309 75797960294156812432241)
                ·
                  rfl

theorem cell19_249102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_249102 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_249102 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_249102 prefixEnd_249102 := by exact prefixLift 249102
  have htrace : WordTrace (prefixWord ++ tailWord_249102) baseStart_249102 baseEnd_249102 := by
    simpa [prefixWord, tailWord_249102, baseEnd_249102] using wordTrace_append hprefix tailTrace_249102
  have hstable : (prefixWord ++ tailWord_249102).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249102).length < 2 ^ (prefixWord ++ tailWord_249102).sum := by decide
  have hdescent : baseEnd_249102 < baseStart_249102 := by decide
  rcases family_descends (prefixWord ++ tailWord_249102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249123 : List Nat := [1, 1, 1, 4, 2, 5, 5]
def baseStart_249123 : Nat := 118140960795 + 249123 * 2 ^ 59
def prefixEnd_249123 : Nat := 4983230072969 + 3 ^ 40 * 249123 * 2
def baseEnd_249123 : Nat := 25268116758544995321839

theorem tailTrace_249123 : CollatzResearch.WordTrace tailWord_249123 prefixEnd_249123 25268116758544995321839 := by
  unfold tailWord_249123
  simp only [CollatzResearch.WordTrace]
  refine ⟨9086262276477392666184023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6057508184318261777456015 9086262276477392666184023)
  ·
    refine ⟨13629393414716088999276035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9086262276477392666184023 13629393414716088999276035)
    ·
      refine ⟨20444090122074133498914053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13629393414716088999276035 20444090122074133498914053)
      ·
        refine ⟨3833266897888900031046385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20444090122074133498914053 3833266897888900031046385)
        ·
          refine ⟨2874950173416675023284789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3833266897888900031046385 2874950173416675023284789)
          ·
            refine ⟨269526578757813283432949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2874950173416675023284789 269526578757813283432949)
            ·
              refine ⟨25268116758544995321839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 269526578757813283432949 25268116758544995321839)
              ·
                rfl

theorem cell19_249123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 5].length) (baseStart_249123 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_249123 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_249123 prefixEnd_249123 := by exact prefixLift 249123
  have htrace : WordTrace (prefixWord ++ tailWord_249123) baseStart_249123 baseEnd_249123 := by
    simpa [prefixWord, tailWord_249123, baseEnd_249123] using wordTrace_append hprefix tailTrace_249123
  have hstable : (prefixWord ++ tailWord_249123).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249123).length < 2 ^ (prefixWord ++ tailWord_249123).sum := by decide
  have hdescent : baseEnd_249123 < baseStart_249123 := by decide
  rcases family_descends (prefixWord ++ tailWord_249123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249140 : List Nat := [2, 5, 1, 1, 1, 1, 4, 4]
def baseStart_249140 : Nat := 118140960795 + 249140 * 2 ^ 59
def prefixEnd_249140 : Nat := 4983230072969 + 3 ^ 40 * 249140 * 2
def baseEnd_249140 : Nat := 75809523117783983587693

theorem tailTrace_249140 : CollatzResearch.WordTrace tailWord_249140 prefixEnd_249140 75809523117783983587693 := by
  unfold tailWord_249140
  simp only [CollatzResearch.WordTrace]
  refine ⟨4543441158707902284776437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6057921544943869713035249 4543441158707902284776437)
  ·
    refine ⟨425947608628865839197791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4543441158707902284776437 425947608628865839197791)
    ·
      refine ⟨638921412943298758796687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 425947608628865839197791 638921412943298758796687)
      ·
        refine ⟨958382119414948138195031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638921412943298758796687 958382119414948138195031)
        ·
          refine ⟨1437573179122422207292547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 958382119414948138195031 1437573179122422207292547)
          ·
            refine ⟨2156359768683633310938821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437573179122422207292547 2156359768683633310938821)
            ·
              refine ⟨404317456628181245801029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2156359768683633310938821 404317456628181245801029)
              ·
                refine ⟨75809523117783983587693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 404317456628181245801029 75809523117783983587693)
                ·
                  rfl

theorem cell19_249140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_249140 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_249140 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_249140 prefixEnd_249140 := by exact prefixLift 249140
  have htrace : WordTrace (prefixWord ++ tailWord_249140) baseStart_249140 baseEnd_249140 := by
    simpa [prefixWord, tailWord_249140, baseEnd_249140] using wordTrace_append hprefix tailTrace_249140
  have hstable : (prefixWord ++ tailWord_249140).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249140).length < 2 ^ (prefixWord ++ tailWord_249140).sum := by decide
  have hdescent : baseEnd_249140 < baseStart_249140 := by decide
  rcases family_descends (prefixWord ++ tailWord_249140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249174 : List Nat := [5, 2, 3, 1, 1, 7]
def baseStart_249174 : Nat := 118140960795 + 249174 * 2 ^ 59
def prefixEnd_249174 : Nat := 4983230072969 + 3 ^ 40 * 249174 * 2
def baseEnd_249174 : Nat := 8424429866897997648005

theorem tailTrace_249174 : CollatzResearch.WordTrace tailWord_249174 prefixEnd_249174 8424429866897997648005 := by
  unfold tailWord_249174
  simp only [CollatzResearch.WordTrace]
  refine ⟨568007649955789273518161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6058748266195085584193717 568007649955789273518161)
  ·
    refine ⟨426005737466841955138621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 568007649955789273518161 426005737466841955138621)
    ·
      refine ⟨159752151550065733176983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426005737466841955138621 159752151550065733176983)
      ·
        refine ⟨239628227325098599765475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159752151550065733176983 239628227325098599765475)
        ·
          refine ⟨359442340987647899648213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239628227325098599765475 359442340987647899648213)
          ·
            refine ⟨8424429866897997648005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 359442340987647899648213 8424429866897997648005)
            ·
              rfl

theorem cell19_249174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 7].length) (baseStart_249174 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_249174 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_249174 prefixEnd_249174 := by exact prefixLift 249174
  have htrace : WordTrace (prefixWord ++ tailWord_249174) baseStart_249174 baseEnd_249174 := by
    simpa [prefixWord, tailWord_249174, baseEnd_249174] using wordTrace_append hprefix tailTrace_249174
  have hstable : (prefixWord ++ tailWord_249174).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249174).length < 2 ^ (prefixWord ++ tailWord_249174).sum := by decide
  have hdescent : baseEnd_249174 < baseStart_249174 := by decide
  rcases family_descends (prefixWord ++ tailWord_249174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249197 : List Nat := [1, 5, 1, 1, 1, 5, 1, 4]
def baseStart_249197 : Nat := 118140960795 + 249197 * 2 ^ 59
def prefixEnd_249197 : Nat := 4983230072969 + 3 ^ 40 * 249197 * 2
def baseEnd_249197 : Nat := 75826867353224740320871

theorem tailTrace_249197 : CollatzResearch.WordTrace tailWord_249197 prefixEnd_249197 75826867353224740320871 := by
  unfold tailWord_249197
  simp only [CollatzResearch.WordTrace]
  refine ⟨9088961278209303304377845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6059307518806202202918563 9088961278209303304377845)
  ·
    refine ⟨852090119832122184785423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9088961278209303304377845 852090119832122184785423)
    ·
      refine ⟨1278135179748183277178135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 852090119832122184785423 1278135179748183277178135)
      ·
        refine ⟨1917202769622274915767203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1278135179748183277178135 1917202769622274915767203)
        ·
          refine ⟨2875804154433412373650805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1917202769622274915767203 2875804154433412373650805)
          ·
            refine ⟨269606639478132410029763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2875804154433412373650805 269606639478132410029763)
            ·
              refine ⟨404409959217198615044645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269606639478132410029763 404409959217198615044645)
              ·
                refine ⟨75826867353224740320871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 404409959217198615044645 75826867353224740320871)
                ·
                  rfl

theorem cell19_249197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 4].length) (baseStart_249197 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_249197 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_249197 prefixEnd_249197 := by exact prefixLift 249197
  have htrace : WordTrace (prefixWord ++ tailWord_249197) baseStart_249197 baseEnd_249197 := by
    simpa [prefixWord, tailWord_249197, baseEnd_249197] using wordTrace_append hprefix tailTrace_249197
  have hstable : (prefixWord ++ tailWord_249197).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249197).length < 2 ^ (prefixWord ++ tailWord_249197).sum := by decide
  have hdescent : baseEnd_249197 < baseStart_249197 := by decide
  rcases family_descends (prefixWord ++ tailWord_249197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249313 : List Nat := [1, 2, 3, 1, 2, 4, 2, 4]
def baseStart_249313 : Nat := 118140960795 + 249313 * 2 ^ 59
def prefixEnd_249313 : Nat := 4983230072969 + 3 ^ 40 * 249313 * 2
def baseEnd_249313 : Nat := 75862164393770841742777

theorem tailTrace_249313 : CollatzResearch.WordTrace tailWord_249313 prefixEnd_249313 75862164393770841742777 := by
  unfold tailWord_249313
  simp only [CollatzResearch.WordTrace]
  refine ⟨9093192145789055115600593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6062128097192703410400395 9093192145789055115600593)
  ·
    refine ⟨6819894109341791336700445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9093192145789055115600593 6819894109341791336700445)
    ·
      refine ⟨2557460291003171751262667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6819894109341791336700445 2557460291003171751262667)
      ·
        refine ⟨3836190436504757626894001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2557460291003171751262667 3836190436504757626894001)
        ·
          refine ⟨2877142827378568220170501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3836190436504757626894001 2877142827378568220170501)
          ·
            refine ⟨539464280133481541281969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2877142827378568220170501 539464280133481541281969)
            ·
              refine ⟨404598210100111155961477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539464280133481541281969 404598210100111155961477)
              ·
                refine ⟨75862164393770841742777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 404598210100111155961477 75862164393770841742777)
                ·
                  rfl

theorem cell19_249313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 4].length) (baseStart_249313 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_249313 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_249313 prefixEnd_249313 := by exact prefixLift 249313
  have htrace : WordTrace (prefixWord ++ tailWord_249313) baseStart_249313 baseEnd_249313 := by
    simpa [prefixWord, tailWord_249313, baseEnd_249313] using wordTrace_append hprefix tailTrace_249313
  have hstable : (prefixWord ++ tailWord_249313).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249313).length < 2 ^ (prefixWord ++ tailWord_249313).sum := by decide
  have hdescent : baseEnd_249313 < baseStart_249313 := by decide
  rcases family_descends (prefixWord ++ tailWord_249313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249364 : List Nat := [2, 4, 3, 1, 3, 1, 1, 4]
def baseStart_249364 : Nat := 118140960795 + 249364 * 2 ^ 59
def prefixEnd_249364 : Nat := 4983230072969 + 3 ^ 40 * 249364 * 2
def baseEnd_249364 : Nat := 75877682920217834609305

theorem tailTrace_249364 : CollatzResearch.WordTrace tailWord_249364 prefixEnd_249364 75877682920217834609305 := by
  unfold tailWord_249364
  simp only [CollatzResearch.WordTrace]
  refine ⟨4547526134302145412853573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6063368179069527217138097 4547526134302145412853573)
  ·
    refine ⟨852661150181652264910045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4547526134302145412853573 852661150181652264910045)
    ·
      refine ⟨319747931318119599341267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 852661150181652264910045 319747931318119599341267)
      ·
        refine ⟨479621896977179399011901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319747931318119599341267 479621896977179399011901)
        ·
          refine ⟨179858211366442274629463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479621896977179399011901 179858211366442274629463)
          ·
            refine ⟨269787317049663411944195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179858211366442274629463 269787317049663411944195)
            ·
              refine ⟨404680975574495117916293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269787317049663411944195 404680975574495117916293)
              ·
                refine ⟨75877682920217834609305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 404680975574495117916293 75877682920217834609305)
                ·
                  rfl

theorem cell19_249364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 4].length) (baseStart_249364 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_249364 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_249364 prefixEnd_249364 := by exact prefixLift 249364
  have htrace : WordTrace (prefixWord ++ tailWord_249364) baseStart_249364 baseEnd_249364 := by
    simpa [prefixWord, tailWord_249364, baseEnd_249364] using wordTrace_append hprefix tailTrace_249364
  have hstable : (prefixWord ++ tailWord_249364).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249364).length < 2 ^ (prefixWord ++ tailWord_249364).sum := by decide
  have hdescent : baseEnd_249364 < baseStart_249364 := by decide
  rcases family_descends (prefixWord ++ tailWord_249364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249368 : List Nat := [2, 1, 2, 3, 4, 2, 1, 4]
def baseStart_249368 : Nat := 118140960795 + 249368 * 2 ^ 59
def prefixEnd_249368 : Nat := 4983230072969 + 3 ^ 40 * 249368 * 2
def baseEnd_249368 : Nat := 75878900059547010520405

theorem tailTrace_249368 : CollatzResearch.WordTrace tailWord_249368 prefixEnd_249368 75878900059547010520405 := by
  unfold tailWord_249368
  simp only [CollatzResearch.WordTrace]
  refine ⟨4547599080294899754426379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6063465440393199672568505 4547599080294899754426379)
  ·
    refine ⟨6821398620442349631639569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4547599080294899754426379 6821398620442349631639569)
    ·
      refine ⟨5116048965331762223729677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6821398620442349631639569 5116048965331762223729677)
      ·
        refine ⟨1918518361999410833898629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5116048965331762223729677 1918518361999410833898629)
        ·
          refine ⟨359722192874889531355993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1918518361999410833898629 359722192874889531355993)
          ·
            refine ⟨269791644656167148516995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359722192874889531355993 269791644656167148516995)
            ·
              refine ⟨404687466984250722775493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269791644656167148516995 404687466984250722775493)
              ·
                refine ⟨75878900059547010520405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 404687466984250722775493 75878900059547010520405)
                ·
                  rfl

theorem cell19_249368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_249368 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_249368 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_249368 prefixEnd_249368 := by exact prefixLift 249368
  have htrace : WordTrace (prefixWord ++ tailWord_249368) baseStart_249368 baseEnd_249368 := by
    simpa [prefixWord, tailWord_249368, baseEnd_249368] using wordTrace_append hprefix tailTrace_249368
  have hstable : (prefixWord ++ tailWord_249368).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249368).length < 2 ^ (prefixWord ++ tailWord_249368).sum := by decide
  have hdescent : baseEnd_249368 < baseStart_249368 := by decide
  rcases family_descends (prefixWord ++ tailWord_249368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249429 : List Nat := [1, 3, 2, 2, 1, 1, 1, 8]
def baseStart_249429 : Nat := 118140960795 + 249429 * 2 ^ 59
def prefixEnd_249429 : Nat := 4983230072969 + 3 ^ 40 * 249429 * 2
def baseEnd_249429 : Nat := 75897461434316943164683

theorem tailTrace_249429 : CollatzResearch.WordTrace tailWord_249429 prefixEnd_249429 75897461434316943164683 := by
  unfold tailWord_249429
  simp only [CollatzResearch.WordTrace]
  refine ⟨9097423013368806926823341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6064948675579204617882227 9097423013368806926823341)
  ·
    refine ⟨3411533630013302597558753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9097423013368806926823341 3411533630013302597558753)
    ·
      refine ⟨2558650222509976948169065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3411533630013302597558753 2558650222509976948169065)
      ·
        refine ⟨1918987666882482711126799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2558650222509976948169065 1918987666882482711126799)
        ·
          refine ⟨2878481500323724066690199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1918987666882482711126799 2878481500323724066690199)
          ·
            refine ⟨4317722250485586100035299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2878481500323724066690199 4317722250485586100035299)
            ·
              refine ⟨6476583375728379150052949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4317722250485586100035299 6476583375728379150052949)
              ·
                refine ⟨75897461434316943164683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6476583375728379150052949 75897461434316943164683)
                ·
                  rfl

theorem cell19_249429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_249429 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_249429 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_249429 prefixEnd_249429 := by exact prefixLift 249429
  have htrace : WordTrace (prefixWord ++ tailWord_249429) baseStart_249429 baseEnd_249429 := by
    simpa [prefixWord, tailWord_249429, baseEnd_249429] using wordTrace_append hprefix tailTrace_249429
  have hstable : (prefixWord ++ tailWord_249429).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249429).length < 2 ^ (prefixWord ++ tailWord_249429).sum := by decide
  have hdescent : baseEnd_249429 < baseStart_249429 := by decide
  rcases family_descends (prefixWord ++ tailWord_249429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249444 : List Nat := [2, 3, 1, 1, 2, 5, 2, 3]
def baseStart_249444 : Nat := 118140960795 + 249444 * 2 ^ 59
def prefixEnd_249444 : Nat := 4983230072969 + 3 ^ 40 * 249444 * 2
def baseEnd_249444 : Nat := 75902025706801352831309

theorem tailTrace_249444 : CollatzResearch.WordTrace tailWord_249444 prefixEnd_249444 75902025706801352831309 := by
  unfold tailWord_249444
  simp only [CollatzResearch.WordTrace]
  refine ⟨4548985054157232244309693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6065313405542976325746257 4548985054157232244309693)
  ·
    refine ⟨1705869395308962091616135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4548985054157232244309693 1705869395308962091616135)
    ·
      refine ⟨2558804092963443137424203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1705869395308962091616135 2558804092963443137424203)
      ·
        refine ⟨3838206139445164706136305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2558804092963443137424203 3838206139445164706136305)
        ·
          refine ⟨2878654604583873529602229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3838206139445164706136305 2878654604583873529602229)
          ·
            refine ⟨269873869179738143400209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2878654604583873529602229 269873869179738143400209)
            ·
              refine ⟨202405401884803607550157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269873869179738143400209 202405401884803607550157)
              ·
                refine ⟨75902025706801352831309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202405401884803607550157 75902025706801352831309)
                ·
                  rfl

theorem cell19_249444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 3].length) (baseStart_249444 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_249444 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_249444 prefixEnd_249444 := by exact prefixLift 249444
  have htrace : WordTrace (prefixWord ++ tailWord_249444) baseStart_249444 baseEnd_249444 := by
    simpa [prefixWord, tailWord_249444, baseEnd_249444] using wordTrace_append hprefix tailTrace_249444
  have hstable : (prefixWord ++ tailWord_249444).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249444).length < 2 ^ (prefixWord ++ tailWord_249444).sum := by decide
  have hdescent : baseEnd_249444 < baseStart_249444 := by decide
  rcases family_descends (prefixWord ++ tailWord_249444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249524 : List Nat := [2, 5, 12]
def baseStart_249524 : Nat := 118140960795 + 249524 * 2 ^ 59
def prefixEnd_249524 : Nat := 4983230072969 + 3 ^ 40 * 249524 * 2
def baseEnd_249524 : Nat := 312454191330801938491

theorem tailTrace_249524 : CollatzResearch.WordTrace tailWord_249524 prefixEnd_249524 312454191330801938491 := by
  unfold tailWord_249524
  simp only [CollatzResearch.WordTrace]
  refine ⟨4550443974012319075765813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6067258632016425434354417 4550443974012319075765813)
  ·
    refine ⟨426604122563654913353045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4550443974012319075765813 426604122563654913353045)
    ·
      refine ⟨312454191330801938491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 12 426604122563654913353045 312454191330801938491)
      ·
        rfl

theorem cell19_249524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 12].length) (baseStart_249524 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_249524 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_249524 prefixEnd_249524 := by exact prefixLift 249524
  have htrace : WordTrace (prefixWord ++ tailWord_249524) baseStart_249524 baseEnd_249524 := by
    simpa [prefixWord, tailWord_249524, baseEnd_249524] using wordTrace_append hprefix tailTrace_249524
  have hstable : (prefixWord ++ tailWord_249524).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249524).length < 2 ^ (prefixWord ++ tailWord_249524).sum := by decide
  have hdescent : baseEnd_249524 < baseStart_249524 := by decide
  rcases family_descends (prefixWord ++ tailWord_249524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249560 : List Nat := [2, 1, 2, 2, 3, 1, 5, 3]
def baseStart_249560 : Nat := 118140960795 + 249560 * 2 ^ 59
def prefixEnd_249560 : Nat := 4983230072969 + 3 ^ 40 * 249560 * 2
def baseEnd_249560 : Nat := 75937322747347454253215

theorem tailTrace_249560 : CollatzResearch.WordTrace tailWord_249560 prefixEnd_249560 75937322747347454253215 := by
  unfold tailWord_249560
  simp only [CollatzResearch.WordTrace]
  refine ⟨4551100487947108149921067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6068133983929477533228089 4551100487947108149921067)
  ·
    refine ⟨6826650731920662224881601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4551100487947108149921067 6826650731920662224881601)
    ·
      refine ⟨5119988048940496668661201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6826650731920662224881601 5119988048940496668661201)
      ·
        refine ⟨3839991036705372501495901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5119988048940496668661201 3839991036705372501495901)
        ·
          refine ⟨1439996638764514688060963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3839991036705372501495901 1439996638764514688060963)
          ·
            refine ⟨2159994958146772032091445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1439996638764514688060963 2159994958146772032091445)
            ·
              refine ⟨202499527326259878008573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2159994958146772032091445 202499527326259878008573)
              ·
                refine ⟨75937322747347454253215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202499527326259878008573 75937322747347454253215)
                ·
                  rfl

theorem cell19_249560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 3].length) (baseStart_249560 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_249560 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_249560 prefixEnd_249560 := by exact prefixLift 249560
  have htrace : WordTrace (prefixWord ++ tailWord_249560) baseStart_249560 baseEnd_249560 := by
    simpa [prefixWord, tailWord_249560, baseEnd_249560] using wordTrace_append hprefix tailTrace_249560
  have hstable : (prefixWord ++ tailWord_249560).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249560).length < 2 ^ (prefixWord ++ tailWord_249560).sum := by decide
  have hdescent : baseEnd_249560 < baseStart_249560 := by decide
  rcases family_descends (prefixWord ++ tailWord_249560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249630 : List Nat := [4, 3, 2, 2, 2, 1, 5]
def baseStart_249630 : Nat := 118140960795 + 249630 * 2 ^ 59
def prefixEnd_249630 : Nat := 4983230072969 + 3 ^ 40 * 249630 * 2
def baseEnd_249630 : Nat := 25319540895202677565823

theorem tailTrace_249630 : CollatzResearch.WordTrace tailWord_249630 prefixEnd_249630 25319540895202677565823 := by
  unfold tailWord_249630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1138094260705077281861293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6069836057093745503260229 1138094260705077281861293)
  ·
    refine ⟨426785347764403980697985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1138094260705077281861293 426785347764403980697985)
    ·
      refine ⟨320089010823302985523489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426785347764403980697985 320089010823302985523489)
      ·
        refine ⟨240066758117477239142617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320089010823302985523489 240066758117477239142617)
        ·
          refine ⟨180050068588107929356963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240066758117477239142617 180050068588107929356963)
          ·
            refine ⟨270075102882161894035445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180050068588107929356963 270075102882161894035445)
            ·
              refine ⟨25319540895202677565823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 270075102882161894035445 25319540895202677565823)
              ·
                rfl

theorem cell19_249630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 5].length) (baseStart_249630 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_249630 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_249630 prefixEnd_249630 := by exact prefixLift 249630
  have htrace : WordTrace (prefixWord ++ tailWord_249630) baseStart_249630 baseEnd_249630 := by
    simpa [prefixWord, tailWord_249630, baseEnd_249630] using wordTrace_append hprefix tailTrace_249630
  have hstable : (prefixWord ++ tailWord_249630).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249630).length < 2 ^ (prefixWord ++ tailWord_249630).sum := by decide
  have hdescent : baseEnd_249630 < baseStart_249630 := by decide
  rcases family_descends (prefixWord ++ tailWord_249630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249636 : List Nat := [2, 3, 1, 3, 2, 3, 5]
def baseStart_249636 : Nat := 118140960795 + 249636 * 2 ^ 59
def prefixEnd_249636 : Nat := 4983230072969 + 3 ^ 40 * 249636 * 2
def baseEnd_249636 : Nat := 25320149464867265521373

theorem tailTrace_249636 : CollatzResearch.WordTrace tailWord_249636 prefixEnd_249636 25320149464867265521373 := by
  unfold tailWord_249636
  simp only [CollatzResearch.WordTrace]
  refine ⟨4552486461809440639804381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6069981949079254186405841 4552486461809440639804381)
  ·
    refine ⟨1707182423178540239926643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4552486461809440639804381 1707182423178540239926643)
    ·
      refine ⟨2560773634767810359889965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1707182423178540239926643 2560773634767810359889965)
      ·
        refine ⟨960290113037928884958737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2560773634767810359889965 960290113037928884958737)
        ·
          refine ⟨720217584778446663719053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 960290113037928884958737 720217584778446663719053)
          ·
            refine ⟨270081594291917498894645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 720217584778446663719053 270081594291917498894645)
            ·
              refine ⟨25320149464867265521373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 270081594291917498894645 25320149464867265521373)
              ·
                rfl

theorem cell19_249636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 5].length) (baseStart_249636 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_249636 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_249636 prefixEnd_249636 := by exact prefixLift 249636
  have htrace : WordTrace (prefixWord ++ tailWord_249636) baseStart_249636 baseEnd_249636 := by
    simpa [prefixWord, tailWord_249636, baseEnd_249636] using wordTrace_append hprefix tailTrace_249636
  have hstable : (prefixWord ++ tailWord_249636).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249636).length < 2 ^ (prefixWord ++ tailWord_249636).sum := by decide
  have hdescent : baseEnd_249636 < baseStart_249636 := by decide
  rcases family_descends (prefixWord ++ tailWord_249636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249710 : List Nat := [4, 1, 2, 3, 1, 3, 1, 4]
def baseStart_249710 : Nat := 118140960795 + 249710 * 2 ^ 59
def prefixEnd_249710 : Nat := 4983230072969 + 3 ^ 40 * 249710 * 2
def baseEnd_249710 : Nat := 75982965472191550919473

theorem tailTrace_249710 : CollatzResearch.WordTrace tailWord_249710 prefixEnd_249710 75982965472191550919473 := by
  unfold tailWord_249710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1138458990668848989725323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6071781283567194611868389 1138458990668848989725323)
  ·
    refine ⟨1707688486003273484587985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1138458990668848989725323 1707688486003273484587985)
    ·
      refine ⟨1280766364502455113440989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1707688486003273484587985 1280766364502455113440989)
      ·
        refine ⟨480287386688420667540371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1280766364502455113440989 480287386688420667540371)
        ·
          refine ⟨720431080032631001310557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480287386688420667540371 720431080032631001310557)
          ·
            refine ⟨270161655012236625491459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 720431080032631001310557 270161655012236625491459)
            ·
              refine ⟨405242482518354938237189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270161655012236625491459 405242482518354938237189)
              ·
                refine ⟨75982965472191550919473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 405242482518354938237189 75982965472191550919473)
                ·
                  rfl

theorem cell19_249710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_249710 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_249710 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_249710 prefixEnd_249710 := by exact prefixLift 249710
  have htrace : WordTrace (prefixWord ++ tailWord_249710) baseStart_249710 baseEnd_249710 := by
    simpa [prefixWord, tailWord_249710, baseEnd_249710] using wordTrace_append hprefix tailTrace_249710
  have hstable : (prefixWord ++ tailWord_249710).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249710).length < 2 ^ (prefixWord ++ tailWord_249710).sum := by decide
  have hdescent : baseEnd_249710 < baseStart_249710 := by decide
  rcases family_descends (prefixWord ++ tailWord_249710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249731 : List Nat := [1, 1, 1, 3, 4, 3, 3, 3]
def baseStart_249731 : Nat := 118140960795 + 249731 * 2 ^ 59
def prefixEnd_249731 : Nat := 4983230072969 + 3 ^ 40 * 249731 * 2
def baseEnd_249731 : Nat := 75989355453669724452749

theorem tailTrace_249731 : CollatzResearch.WordTrace tailWord_249731 prefixEnd_249731 75989355453669724452749 := by
  unfold tailWord_249731
  simp only [CollatzResearch.WordTrace]
  refine ⟨9108437858274712504317047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6072291905516475002878031 9108437858274712504317047)
  ·
    refine ⟨13662656787412068756475571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9108437858274712504317047 13662656787412068756475571)
    ·
      refine ⟨20493985181118103134713357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13662656787412068756475571 20493985181118103134713357)
      ·
        refine ⟨7685244442919288675517509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20493985181118103134713357 7685244442919288675517509)
        ·
          refine ⟨1440983333047366626659533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7685244442919288675517509 1440983333047366626659533)
          ·
            refine ⟨540368749892762484997325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1440983333047366626659533 540368749892762484997325)
            ·
              refine ⟨202638281209785931873997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 540368749892762484997325 202638281209785931873997)
              ·
                refine ⟨75989355453669724452749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202638281209785931873997 75989355453669724452749)
                ·
                  rfl

theorem cell19_249731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 3].length) (baseStart_249731 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_249731 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_249731 prefixEnd_249731 := by exact prefixLift 249731
  have htrace : WordTrace (prefixWord ++ tailWord_249731) baseStart_249731 baseEnd_249731 := by
    simpa [prefixWord, tailWord_249731, baseEnd_249731] using wordTrace_append hprefix tailTrace_249731
  have hstable : (prefixWord ++ tailWord_249731).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249731).length < 2 ^ (prefixWord ++ tailWord_249731).sum := by decide
  have hdescent : baseEnd_249731 < baseStart_249731 := by decide
  rcases family_descends (prefixWord ++ tailWord_249731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249828 : List Nat := [2, 3, 1, 1, 1, 1, 6, 4]
def baseStart_249828 : Nat := 118140960795 + 249828 * 2 ^ 59
def prefixEnd_249828 : Nat := 4983230072969 + 3 ^ 40 * 249828 * 2
def baseEnd_249828 : Nat := 76018871082402240296929

theorem tailTrace_249828 : CollatzResearch.WordTrace tailWord_249828 prefixEnd_249828 76018871082402240296929 := by
  unfold tailWord_249828
  simp only [CollatzResearch.WordTrace]
  refine ⟨4555987869461649035299069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6074650492615532047065425 4555987869461649035299069)
  ·
    refine ⟨1708495451048118388237151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4555987869461649035299069 1708495451048118388237151)
    ·
      refine ⟨2562743176572177582355727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1708495451048118388237151 2562743176572177582355727)
      ·
        refine ⟨3844114764858266373533591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2562743176572177582355727 3844114764858266373533591)
        ·
          refine ⟨5766172147287399560300387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3844114764858266373533591 5766172147287399560300387)
          ·
            refine ⟨8649258220931099340450581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5766172147287399560300387 8649258220931099340450581)
            ·
              refine ⟨405433979106145281583621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8649258220931099340450581 405433979106145281583621)
              ·
                refine ⟨76018871082402240296929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 405433979106145281583621 76018871082402240296929)
                ·
                  rfl

theorem cell19_249828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_249828 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_249828 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_249828 prefixEnd_249828 := by exact prefixLift 249828
  have htrace : WordTrace (prefixWord ++ tailWord_249828) baseStart_249828 baseEnd_249828 := by
    simpa [prefixWord, tailWord_249828, baseEnd_249828] using wordTrace_append hprefix tailTrace_249828
  have hstable : (prefixWord ++ tailWord_249828).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249828).length < 2 ^ (prefixWord ++ tailWord_249828).sum := by decide
  have hdescent : baseEnd_249828 < baseStart_249828 := by decide
  rcases family_descends (prefixWord ++ tailWord_249828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249866 : List Nat := [3, 1, 2, 2, 4, 7]
def baseStart_249866 : Nat := 118140960795 + 249866 * 2 ^ 59
def prefixEnd_249866 : Nat := 4983230072969 + 3 ^ 40 * 249866 * 2
def baseEnd_249866 : Nat := 8447825989558823494709

theorem tailTrace_249866 : CollatzResearch.WordTrace tailWord_249866 prefixEnd_249866 8447825989558823494709 := by
  unfold tailWord_249866
  simp only [CollatzResearch.WordTrace]
  refine ⟨2278340428196407640120363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6075574475190420373654301 2278340428196407640120363)
  ·
    refine ⟨3417510642294611460180545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2278340428196407640120363 3417510642294611460180545)
    ·
      refine ⟨2563132981720958595135409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3417510642294611460180545 2563132981720958595135409)
      ·
        refine ⟨1922349736290718946351557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2563132981720958595135409 1922349736290718946351557)
        ·
          refine ⟨360440575554509802440917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1922349736290718946351557 360440575554509802440917)
          ·
            refine ⟨8447825989558823494709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 360440575554509802440917 8447825989558823494709)
            ·
              rfl

theorem cell19_249866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 7].length) (baseStart_249866 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_249866 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_249866 prefixEnd_249866 := by exact prefixLift 249866
  have htrace : WordTrace (prefixWord ++ tailWord_249866) baseStart_249866 baseEnd_249866 := by
    simpa [prefixWord, tailWord_249866, baseEnd_249866] using wordTrace_append hprefix tailTrace_249866
  have hstable : (prefixWord ++ tailWord_249866).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249866).length < 2 ^ (prefixWord ++ tailWord_249866).sum := by decide
  have hdescent : baseEnd_249866 < baseStart_249866 := by decide
  rcases family_descends (prefixWord ++ tailWord_249866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249980 : List Nat := [2, 2, 2, 1, 1, 6, 5]
def baseStart_249980 : Nat := 118140960795 + 249980 * 2 ^ 59
def prefixEnd_249980 : Nat := 4983230072969 + 3 ^ 40 * 249980 * 2
def baseEnd_249980 : Nat := 25355040792303641639579

theorem tailTrace_249980 : CollatzResearch.WordTrace tailWord_249980 prefixEnd_249980 25355040792303641639579 := by
  unfold tailWord_249980
  simp only [CollatzResearch.WordTrace]
  refine ⟨4558759817186314015065697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6078346422915085353420929 4558759817186314015065697)
  ·
    refine ⟨3419069862889735511299273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4558759817186314015065697 3419069862889735511299273)
    ·
      refine ⟨2564302397167301633474455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3419069862889735511299273 2564302397167301633474455)
      ·
        refine ⟨3846453595750952450211683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2564302397167301633474455 3846453595750952450211683)
        ·
          refine ⟨5769680393626428675317525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3846453595750952450211683 5769680393626428675317525)
          ·
            refine ⟨270453768451238844155509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5769680393626428675317525 270453768451238844155509)
            ·
              refine ⟨25355040792303641639579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 270453768451238844155509 25355040792303641639579)
              ·
                rfl

theorem cell19_249980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 5].length) (baseStart_249980 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_249980 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_249980 prefixEnd_249980 := by exact prefixLift 249980
  have htrace : WordTrace (prefixWord ++ tailWord_249980) baseStart_249980 baseEnd_249980 := by
    simpa [prefixWord, tailWord_249980, baseEnd_249980] using wordTrace_append hprefix tailTrace_249980
  have hstable : (prefixWord ++ tailWord_249980).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249980).length < 2 ^ (prefixWord ++ tailWord_249980).sum := by decide
  have hdescent : baseEnd_249980 < baseStart_249980 := by decide
  rcases family_descends (prefixWord ++ tailWord_249980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250037 : List Nat := [1, 3, 3, 4, 8]
def baseStart_250037 : Nat := 118140960795 + 250037 * 2 ^ 59
def prefixEnd_250037 : Nat := 4983230072969 + 3 ^ 40 * 250037 * 2
def baseEnd_250037 : Nat := 2817869133790803024145

theorem tailTrace_250037 : CollatzResearch.WordTrace tailWord_250037 prefixEnd_250037 2817869133790803024145 := by
  unfold tailWord_250037
  simp only [CollatzResearch.WordTrace]
  refine ⟨9119598595166126764956365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6079732396777417843304243 9119598595166126764956365)
  ·
    refine ⟨3419849473187297536858637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9119598595166126764956365 3419849473187297536858637)
    ·
      refine ⟨1282443552445236576321989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3419849473187297536858637 1282443552445236576321989)
      ·
        refine ⟨240458166083481858060373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1282443552445236576321989 240458166083481858060373)
        ·
          refine ⟨2817869133790803024145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 240458166083481858060373 2817869133790803024145)
          ·
            rfl

theorem cell19_250037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 8].length) (baseStart_250037 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_250037 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_250037 prefixEnd_250037 := by exact prefixLift 250037
  have htrace : WordTrace (prefixWord ++ tailWord_250037) baseStart_250037 baseEnd_250037 := by
    simpa [prefixWord, tailWord_250037, baseEnd_250037] using wordTrace_append hprefix tailTrace_250037
  have hstable : (prefixWord ++ tailWord_250037).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250037).length < 2 ^ (prefixWord ++ tailWord_250037).sum := by decide
  have hdescent : baseEnd_250037 < baseStart_250037 := by decide
  rcases family_descends (prefixWord ++ tailWord_250037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250039 : List Nat := [1, 1, 3, 1, 4, 9]
def baseStart_250039 : Nat := 118140960795 + 250039 * 2 ^ 59
def prefixEnd_250039 : Nat := 4983230072969 + 3 ^ 40 * 250039 * 2
def baseEnd_250039 : Nat := 8453675020224029956385

theorem tailTrace_250039 : CollatzResearch.WordTrace tailWord_250039 prefixEnd_250039 8453675020224029956385 := by
  unfold tailWord_250039
  simp only [CollatzResearch.WordTrace]
  refine ⟨9119671541158881106529171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6079781027439254071019447 9119671541158881106529171)
  ·
    refine ⟨13679507311738321659793757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9119671541158881106529171 13679507311738321659793757)
    ·
      refine ⟨5129815241901870622422659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13679507311738321659793757 5129815241901870622422659)
      ·
        refine ⟨7694722862852805933633989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5129815241901870622422659 7694722862852805933633989)
        ·
          refine ⟨1442760536784901112556373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7694722862852805933633989 1442760536784901112556373)
          ·
            refine ⟨8453675020224029956385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1442760536784901112556373 8453675020224029956385)
            ·
              rfl

theorem cell19_250039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 9].length) (baseStart_250039 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_250039 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_250039 prefixEnd_250039 := by exact prefixLift 250039
  have htrace : WordTrace (prefixWord ++ tailWord_250039) baseStart_250039 baseEnd_250039 := by
    simpa [prefixWord, tailWord_250039, baseEnd_250039] using wordTrace_append hprefix tailTrace_250039
  have hstable : (prefixWord ++ tailWord_250039).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250039).length < 2 ^ (prefixWord ++ tailWord_250039).sum := by decide
  have hdescent : baseEnd_250039 < baseStart_250039 := by decide
  rcases family_descends (prefixWord ++ tailWord_250039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250050 : List Nat := [3, 5, 1, 1, 1, 3, 1, 4]
def baseStart_250050 : Nat := 118140960795 + 250050 * 2 ^ 59
def prefixEnd_250050 : Nat := 4983230072969 + 3 ^ 40 * 250050 * 2
def baseEnd_250050 : Nat := 76086422315171503362991

theorem tailTrace_250050 : CollatzResearch.WordTrace tailWord_250050 prefixEnd_250050 76086422315171503362991 := by
  unfold tailWord_250050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2280018186029757496294901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6080048496079353323453069 2280018186029757496294901)
  ·
    refine ⟨213751704940289765277647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2280018186029757496294901 213751704940289765277647)
    ·
      refine ⟨320627557410434647916471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213751704940289765277647 320627557410434647916471)
      ·
        refine ⟨480941336115651971874707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320627557410434647916471 480941336115651971874707)
        ·
          refine ⟨721412004173477957812061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480941336115651971874707 721412004173477957812061)
          ·
            refine ⟨270529501565054234179523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 721412004173477957812061 270529501565054234179523)
            ·
              refine ⟨405794252347581351269285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270529501565054234179523 405794252347581351269285)
              ·
                refine ⟨76086422315171503362991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 405794252347581351269285 76086422315171503362991)
                ·
                  rfl

theorem cell19_250050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_250050 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_250050 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_250050 prefixEnd_250050 := by exact prefixLift 250050
  have htrace : WordTrace (prefixWord ++ tailWord_250050) baseStart_250050 baseEnd_250050 := by
    simpa [prefixWord, tailWord_250050, baseEnd_250050] using wordTrace_append hprefix tailTrace_250050
  have hstable : (prefixWord ++ tailWord_250050).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250050).length < 2 ^ (prefixWord ++ tailWord_250050).sum := by decide
  have hdescent : baseEnd_250050 < baseStart_250050 := by decide
  rcases family_descends (prefixWord ++ tailWord_250050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
